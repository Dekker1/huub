//! Module containing the [`tracing_subscriber::Layer`] implementations that
//! format the events emitted on the `"proof"` target by the `huub` solver
//! into proof files.
//!
//! Two proof formats are supported:
//!
//! - The Deletion Reverse Constraint Propagation (DRCP) format, which describes
//!   the proof in terms of atomic constraints `[x op v]` on the decision
//!   variables. This format is produced by the [`DrcpWriterLayer`].
//! - The VeriPB pseudo-Boolean (`.pbp`) format, which describes the proof in
//!   terms of pseudo-Boolean constraints over the Boolean literals created by
//!   the solver. This format is produced by the [`PbpWriterLayer`].

use std::{
	fmt,
	fs::File,
	io::{self, BufWriter, Write},
	num::NonZeroI32,
	path::PathBuf,
	sync::Mutex,
};

use huub::solver::IntLitMeaning;
use rustc_hash::FxHashSet;
use tracing::{
	Event, Subscriber,
	field::{Field, Visit},
};
use tracing_subscriber::layer::{Context, Layer};

use crate::{
	cli::{CliProofFormat, ProofConfig},
	trace::{LitName, ReverseMaps, parse_int_list},
};

/// A [`tracing_subscriber::Layer`] that writes the events emitted on the
/// `"proof"` target as a proof in the DRCP format.
///
/// The proof steps are streamed directly to the proof file, while the atom
/// definitions are written to a companion literal-definition file (with a
/// `.lits` extension) when the proof is concluded.
pub(crate) struct DrcpWriterLayer {
	/// The path of the companion literal-definition file.
	lits_path: PathBuf,
	/// The reverse mappings used to resolve the names of literals and integer
	/// variables.
	maps: ReverseMaps,
	/// The writer of the proof steps (the proof file itself).
	out: Mutex<BufWriter<File>>,
	/// The identifiers of the literal-definition clauses that are omitted from
	/// the proof, so that they can also be dropped from the propagation hints
	/// of later derived clauses.
	skipped: Mutex<FxHashSet<i64>>,
	/// The set of (positive) literal codes used in the proof steps, for which
	/// atom definitions are written to the companion file.
	used: Mutex<FxHashSet<i32>>,
}

/// A visitor that collects the fields of an event emitted on the `"proof"`
/// target.
#[derive(Debug, Default)]
struct ProofEvent {
	/// The antecedent clause identifiers of a derived clause.
	antecedents: Vec<i64>,
	/// The literals of the clause, represented as non-zero integers.
	clause: Vec<i32>,
	/// The indices of the user constraints from which the clause stems.
	constraints: Vec<u32>,
	/// The name of the solver rule or constraint from which the clause stems.
	hint: String,
	/// The identifier of the clause (as given by the SAT oracle).
	id: i64,
	/// The event message, identifying the kind of proof event.
	message: String,
	/// Whether the objective of the `end_proof` event was minimized.
	minimize: bool,
	/// The index of the integer decision variable that was optimized, if any.
	obj_int_var: Option<u64>,
	/// The objective value reported by the `end_proof` event, present only when
	/// the problem is optimized and a dual bound can be concluded.
	objective: Option<i64>,
	/// The literal that is propagated by the clause, or `0` if the clause does
	/// not stem from a propagation.
	propagated: i32,
	/// The solver status given by the `end_proof` event.
	status: String,
}

/// A [`tracing_subscriber::Layer`] that writes the events emitted on the
/// `"proof"` target as a proof in the requested proof format.
pub(crate) enum ProofLayer {
	/// Write the proof in the DRCP format.
	Drcp(DrcpWriterLayer),
	/// Write the proof in the VeriPB pseudo-Boolean format.
	Veripb(VeripbWriterLayer),
}

/// A [`tracing_subscriber::Layer`] that writes the events emitted on the
/// `"proof"` target as a proof in the VeriPB pseudo-Boolean format.
pub(crate) struct VeripbWriterLayer {
	/// The writer to which the proof is written.
	out: Mutex<BufWriter<File>>,
}

/// Write the DRCP atomic constraint of the given [`LitName`].
///
/// Note that the DRCP format does not have a strict inequality, the
/// [`IntLitMeaning::Less`] meaning is represented using `<=`.
fn write_atom<W: Write>(out: &mut W, name: &LitName) -> io::Result<()> {
	match name {
		LitName::BoolVar(var, pos) => {
			write!(out, "[{} == {}]", var.name, if *pos { 1 } else { 0 })
		}
		LitName::IntLit(var, meaning) => match meaning {
			IntLitMeaning::Eq(val) => write!(out, "[{} == {val}]", var.name),
			IntLitMeaning::NotEq(val) => write!(out, "[{} != {val}]", var.name),
			IntLitMeaning::GreaterEq(val) => write!(out, "[{} >= {val}]", var.name),
			IntLitMeaning::Less(val) => write!(out, "[{} <= {}]", var.name, val - 1),
		},
	}
}

impl DrcpWriterLayer {
	/// Record the use of the given literals in the proof, and return their
	/// (signed) atom codes.
	fn atom_codes(&self, lits: impl IntoIterator<Item = i32>) -> Vec<i32> {
		let mut used = self.used.lock().unwrap();
		lits.into_iter()
			.inspect(|lit| {
				let _ = used.insert(lit.abs());
			})
			.collect()
	}

	/// Conclude the proof: write the atom definitions for all used literal
	/// codes to the companion literal-definition file, and the conclusion
	/// derived from the `end_proof` event to the proof file.
	fn conclude(&self, event: &ProofEvent) -> io::Result<()> {
		let mut codes: Vec<i32> = self.used.lock().unwrap().iter().copied().collect();
		codes.sort_unstable();

		// Write the atom definitions for all used literal codes to the companion
		// literal-definition file.
		let mut lits = BufWriter::new(File::create(&self.lits_path)?);
		{
			let lit_map = self.maps.lit.lock().unwrap();
			for code in &codes {
				write!(lits, "a {code} ")?;
				match lit_map.get(&NonZeroI32::new(*code).unwrap()) {
					Some(name) => write_atom(&mut lits, name)?,
					// The literal has no known meaning (e.g. it is an auxiliary literal
					// introduced by an encoding). Use a synthesized name based on the
					// literal code.
					None => write!(lits, "[_b{code} == 1]")?,
				}
				writeln!(lits)?;
			}
		}

		// Write the conclusion of the proof to the proof file.
		let mut out = self.out.lock().unwrap();
		match event.status.as_str() {
			"Unsatisfiable" => writeln!(out, "c UNSAT")?,
			"Complete" => {
				// Conclude with the proven dual bound on the objective when the
				// problem is optimized and the objective maps to a known integer
				// decision.
				let name = event.obj_int_var.and_then(|idx| {
					let int_map = self.maps.int.lock().unwrap();
					int_map
						.get(idx as usize)
						.cloned()
						.flatten()
						.map(|v| v.name.clone())
				});
				if let (Some(objective), Some(name)) = (event.objective, name) {
					let op = if event.minimize { ">=" } else { "<=" };
					// Synthesize a fresh positive atom code for the bound (the
					// codes of the SAT literals are used for the other atoms, but
					// no SAT literal is known to represent the bound). It is
					// defined in the companion file alongside the other atoms.
					let code = codes.last().copied().unwrap_or(0).saturating_add(1);
					writeln!(lits, "a {code} [{name} {op} {objective}]")?;
					writeln!(out, "c {code}")?;
				}
			}
			_ => {}
		}
		lits.flush()?;
		out.flush()
	}

	/// Create a new [`DrcpWriterLayer`] that produces a proof file at `path`
	/// and a companion literal-definition file alongside it, using the given
	/// reverse mappings to resolve the meanings of literals.
	fn new(path: PathBuf, maps: ReverseMaps) -> io::Result<Self> {
		let out = BufWriter::new(File::create(&path)?);
		Ok(Self {
			lits_path: path.with_extension("lits"),
			maps,
			out: Mutex::new(out),
			skipped: Mutex::default(),
			used: Mutex::default(),
		})
	}

	/// Process a proof event, writing the corresponding DRCP step.
	fn process(&self, event: &ProofEvent) -> io::Result<()> {
		match event.message.as_str() {
			"add_original_clause" => {
				// Ignore literal-definition clauses
				if event.hint == "lit_def" {
					let _ = self.skipped.lock().unwrap().insert(event.id);
					return Ok(());
				}
				// A clause `(l1 ∨ ... ∨ ln)` stemming from the solver is
				// represented as an inference step: the negations of the
				// non-propagated literals form the premises, and the propagated
				// literal (if any) forms the consequent.
				let premises = self.atom_codes(
					event
						.clause
						.iter()
						.filter(|&&l| l != event.propagated)
						.map(|&l| -l),
				);
				let mut out = self.out.lock().unwrap();
				write!(out, "i {}", event.id)?;
				for code in premises {
					write!(out, " {code}")?;
				}
				write!(out, " 0")?;
				if event.propagated != 0 {
					let consequent = self.atom_codes([event.propagated])[0];
					write!(out, " {consequent}")?;
				}
				if let Some(&con) = event.constraints.first() {
					// Note that the DRCP format uses non-zero constraint
					// identifiers, while the constraint indices are zero-based.
					write!(out, " c:{}", con + 1)?;
				}
				if !event.hint.is_empty() {
					write!(out, " l:{}", event.hint)?;
				}
				writeln!(out)
			}
			"add_derived_clause" | "add_assumption_clause" => {
				// A clause `(l1 ∨ ... ∨ ln)` derived by the SAT oracle is
				// represented as a nogood (deduction) step refuting the
				// conjunction of the negations of its literals.
				let premises = self.atom_codes(event.clause.iter().map(|&l| -l));
				let skipped = self.skipped.lock().unwrap();
				let mut out = self.out.lock().unwrap();
				write!(out, "n {}", event.id)?;
				for code in premises {
					write!(out, " {code}")?;
				}
				write!(out, " 0")?;
				for ant in event
					.antecedents
					.iter()
					.filter(|ant| !skipped.contains(ant))
				{
					write!(out, " {ant}")?;
				}
				writeln!(out)
			}
			"end_proof" => self.conclude(event),
			// The DRCP format does not represent clause deletions, assumption
			// tracking, or solver status reports.
			_ => Ok(()),
		}
	}
}

impl Visit for ProofEvent {
	fn record_bool(&mut self, field: &Field, value: bool) {
		if field.name() == "minimize" {
			self.minimize = value;
		}
	}

	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		match field.name() {
			"message" => self.message = format!("{value:?}"),
			"clause" => self.clause = parse_int_list(value).unwrap_or_default(),
			"antecedents" => self.antecedents = parse_int_list(value).unwrap_or_default(),
			"constraints" => self.constraints = parse_int_list(value).unwrap_or_default(),
			"status" => self.status = format!("{value:?}"),
			_ => {}
		}
	}

	fn record_i64(&mut self, field: &Field, value: i64) {
		match field.name() {
			"id" => self.id = value,
			"propagated" => self.propagated = value as i32,
			"objective" => self.objective = Some(value),
			_ => {}
		}
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		match field.name() {
			"hint" => self.hint = value.to_owned(),
			"status" => self.status = value.to_owned(),
			_ => {}
		}
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		match field.name() {
			"obj_int_var" => self.obj_int_var = Some(value),
			_ => self.record_i64(field, value as i64),
		}
	}
}

impl ProofLayer {
	/// Create a new [`ProofLayer`] according to the given [`ProofConfig`],
	/// using the given reverse mappings to resolve the meanings of literals.
	pub(crate) fn new(config: &ProofConfig, maps: ReverseMaps) -> io::Result<Self> {
		Ok(match config.format {
			CliProofFormat::Drcp => {
				ProofLayer::Drcp(DrcpWriterLayer::new(config.path.clone(), maps)?)
			}
			CliProofFormat::Veripb => {
				ProofLayer::Veripb(VeripbWriterLayer::new(config.path.clone())?)
			}
		})
	}
}

impl<S: Subscriber> Layer<S> for ProofLayer {
	fn on_event(&self, event: &Event<'_>, _: Context<'_, S>) {
		let mut fields = ProofEvent::default();
		event.record(&mut fields);
		let res = match self {
			ProofLayer::Drcp(layer) => layer.process(&fields),
			ProofLayer::Veripb(layer) => layer.process(&fields),
		};
		if let Err(err) = res {
			// Note that panicking within the tracing subscriber would poison
			// the solving process; the proof is invalid regardless.
			eprintln!("ERROR: unable to write proof file: {err}");
		}
	}
}

impl VeripbWriterLayer {
	/// Create a new [`PbpWriterLayer`] that produces a proof file at `path`,
	/// writing the header of the proof file.
	fn new(path: PathBuf) -> io::Result<Self> {
		let layer = Self {
			out: Mutex::new(BufWriter::new(File::create(&path)?)),
		};
		{
			let mut out = layer.out.lock().unwrap();
			writeln!(out, "pseudo-Boolean proof version 3.0")?;
			writeln!(out, "f 0 ;")?;
		}
		Ok(layer)
	}

	/// Process a proof event, writing the corresponding VeriPB proof line.
	fn process(&self, event: &ProofEvent) -> io::Result<()> {
		let mut out = self.out.lock().unwrap();
		match event.message.as_str() {
			"add_original_clause" => {
				write!(out, "@c{} a ", event.id)?;
				for &l in &event.clause {
					if l >= 0 {
						write!(out, "1 x{l} ")?;
					} else {
						write!(out, "1 ~x{} ", -l)?;
					}
				}
				write!(out, ">= 1")?;
				// Annotate the clause with its solver rule or constraint when
				// known.
				if !event.hint.is_empty() {
					write!(out, " :: {}", event.hint)?;
					if !event.constraints.is_empty() {
						write!(out, "{:?}", event.constraints)?;
					}
				}
				writeln!(out, ";")
			}
			"add_derived_clause" | "add_assumption_clause" => {
				// Derived clauses are justified by a reverse unit propagation
				// resolution chain over their antecedents.
				write!(out, "@c{} pol ", event.id)?;
				for (i, ant) in event.antecedents.iter().rev().enumerate() {
					if i == 0 {
						write!(out, "@c{ant} ")?;
					} else {
						write!(out, "@c{ant} + s ")?;
					}
				}
				writeln!(out, ";")
			}
			"delete_clause" => {
				writeln!(out, "del id @c{} ;", event.id)
			}
			"solve_query" | "add_assumption" | "reset_assumptions" | "conclude_sat"
			| "conclude_unknown" | "conclude_unsat" | "begin_proof" => {
				// Events related to incremental solving have no VeriPB
				// representation; they are included as comments.
				writeln!(out, "% {}", event.message)
			}
			"end_proof" => {
				writeln!(out, "output NONE ;")?;
				if event.status == "Unsatisfiable" {
					writeln!(out, "conclusion UNSAT ;")?;
				} else {
					writeln!(out, "conclusion NONE ;")?;
				}
				writeln!(out, "end pseudo-Boolean proof ;")?;
				out.flush()
			}
			_ => Ok(()),
		}
	}
}

#[cfg(test)]
mod tests {
	use std::{
		fs,
		num::NonZeroI32,
		sync::{Arc, Mutex},
	};

	use drcp_format::{Conclusion, IntComparison, Step, reader::ProofReader};
	use expect_test::expect;
	use flatzinc_serde::{Type, Variable};
	use huub::solver::IntLitMeaning;
	use rustc_hash::FxHashMap;
	use tracing::subscriber::with_default;
	use tracing_subscriber::layer::SubscriberExt;

	use crate::{
		cli::{CliProofFormat, ProofConfig},
		proof::ProofLayer,
		trace::{LitName, ReverseMaps, VarRef},
	};

	/// Create the literal reverse mapping used by the formatter tests.
	///
	/// The mapping describes the following literals:
	/// - `1`: `x == 2` (and `-1`: `x != 2`)
	/// - `2`: `y >= 3` (and `-2`: `y < 3`)
	fn lit_reverse_map() -> Arc<Mutex<FxHashMap<NonZeroI32, LitName>>> {
		let x = var("x");
		let y = var("y");
		let mut map = FxHashMap::default();
		let _ = map.insert(
			NonZeroI32::new(1).unwrap(),
			LitName::IntLit(Arc::clone(&x), IntLitMeaning::Eq(2)),
		);
		let _ = map.insert(
			NonZeroI32::new(-1).unwrap(),
			LitName::IntLit(x, IntLitMeaning::NotEq(2)),
		);
		let _ = map.insert(
			NonZeroI32::new(2).unwrap(),
			LitName::IntLit(Arc::clone(&y), IntLitMeaning::GreaterEq(3)),
		);
		let _ = map.insert(
			NonZeroI32::new(-2).unwrap(),
			LitName::IntLit(y, IntLitMeaning::Less(3)),
		);
		Arc::new(Mutex::new(map))
	}

	/// Emit a synthetic proof for the given format and return the produced
	/// proof file together with the companion literal-definition file (empty
	/// for formats that do not produce one).
	fn run_events(format: CliProofFormat) -> (String, String) {
		let dir = std::env::temp_dir().join(format!("huub-proof-test-{:?}", format));
		let _ = fs::create_dir_all(&dir);
		let path = dir.join(match format {
			CliProofFormat::Drcp => "test.drcp",
			CliProofFormat::Veripb => "test.pbp",
		});
		let config = ProofConfig {
			format,
			path: path.clone(),
		};
		let maps = ReverseMaps {
			lit: lit_reverse_map(),
			int: Arc::default(),
		};
		let layer = ProofLayer::new(&config, maps).unwrap();
		let subscriber = tracing_subscriber::registry().with(layer);
		with_default(subscriber, || {
			// An original clause from a constraint that propagates `x = 2`.
			tracing::trace!(
				target: "proof",
				id = 1_i64,
				redundant = false,
				restored = false,
				clause = ?vec![1_i32, -2_i32],
				propagated = 1_i32,
				hint = "int_lin_eq",
				constraints = ?vec![3_u32],
				"add_original_clause"
			);
			// A literal definition clause without a propagation or constraint.
			tracing::trace!(
				target: "proof",
				id = 2_i64,
				redundant = false,
				restored = false,
				clause = ?vec![-1_i32, 2_i32],
				propagated = 0_i32,
				hint = "lit_def",
				constraints = ?Vec::<u32>::new(),
				"add_original_clause"
			);
			// A derived (learned) clause.
			tracing::trace!(
				target: "proof",
				id = 3_i64,
				redundant = true,
				clause = ?vec![-1_i32],
				antecedents = ?vec![1_i64, 2_i64],
				"add_derived_clause"
			);
			tracing::trace!(
				target: "proof",
				status = "Unsatisfiable",
				"end_proof"
			);
		});
		let proof = fs::read_to_string(&path).unwrap();
		let lits = match format {
			CliProofFormat::Drcp => fs::read_to_string(path.with_extension("lits")).unwrap(),
			CliProofFormat::Veripb => String::new(),
		};
		(proof, lits)
	}

	#[test]
	fn test_drcp_formatter() {
		let (proof, lits) = run_events(CliProofFormat::Drcp);
		// The proof file contains only the steps and the conclusion.
		expect![[r#"
    i 1 2 0 1 c:4 l:int_lin_eq
    n 3 1 0 1
    c UNSAT
"#]]
		.assert_eq(&proof);
		// The companion file defines the atoms used in the proof.
		expect![[r#"
    a 1 [x == 2]
    a 2 [y >= 3]
"#]]
		.assert_eq(&lits);

		// The companion definitions followed by the proof should be parseable by
		// the `drcp-format` reader, which reads atom definitions before steps.
		let proof = format!("{lits}{proof}");
		let mut reader = ProofReader::<_, i32>::new(proof.as_bytes());
		let mut steps = Vec::new();
		while let Some(step) = reader.next_step().expect("valid DRCP proof") {
			steps.push(step);
		}
		// One inference, one nogood, and one conclusion.
		assert_eq!(steps.len(), 3);
		assert!(matches!(steps[0], Step::Inference(_)));
		assert!(matches!(steps[1], Step::Deduction(_)));
		assert_eq!(steps[2], Step::Conclusion(Conclusion::Unsat));

		// The first inference propagates `[x == 2]` from `[y >= 3]`.
		let Step::Inference(inf) = &steps[0] else {
			unreachable!()
		};
		assert_eq!(inf.premises.len(), 1);
		assert_eq!(inf.premises[0].comparison, IntComparison::GreaterEqual);
		let consequent = inf.consequent.as_ref().unwrap();
		assert_eq!(consequent.comparison, IntComparison::Equal);
		assert_eq!(inf.generated_by, std::num::NonZero::new(4_u32));
		assert_eq!(inf.label.as_deref(), Some("int_lin_eq"));
	}

	#[test]
	fn test_drcp_objective_bound() {
		// A completed optimization proof concludes with the proven dual bound on
		// the objective, naming the integer decision it is optimized over.
		let dir = std::env::temp_dir().join("huub-proof-test-obj-bound");
		let _ = fs::create_dir_all(&dir);
		let path = dir.join("test.drcp");
		let config = ProofConfig {
			format: CliProofFormat::Drcp,
			path: path.clone(),
		};
		// Map integer decision `0` to a variable named `obj`.
		let maps = ReverseMaps {
			lit: lit_reverse_map(),
			int: Arc::new(Mutex::new(vec![Some(var("obj"))])),
		};
		let layer = ProofLayer::new(&config, maps).unwrap();
		let subscriber = tracing_subscriber::registry().with(layer);
		with_default(subscriber, || {
			tracing::trace!(
				target: "proof",
				id = 1_i64,
				redundant = false,
				restored = false,
				clause = ?vec![1_i32],
				propagated = 0_i32,
				hint = "int_lin_le",
				constraints = ?Vec::<u32>::new(),
				"add_original_clause"
			);
			// A minimization that is proven complete with objective value `7`.
			tracing::trace!(
				target: "proof",
				status = "Complete",
				objective = 7_i64,
				obj_int_var = 0_u64,
				minimize = true,
				"end_proof"
			);
		});
		let proof = fs::read_to_string(&path).unwrap();
		// The dual bound is concluded in the proof file, and its atom (like the
		// others) is defined in the companion file.
		expect![[r#"
    i 1 -1 0 l:int_lin_le
    c 2
"#]]
		.assert_eq(&proof);
		let lits = fs::read_to_string(path.with_extension("lits")).unwrap();
		expect![[r#"
    a 1 [x == 2]
    a 2 [obj >= 7]
"#]]
		.assert_eq(&lits);
	}

	#[test]
	fn test_pbp_formatter() {
		let (proof, _lits) = run_events(CliProofFormat::Veripb);
		expect![[r#"
    pseudo-Boolean proof version 3.0
    f 0 ;
    @c1 a 1 x1 1 ~x2 >= 1 :: int_lin_eq[3];
    @c2 a 1 ~x1 1 x2 >= 1 :: lit_def;
    @c3 pol @c2 @c1 + s ;
    output NONE ;
    conclusion UNSAT ;
    end pseudo-Boolean proof ;
"#]]
		.assert_eq(&proof);
	}

	/// Create a [`VarRef`] for a variable with the given name.
	fn var(name: &str) -> VarRef {
		Arc::new(Variable {
			name: name.to_owned(),
			ty: Type::Bool,
			ann: Vec::new(),
			defined: false,
			introduced: false,
		})
	}
}
