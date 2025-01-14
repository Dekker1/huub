use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use crate::{
	brancher::Brancher,
	model::{bool::BoolView, int::IntView, reformulate::VariableMap},
	solver::SatSolver,
	Solver,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VariableSelection {
	AntiFirstFail,
	FirstFail,
	InputOrder,
	Largest,
	Smallest,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueSelection {
	IndomainMax,
	IndomainMin,
	OutdomainMax,
	OutdomainMin,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Branching {
	Bool(Vec<BoolView>, VariableSelection, ValueSelection),
	Int(Vec<IntView>, VariableSelection, ValueSelection),
	Seq(Vec<Branching>),
}

impl Branching {
	pub(crate) fn to_solver<Sol, Sat>(&self, slv: &mut Solver<Sat>, map: &mut VariableMap)
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match self {
			Branching::Bool(vars, var_sel, val_sel) => {
				let vars: Vec<_> = vars.iter().map(|v| map.get_bool(slv, v)).collect();
				slv.add_brancher(Brancher::prepare_bool(vars, *var_sel, *val_sel));
			}
			Branching::Int(v, var_sel, val_sel) => {
				let vars: Vec<_> = v.iter().map(|v| v.to_arg(slv, map)).collect();
				slv.add_brancher(Brancher::prepare_int(vars, *var_sel, *val_sel));
			}
			Branching::Seq(branchings) => {
				for b in branchings {
					b.to_solver(slv, map);
				}
			}
		}
	}
}
