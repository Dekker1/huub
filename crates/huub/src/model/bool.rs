use std::{
	fmt::{self, Display},
	num::NonZeroI32,
	ops::Not,
};

use pindakaas::{Lit as RawLit, Var as RawVar};

use crate::{
	model::ReifContext,
	solver::{BoolView, SatSolver},
	SimplifiedBool, Solver, VariableMap,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolExpr {
	Not(Box<BoolExpr>),
	Lit(Literal),
	Val(bool),
}

impl BoolExpr {
	pub(crate) fn to_arg<S: SatSolver>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<S>,
		map: &mut VariableMap,
	) -> SimplifiedBool {
		match self {
			BoolExpr::Not(b) => b.to_negated_arg(ctx, slv, map),
			BoolExpr::Lit(l) => SimplifiedBool::Lit(BoolView(l.0)),
			BoolExpr::Val(v) => SimplifiedBool::Val(*v),
		}
	}

	fn to_negated_arg<S: SatSolver>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<S>,
		map: &mut VariableMap,
	) -> SimplifiedBool {
		match self {
			BoolExpr::Not(v) => v.to_arg(ctx, slv, map),
			BoolExpr::Lit(v) => SimplifiedBool::Lit(BoolView((!v).0)),
			BoolExpr::Val(v) => SimplifiedBool::Val(!v),
		}
	}
}

impl Not for BoolExpr {
	type Output = BoolExpr;
	fn not(self) -> Self::Output {
		match self {
			BoolExpr::Lit(l) => BoolExpr::Lit(!l),
			BoolExpr::Val(v) => BoolExpr::Val(!v),
			BoolExpr::Not(e) => *e,
			//			e => BoolExpr::Not(Box::new(e)),
		}
	}
}

impl Not for &BoolExpr {
	type Output = BoolExpr;
	fn not(self) -> Self::Output {
		match self {
			BoolExpr::Lit(l) => BoolExpr::Lit(!*l),
			BoolExpr::Val(v) => BoolExpr::Val(!*v),
			BoolExpr::Not(e) => (**e).clone(),
			//			e => BoolExpr::Not(Box::new(e.clone())),
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoolVar(pub(crate) RawVar);

impl Not for BoolVar {
	type Output = Literal;
	fn not(self) -> Self::Output {
		!Literal::from(self)
	}
}
impl Not for &BoolVar {
	type Output = Literal;
	fn not(self) -> Self::Output {
		!*self
	}
}

impl Display for BoolVar {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}

impl From<BoolVar> for NonZeroI32 {
	fn from(val: BoolVar) -> Self {
		val.0.into()
	}
}
impl From<BoolVar> for i32 {
	fn from(val: BoolVar) -> Self {
		val.0.into()
	}
}
impl From<BoolVar> for BoolExpr {
	fn from(value: BoolVar) -> Self {
		BoolExpr::Lit(value.into())
	}
}

/// Literal is type that can be use to represent Boolean decision variables and
/// their negations
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal(pub(crate) RawLit);

impl Literal {
	pub fn var(&self) -> BoolVar {
		BoolVar(self.0.var())
	}
	pub fn is_negated(&self) -> bool {
		self.0.is_negated()
	}
}

impl Not for Literal {
	type Output = Literal;
	fn not(self) -> Self::Output {
		Literal(!self.0)
	}
}
impl Not for &Literal {
	type Output = Literal;
	fn not(self) -> Self::Output {
		!(*self)
	}
}

impl From<BoolVar> for Literal {
	fn from(value: BoolVar) -> Self {
		Literal(value.0.into())
	}
}
impl From<Literal> for NonZeroI32 {
	fn from(val: Literal) -> Self {
		val.0.into()
	}
}
impl From<Literal> for i32 {
	fn from(val: Literal) -> Self {
		val.0.into()
	}
}
impl From<Literal> for BoolExpr {
	fn from(value: Literal) -> Self {
		BoolExpr::Lit(value)
	}
}

impl Display for Literal {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}