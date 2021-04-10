//! wip

use crate::ops::AddSym;
use crate::*;
use core::ops::Add;

#[derive(Clone)]
pub enum EExpr<Out, In: ?Sized> {
    Zero,
    One,
    Const(Const<Out>),
    //Variable(DimVariable<DimWrap>),
    Dynamic(Arc<dyn DynamicSymbol<Out, In>>),
}

impl<Out: PartialEq<Out>, In: ?Sized> PartialEq for EExpr<Out, In> {
    fn eq(&self, e: &EExpr<Out, In>) -> bool {
        match (self, e) {
            (EExpr::Zero, EExpr::Zero) => true,
            (EExpr::One, EExpr::One) => true,
            (EExpr::Const(Const(c1)), EExpr::Const(Const(c2))) => c1 == c2,
            (_, _) => false,
        }
    }
}

impl<Out: Display, In: ?Sized> Display for EExpr<Out, In> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            EExpr::Zero => ZeroSym.fmt(fmt),
            EExpr::One => OneSym.fmt(fmt),
            EExpr::Const(c) => c.fmt(fmt),
            //EExpr::Variable(v) => v.fmt(fmt),
            EExpr::Dynamic(d) => d.fmt(fmt),
        }
    }
}

impl<Out: Display, In: ?Sized> DynamicSymbol<Out, In> for EExpr<Out, In>
where
    Self: Any,
    Out: Zero + Clone + One,
{
    fn calc_dyn(&self, i: &In) -> Out {
        match self {
            EExpr::Zero => Out::zero(),
            EExpr::One => Out::one(),
            EExpr::Const(Const(c)) => c.clone(),
            //EExpr::Variable(v) => v.calc_dyn(i),
            EExpr::Dynamic(d) => d.calc_dyn(i),
        }
    }
    fn diff_dyn(&self, d: usize) -> Arc<(dyn DynamicSymbol<Out, In>)> {
        match self {
            EExpr::Zero => ZeroSym.diff_dyn(d),
            EExpr::One => OneSym.diff_dyn(d),
            EExpr::Const(c) => c.diff_dyn(d),
            EExpr::Dynamic(dy) => dy.diff_dyn(d),
        }
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out: Display, In: ?Sized> Symbol<Out, In> for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One,
{
    type Derivative = EExpr<Out, In>;
    fn calc_ref(&self, i: &In) -> Out {
        match self {
            EExpr::Zero => Out::zero(),
            EExpr::One => Out::one(),
            EExpr::Const(Const(c)) => c.clone(),
            EExpr::Dynamic(d) => d.calc_dyn(i),
        }
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        match self {
            EExpr::Zero | EExpr::One | EExpr::Const(_) => EExpr::Zero,
            EExpr::Dynamic(d) => EExpr::Dynamic(d.diff_dyn(dm)),
        }
    }
}

impl<Out, In: ?Sized> Add for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display,
{
    type Output = EExpr<Out, In>;
    fn add(self, e: EExpr<Out, In>) -> EExpr<Out, In> {
        match (self, e) {
            (EExpr::Zero, x) | (x, EExpr::Zero) => x,
            (EExpr::One, EExpr::Const(Const(c))) | (EExpr::Const(Const(c)), EExpr::One) => {
                EExpr::Const(Const(c + Out::one()))
            }
            (EExpr::Const(Const(c1)), EExpr::Const(Const(c2))) => EExpr::Const(Const(c1 + c2)),
            (l, r) => EExpr::Dynamic(Arc::new(AddSym::new(l, r))),
        }
    }
}

impl<Out: Display + Add<Output = Out>, In: ?Sized> Zero for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display,
{
    fn zero() -> Self {
        EExpr::One
    }
    fn is_zero(&self) -> bool {
        match self {
            EExpr::Zero => true,
            EExpr::Const(Const(c)) if c.is_zero() => true,
            _ => false,
        }
    }
}
