//! wip

use crate::ops::{AddSym, DivSym, MulSym, NegSym, SubSym};
use crate::*;
use core::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone)]
pub enum EExpr<Out, In: ?Sized> {
    Zero,
    One,
    Const(Const<Out>),
    Dynamic(Arc<dyn DynamicSymbol<Out, In>>),
}

impl<Out, In: ?Sized> EExpr<Out, In> {
    pub fn try_downcast<T>(&self) -> Option<&T>
    where
        T: Any,
    {
        if let EExpr::Dynamic(ref d) = self {
            d.as_ref().as_any().downcast_ref::<T>()
        } else {
            None
        }
    }
}

unsafe impl<Out: Send + Sync, In: ?Sized + Send + Sync> Send for EExpr<Out, In> {}
unsafe impl<Out: Send + Sync, In: ?Sized + Send + Sync> Sync for EExpr<Out, In> {}

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
            EExpr::Dynamic(d) => d.fmt(fmt),
        }
    }
}

impl<Out: Display, In: ?Sized> DynamicSymbol<Out, In> for EExpr<Out, In>
where
    Self: Any,
    Out: Zero + Clone + One,
{
    fn calc_ref(&self, i: &In) -> Out {
        match self {
            EExpr::Zero => Out::zero(),
            EExpr::One => Out::one(),
            EExpr::Const(Const(c)) => c.clone(),
            EExpr::Dynamic(d) => d.calc_ref(i),
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

impl<Out, In: ?Sized> Sub for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Sub<Output = Out> + Display + Neg<Output = Out>,
{
    type Output = EExpr<Out, In>;
    fn sub(self, e: EExpr<Out, In>) -> EExpr<Out, In> {
        match (self, e) {
            (x, EExpr::Zero) => x,
            (EExpr::Zero, x) => -x,
            (EExpr::Const(Const(c)), EExpr::One) => EExpr::Const(Const(c - Out::one())),
            (EExpr::One, EExpr::Const(Const(c))) => EExpr::Const(Const(Out::one() - c)),
            (EExpr::Const(Const(c1)), EExpr::Const(Const(c2))) => EExpr::Const(Const(c1 - c2)),
            (l, r) => EExpr::Dynamic(Arc::new(SubSym::new(l, r))),
        }
    }
}

impl<Out, In: ?Sized> Neg for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Neg<Output = Out> + Display,
{
    type Output = EExpr<Out, In>;
    fn neg(self) -> EExpr<Out, In> {
        match self {
            EExpr::Zero => EExpr::Zero,
            EExpr::One => EExpr::Const(Const(-Out::one())),
            EExpr::Const(Const(c)) => EExpr::Const(Const(-c)),
            x => EExpr::Dynamic(Arc::new(NegSym::new(x))),
        }
    }
}

impl<Out, In: ?Sized> Mul for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display + Mul<Output = Out>,
{
    type Output = EExpr<Out, In>;
    fn mul(self, e: EExpr<Out, In>) -> EExpr<Out, In> {
        match (self, e) {
            (EExpr::Zero, _) | (_, EExpr::Zero) => EExpr::Zero,
            (EExpr::One, x) | (x, EExpr::One) => x,
            (EExpr::Const(Const(c1)), EExpr::Const(Const(c2))) => EExpr::Const(Const(c1 * c2)),
            (l, r) => EExpr::Dynamic(Arc::new(MulSym::new(l, r))),
        }
    }
}

impl<Out, In: ?Sized> One for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display + Mul<Output = Out>,
{
    fn one() -> Self {
        EExpr::One
    }
    fn is_one(&self) -> bool {
        match self {
            EExpr::One => true,
            _ => false,
        }
    }
}

impl<Out, In: ?Sized> Div for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero
        + Clone
        + One
        + Sub<Output = Out>
        + Display
        + Neg<Output = Out>
        + Add<Output = Out>
        + Mul<Output = Out>
        + Div<Output = Out>,
{
    type Output = EExpr<Out, In>;
    fn div(self, e: EExpr<Out, In>) -> EExpr<Out, In> {
        match (self, e) {
            (EExpr::Zero, _) => EExpr::Zero,
            (x, EExpr::One) => x,
            (EExpr::One, EExpr::Const(Const(c))) => EExpr::Const(Const(Out::one() / c)),
            (EExpr::Const(Const(c1)), EExpr::Const(Const(c2))) => EExpr::Const(Const(c1 / c2)),
            (l, r) => EExpr::Dynamic(Arc::new(DivSym::new(l, r))),
        }
    }
}

/*
impl<Out, In: ?Sized> Pow<EExpr<Out, In>> for EExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero
        + Clone
        + One
        + Sub<Output = Out>
        + Display
        + Neg<Output = Out>
        + Add<Output = Out>
        + Mul<Output = Out>
        + Div<Output = Out>
        + Pow<Out, Output = Out>,
{
    type Output = EExpr<Out, In>;
    fn pow(self, r : EExpr<Out, In>) -> EExpr<Out, In> {
        match (self, r) {
            (_, EExpr::Zero) => EExpr::One,
            (EExpr::Zero, _) => EExpr::Zero,
        }
    }
}
*/
