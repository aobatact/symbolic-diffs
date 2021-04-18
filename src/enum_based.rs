//! wip

use crate::float_ops::*;
use crate::ops::*;
use crate::symbols::*;
use crate::*;
use core::ops::{Add, Div, Mul, Neg, Sub};

pub enum DynExpr<Out, In: ?Sized> {
    Zero,
    One,
    Const(Const<Out>),
    Dynamic(Arc<dyn DynamicSymbol<Out, In>>),
}

impl<Out, In: ?Sized> Clone for DynExpr<Out, In> {
    fn clone(&self) -> Self {
        todo!()
    }
}

unsafe impl<Out: Send + Sync, In: ?Sized + Send + Sync> Send for DynExpr<Out, In> {}
unsafe impl<Out: Send + Sync, In: ?Sized + Send + Sync> Sync for DynExpr<Out, In> {}

impl<Out: PartialEq<Out>, In: ?Sized> PartialEq for DynExpr<Out, In> {
    fn eq(&self, e: &DynExpr<Out, In>) -> bool {
        match (self, e) {
            (DynExpr::Zero, DynExpr::Zero) => true,
            (DynExpr::One, DynExpr::One) => true,
            (DynExpr::Const(Const(c1)), DynExpr::Const(Const(c2))) => c1 == c2,
            (_, _) => false,
        }
    }
}

impl<Out: Display, In: ?Sized> Display for DynExpr<Out, In> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            DynExpr::Zero => ZeroSym.fmt(fmt),
            DynExpr::One => OneSym.fmt(fmt),
            DynExpr::Const(c) => c.fmt(fmt),
            DynExpr::Dynamic(d) => d.fmt(fmt),
        }
    }
}

impl<Out: Display, In: ?Sized> DynamicSymbol<Out, In> for DynExpr<Out, In>
where
    Self: Any,
    Out: Zero + Clone + One,
{
    fn calc_ref(&self, i: &In) -> Out {
        match self {
            DynExpr::Zero => Out::zero(),
            DynExpr::One => Out::one(),
            DynExpr::Const(Const(c)) => c.clone(),
            DynExpr::Dynamic(d) => d.calc_ref(i),
        }
    }
    fn diff_dyn(&self, d: usize) -> Arc<(dyn DynamicSymbol<Out, In>)> {
        match self {
            DynExpr::Zero => ZeroSym.diff_dyn(d),
            DynExpr::One => OneSym.diff_dyn(d),
            DynExpr::Const(c) => c.diff_dyn(d),
            DynExpr::Dynamic(dy) => dy.diff_dyn(d),
        }
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out: Display, In: ?Sized> Symbol<Out, In> for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One,
{
    type Derivative = DynExpr<Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        match self {
            DynExpr::Zero | DynExpr::One | DynExpr::Const(_) => DynExpr::Zero,
            DynExpr::Dynamic(d) => DynExpr::Dynamic(d.diff_dyn(dm)),
        }
    }
    fn to_dyn_expr(self) -> DynExpr<Out, In> {
        self
    }
}

impl<Out, In: ?Sized> Add for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display,
{
    type Output = DynExpr<Out, In>;
    fn add(self, e: DynExpr<Out, In>) -> DynExpr<Out, In> {
        match (self, e) {
            (DynExpr::Zero, x) | (x, DynExpr::Zero) => x,
            (DynExpr::One, DynExpr::Const(Const(c))) | (DynExpr::Const(Const(c)), DynExpr::One) => {
                DynExpr::Const(Const(c + Out::one()))
            }
            (DynExpr::Const(Const(c1)), DynExpr::Const(Const(c2))) => {
                DynExpr::Const(Const(c1 + c2))
            }
            (l, r) => DynExpr::Dynamic(Arc::new(AddSym::new(l, r))),
        }
    }
}

impl<Out: Display + Add<Output = Out>, In: ?Sized> Zero for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display,
{
    fn zero() -> Self {
        DynExpr::One
    }
    fn is_zero(&self) -> bool {
        match self {
            DynExpr::Zero => true,
            DynExpr::Const(Const(c)) if c.is_zero() => true,
            _ => false,
        }
    }
}

impl<Out, In: ?Sized> Sub for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Sub<Output = Out> + Display + Neg<Output = Out>,
{
    type Output = DynExpr<Out, In>;
    fn sub(self, e: DynExpr<Out, In>) -> DynExpr<Out, In> {
        match (self, e) {
            (x, DynExpr::Zero) => x,
            (DynExpr::Zero, x) => -x,
            (DynExpr::Const(Const(c)), DynExpr::One) => DynExpr::Const(Const(c - Out::one())),
            (DynExpr::One, DynExpr::Const(Const(c))) => DynExpr::Const(Const(Out::one() - c)),
            (DynExpr::Const(Const(c1)), DynExpr::Const(Const(c2))) => {
                DynExpr::Const(Const(c1 - c2))
            }
            (l, r) => DynExpr::Dynamic(Arc::new(SubSym::new(l, r))),
        }
    }
}

impl<Out, In: ?Sized> Neg for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Neg<Output = Out> + Display,
{
    type Output = DynExpr<Out, In>;
    fn neg(self) -> DynExpr<Out, In> {
        match self {
            DynExpr::Zero => DynExpr::Zero,
            DynExpr::One => DynExpr::Const(Const(-Out::one())),
            DynExpr::Const(Const(c)) => DynExpr::Const(Const(-c)),
            x => DynExpr::Dynamic(Arc::new(NegSym::new(x))),
        }
    }
}

impl<Out, In: ?Sized> Mul for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display + Mul<Output = Out>,
{
    type Output = DynExpr<Out, In>;
    fn mul(self, e: DynExpr<Out, In>) -> DynExpr<Out, In> {
        match (self, e) {
            (DynExpr::Zero, _) | (_, DynExpr::Zero) => DynExpr::Zero,
            (DynExpr::One, x) | (x, DynExpr::One) => x,
            (DynExpr::Const(Const(c1)), DynExpr::Const(Const(c2))) => {
                DynExpr::Const(Const(c1 * c2))
            }
            (l, r) => DynExpr::Dynamic(Arc::new(MulSym::new(l, r))),
        }
    }
}

impl<Out, In: ?Sized> One for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Add<Output = Out> + Display + Mul<Output = Out>,
{
    fn one() -> Self {
        DynExpr::One
    }
    fn is_one(&self) -> bool {
        match self {
            DynExpr::One => true,
            _ => false,
        }
    }
}

impl<Out, In: ?Sized> Div for DynExpr<Out, In>
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
    type Output = DynExpr<Out, In>;
    fn div(self, e: DynExpr<Out, In>) -> DynExpr<Out, In> {
        match (self, e) {
            (DynExpr::Zero, _) => DynExpr::Zero,
            (x, DynExpr::One) => x,
            (DynExpr::One, DynExpr::Const(Const(c))) => DynExpr::Const(Const(Out::one() / c)),
            (DynExpr::Const(Const(c1)), DynExpr::Const(Const(c2))) => {
                DynExpr::Const(Const(c1 / c2))
            }
            (l, r) => DynExpr::Dynamic(Arc::new(DivSym::new(l, r))),
        }
    }
}

macro_rules! as_dyn_expr {
    (c $($m:ident),* $(,)*) => {
        $(
        fn $m() -> Self {
            DynExpr::Const(Const(Out::$m()))
        })*
    };
    (f $($m:ident),* $(,)*) => {
        $(
        fn $m(self) -> Self {
            DynExpr::Dynamic(Arc::new(<Self as UnaryFloatSymbolEx<Out, In>>::$m(self)))
        }
        )*
    };
}

impl<Out, In> ExNumConsts for DynExpr<Out, In>
where
    Out: ExNumConsts + Any + Clone + Zero + Display,
{
    as_dyn_expr!(c e, ln_10, ln_2, log10_e, log10_2, log2_e, log2_10, two);
}

impl<Out, In> ExNumOps for DynExpr<Out, In>
where
    Out: ExNumOps + Any + Clone + Zero + Display,
    In: Any + std::clone::Clone,
{
    as_dyn_expr!(f exp, ln, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh, recip, exp_m1, exp2, ln_1p, log2, log10,);
}

impl<Out, In> Pow<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: ExNumOps + Any + Clone + Pow<Out, Output = Out>,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn pow(self, r: DynExpr<Out, In>) -> DynExpr<Out, In> {
        BinarySym::new_with_op(PowOp, self, r).to_dyn_expr()
    }
}

/// Operation for pow
impl<Out, In> DynExpr<Out, In>
where
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + Any,
    In: ?Sized + Any,
{
    pub fn pow_t<T>(self, r: T) -> DynExpr<Out, In>
    where
        Out: Pow<T, Output = Out> + Display + Zero + One,
        T: Sub<Output = T> + One + Clone + Any + Default,
    {
        UnarySym::new_with_op(UnaryPowOp(r), self).to_dyn_expr()
    }
}
