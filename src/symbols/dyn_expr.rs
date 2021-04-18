//! wip

use crate::float_ops::*;
use crate::ops::*;
use crate::symbols::*;
use core::ops::{Add, Div, Mul, Neg, Sub};

pub enum DynExpr<Out, In: ?Sized> {
    Zero,
    One,
    Const(Const<Out>),
    Dynamic(Arc<dyn DynamicSymbol<Out, In>>),
}

impl<Out: Clone, In: ?Sized> Clone for DynExpr<Out, In> {
    fn clone(&self) -> Self {
        match self {
            DynExpr::Zero => DynExpr::Zero,
            DynExpr::One => DynExpr::One,
            DynExpr::Const(c) => DynExpr::Const(c.clone()),
            DynExpr::Dynamic(d) => DynExpr::Dynamic(d.clone()),
        }
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
            (DynExpr::Dynamic(d1), DynExpr::Dynamic(d2)) => Arc::ptr_eq(d1, d2),
            _ => false,
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

impl<Out, In: ?Sized> Default for DynExpr<Out, In> {
    fn default() -> Self {
        DynExpr::Zero
    }
}

impl<Out, In: ?Sized> DynamicSymbol<Out, In> for DynExpr<Out, In>
where
    Self: Any,
    Out: Zero + Clone + One + Display,
{
    fn calc_ref(&self, i: &In) -> Out {
        match self {
            DynExpr::Zero => Out::zero(),
            DynExpr::One => Out::one(),
            DynExpr::Const(Const(c)) => c.clone(),
            DynExpr::Dynamic(d) => d.calc_ref(i),
        }
    }
    fn diff_dyn(&self, d: usize) -> DynExpr<Out, In> {
        match self {
            DynExpr::Zero => DynExpr::Zero,
            DynExpr::One => DynExpr::Zero,
            DynExpr::Const(_) => DynExpr::Zero,
            DynExpr::Dynamic(dy) => dy.diff_dyn(d),
        }
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In: ?Sized> Symbol<Out, In> for DynExpr<Out, In>
where
    Self: Any + Clone,
    Out: Zero + Clone + One + Display,
{
    type Derivative = DynExpr<Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        match self {
            DynExpr::Zero | DynExpr::One | DynExpr::Const(_) => DynExpr::Zero,
            DynExpr::Dynamic(d) => d.diff_dyn(dm).to_dyn_expr(),
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
            (l, r) => DivSym::new(l, r).to_dyn_expr(),
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
    Out: ExNumOps
        + Add<Output = Out>
        + Mul<Output = Out>
        + Pow<Out, Output = Out>
        + Clone
        + Any
        + Zero
        + One
        + Default,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn pow(self, r: DynExpr<Out, In>) -> DynExpr<Out, In> {
        match (self, r) {
            (_, DynExpr::Zero) => DynExpr::One,
            (DynExpr::Zero, _) => DynExpr::Zero,
            (DynExpr::One, _) => DynExpr::One,
            (x, DynExpr::One) => x,
            (DynExpr::Const(Const(c1)), DynExpr::Const(Const(c2))) => {
                DynExpr::Const(Const(c1.pow(c2)))
            }
            (x, DynExpr::Const(Const(c2))) => {
                UnarySym::new_with_op(UnaryPowOp(c2), x).to_dyn_expr()
            }
            (l, r) => BinarySym::new_with_op(PowOp, l, r).to_dyn_expr(),
        }
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

#[cfg(test)]
mod tests {
    use crate::ops::*;
    use crate::*;
    use std::sync::Arc;
    #[cfg(feature = "typenum")]
    use typenum::*;

    #[test]
    fn variable() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(1, x.calc_ref(&1));
        let y = x + x;
        assert_eq!(2, y.calc_ref(&1));
        let z = y.diff_dyn(0);
        assert_eq!(2, z.calc_ref(&2));

        let x: Expr<Variable, f32> = Variable.into();
        let w = Arc::new(x);
        assert_eq!(1., x.calc_ref(&1.));
        let w = w.to_dyn_expr().to_expr();
        assert_eq!(1., x.calc_ref(&1.));
        let y = w.clone() + w.clone();
        assert_eq!(2., y.calc_ref(&1.));
        let y = w.clone() + x;
        assert_eq!(2., y.calc_ref(&1.));
        let y = x + w.clone();
        assert_eq!(2., y.calc_ref(&1.));
        let z = y.diff_dyn(0);
        assert_eq!(2., z.calc_ref(&1.));

        let wexp = w.exp();
        assert_eq!(1_f32.exp(), wexp.calc_ref(&1.));
        assert_eq!(1_f32.exp(), wexp.diff(0).calc_ref(&1.));
    }

    #[test]
    fn monomial() {
        let x = DimMonomial::<U0, f32, u8>::new(2., 3).to_expr();
        let v = [2.0];
        assert_eq!(16., x.calc_ref(&v));
        let y = x + x;
        assert_eq!(32., y.calc_ref(&v));
        let z = y.diff_dyn(0);
        assert_eq!(48., z.calc_ref(&v));

        let a = z.to_expr() + x;
        assert_eq!(64., a.calc_ref(&v));

        let x1 = x.diff_dyn(0);
        let y1 = x + x1;
        assert_eq!(40., y1.calc_ref(&v));
        assert_eq!(48., y1.diff(0).calc_ref(&v));
    }

    #[cfg(feature = "typenum")]
    #[test]
    fn dynexpr() {
        let v1 = [2., 3.];
        let x: DynExpr<f32, _> = DimMonomial::<U0, f32, u8>::new(2., 2_u8).to_dyn_expr();
        //let x = DimMonomial::<U0, f32, u8>::new(2., 2_u8).to_dyn_expr();
        let y: DynExpr<f32, _> = DimMonomial::<U1, f32, u8>::new(-1., 2_u8).to_dyn_expr();
        assert_eq!(8., x.calc(v1));
        let xpy = x.clone() + y.clone();
        assert_eq!(-1., xpy.calc(v1));
        let xsy = x.clone() - y.clone();
        assert_eq!(17., xsy.calc(v1));

        let xy = x.clone() * y.clone();
        assert_eq!(-72., xy.calc(v1));

        let xe = float_ops::ExNumOps::exp(x.clone());
        assert_eq!((8_f32).exp(), xe.calc(v1));
    }

    #[cfg(feature = "typenum")]
    #[test]
    fn dynexpr_div() {
        let v1 = [2., 3.];
        let x: DynExpr<f32, _> = DimMonomial::<U0, f32, u8>::new(2., 2_u8).to_dyn_expr();
        //let x = DimMonomial::<U0, f32, u8>::new(2., 2_u8).to_dyn_expr();
        let y: DynExpr<f32, _> = DimMonomial::<U1, f32, u8>::new(-1., 2_u8).to_dyn_expr();
        assert_eq!(8., x.calc(v1));

        //compile freeze for div
        let xdy = x.clone() / y.clone();
        assert_eq!(-(8.0 / 9.0), xdy.calc(v1));

        let _add = DynExpr::Dynamic(Arc::new(AddSym::new(x.clone(), y.clone())));
        let _sub = DynExpr::Dynamic(Arc::new(SubSym::new(x.clone(), y.clone())));
        let _mul = DynExpr::Dynamic(Arc::new(MulSym::new(x.clone(), y.clone())));
        //compile freeze for div
        let _div = Arc::new(DivSym::new(x.clone(), y.clone()));
        //let _div = DynExpr(Arc::new(DivSym::new(x.clone(), y.clone())));

        let x = DimMonomial::<U0, f32, u8>::new(6., 2).to_expr();
        let y = DimMonomial::<U1, f32, u8>::new(3., 1);
        let xy = x / y;
        let v = [1., 1.];
        let v1 = [6., 3.];
        assert_eq!(2., xy.calc(v));
        assert_eq!(4., xy.clone().diff(0).calc(v));
        assert_eq!(-2., xy.clone().diff(1).calc(v));
        assert_eq!(24., xy.calc(v1));
        assert_eq!(8., xy.clone().diff(0).calc(v1));
        assert_eq!(-8., xy.diff(1).calc(v1));
    }
}
