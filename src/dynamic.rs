/// currently not working.
use crate::float_ops::*;
use crate::ops::*;
use crate::*;
use core::{
    any::Any,
    //fmt::{Debug, Error, Formatter},
    ops::{Add, Div, Mul, Neg, Sub},
};
use std::sync::Arc;

impl<Out, In: ?Sized> DynExpr<Out, In> {
    pub fn inner_any(&self) -> &(dyn Any) {
        self.0.as_ref().as_any()
    }
    pub fn try_downcast<T>(&self) -> Option<&T>
    where
        T: Any,
    {
        self.inner_any().downcast_ref::<T>()
    }
}

impl<Out, In: ?Sized> From<Arc<dyn DynamicSymbol<Out, In>>> for DynExpr<Out, In> {
    fn from(sym: Arc<dyn DynamicSymbol<Out, In>>) -> Self {
        DynExpr(sym)
    }
}

impl<Out, In> Display for DynExpr<Out, In>
where
    Out: Any,
    In: ?Sized + Any,
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        self.0.fmt(fmt)
    }
}

impl<Out, In> DynamicSymbol<Out, In> for DynExpr<Out, In>
where
    Out: Any,
    In: ?Sized + Any,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.0.calc_dyn(value)
    }
    fn diff_dyn(&self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In>)> {
        self.0.diff_dyn(dim)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for DynExpr<Out, In>
where
    Out: Any,
    In: ?Sized + Any,
{
    type Derivative = DynExpr<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    fn diff(self, dim: usize) -> DynExpr<Out, In> {
        self.diff_dyn(dim).into()
    }
}

impl<Out, In: ?Sized> Clone for DynExpr<Out, In> {
    fn clone(&self) -> Self {
        DynExpr(self.0.clone())
    }
}

impl<Out, In> Add<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Any + Add<Output = Out> + Zero,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn add(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        if self.is_zero() {
            other
        } else if other.is_zero() {
            self
        } else {
            AddSym::new(self.0, other.0).to_dyn_expr()
        }
    }
}

impl<Out, In> Sub<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Any + Sub<Output = Out> + Zero + Neg<Output = Out>,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn sub(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        if self.is_zero() {
            -other
        } else if other.is_zero() {
            self
        } else {
            SubSym::new(self.0, other.0).to_dyn_expr()
        }
    }
}

impl<Out, In> Mul<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Any + Add<Output = Out> + Mul<Output = Out> + Zero,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn mul(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        let l = self.inner_any();
        let r = other.inner_any();
        if self.is_zero() || r.downcast_ref::<OneSym>().is_some() {
            self
        } else if other.is_zero() || l.downcast_ref::<OneSym>().is_some() {
            other
        } else {
            MulSym::new(self, other).to_dyn_expr()
        }
    }
}

impl<Out, In> Div<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Any + Add<Output = Out> + Mul<Output = Out> + Sub<Output = Out> + Div<Output = Out> + Zero,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    #[inline(never)]
    fn div(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        let l = self.inner_any();
        let r = other.inner_any();
        if l.downcast_ref::<ZeroSym>().is_some() || r.downcast_ref::<OneSym>().is_some() {
            self
        } else {
            unimplemented!("with div, compile freeze");
            DivSym::new(self.0, other).to_dyn_expr()
        }
    }
}

impl<Out, In> Zero for DynExpr<Out, In>
where
    Out: Any + Add<Output = Out> + Zero,
    In: ?Sized + Any,
{
    #[inline]
    fn zero() -> Self {
        ZeroSym.to_dyn_expr()
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.try_downcast::<ZeroSym>().is_some()
            || self
                .try_downcast::<Const<Out>>()
                .map_or(false, |Const(x)| x.is_zero())
    }
}

impl<Out, In> One for DynExpr<Out, In>
where
    Out: Any + Add<Output = Out> + Zero + One,
    In: ?Sized + Any,
{
    #[inline]
    fn one() -> Self {
        OneSym.to_dyn_expr()
    }
    #[inline]
    fn is_one(&self) -> bool {
        self.try_downcast::<OneSym>().is_some() //|| self.try_downcast::<Const<Out>>().map_or(false,|Const(x)|x.is_one())
    }
}

impl<Out, In> Neg for DynExpr<Out, In>
where
    Out: Any + Neg<Output = Out> + Zero,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn neg(self) -> DynExpr<Out, In> {
        if self.is_zero() {
            DynExpr::zero()
        } else {
            NegSym::new_with_op(NegOp, self.0).to_dyn_expr()
        }
    }
}

macro_rules! as_dyn_expr {
    (c $($m:ident),* $(,)*) => {
        $(
        fn $m() -> Self {
            Const(Out::$m()).to_dyn_expr()
        })*
    };
    (f $($m:ident),* $(,)*) => {
        $(
        fn $m(self) -> Self {
            <Self as UnaryFloatSymbolEx<Out, In>>::$m(self).to_dyn_expr()
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
    In: Any,
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
        BinarySym::new_with_op(PowOp, self.0, r).to_dyn_expr()
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
        Out: Pow<T, Output = Out>,
        T: Sub<Output = T> + One + Clone + Any + Default,
    {
        UnarySym::new_with_op(UnaryPowOp(r), self.0).to_dyn_expr()
    }
}

/*
//needs specialization
impl<Out, In> Add<Arc<dyn DynamicSymbol<Out, In>>> for Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>
    where Out : Clone + Any + Add<Out, Output = Out>,In : ?Sized  + Any,
{
    type Output = Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>;
    fn add(self, other : Arc<dyn DynamicSymbol<Out, In>>) -> Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In> {
        let l = self.inner_any();
        if l.downcast_ref::<ZeroSym>().is_some() {
            other.to_expr()
        } else if other.as_ref().as_any().downcast_ref::<ZeroSym>().is_some() {
            self
        } else {
            Expr::new(Arc::new(AddSym::new(self.0,other)))
        }
    }
}
*/
//pub type DynExprMV<T, Dim> = DynExpr<T, GenericArray<T, Dim>>;

#[cfg(test)]
mod tests {
    use crate::dynamic::*;
    use generic_array::*;
    use std::sync::Arc;
    use typenum::*;

    #[test]
    fn variable() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(1, x.calc_dyn(&1));
        let y = x + x;
        assert_eq!(2, y.calc_dyn(&1));
        let z = y.diff_dyn(0);
        assert_eq!(2, z.calc_dyn(&2));

        let x: Expr<Variable, f32> = Variable.into();
        let w = Arc::new(x);
        assert_eq!(1., x.calc_dyn(&1.));
        let w = (w as Arc<dyn DynamicSymbol<f32, f32>>).to_expr();
        assert_eq!(1., x.calc_dyn(&1.));
        let y = w.clone() + w.clone();
        assert_eq!(2., y.calc_dyn(&1.));
        let y = w.clone() + x;
        assert_eq!(2., y.calc_dyn(&1.));
        let y = x + w.clone();
        assert_eq!(2., y.calc_dyn(&1.));
        let z = y.diff_dyn(0);
        assert_eq!(2., z.calc_dyn(&1.));

        let wexp = w.exp();
        assert_eq!(1_f32.exp(), wexp.calc_dyn(&1.));
        assert_eq!(1_f32.exp(), wexp.calc_ref(&1.));
        assert_eq!(1_f32.exp(), wexp.diff(0).calc_ref(&1.));
    }

    #[test]
    fn monomial() {
        let x = DimMonomial::<U0, f32, u8>::new(2., 3).to_expr();
        let v = [2.0];
        assert_eq!(16., x.calc_dyn(&v));
        let y = x + x;
        assert_eq!(32., y.calc_dyn(&v));
        let z = y.diff_dyn(0);
        assert_eq!(48., z.calc_dyn(&v));
        assert_eq!(48., z.calc_ref(&v));

        let a = z.to_expr() + x;
        assert_eq!(64., a.calc_dyn(&v));
        assert_eq!(64., a.calc_ref(&v));

        let x1 = x.diff_dyn(0);
        let y1 = x + x1;
        assert_eq!(40., y1.calc_dyn(&v));
        assert_eq!(48., y1.diff(0).calc_dyn(&v));
    }

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

        //compile freeze for div
        //let xdy = x.clone() / y.clone();
        //assert_eq!(-(8.0/9.0), xdy.calc(v1));

        let xe = float_ops::ExNumOps::exp(x.clone());
        assert_eq!((8_f32).exp(), xe.calc(v1));

        let _add = DynExpr(Arc::new(AddSym::new(x.clone(), y.clone())));
        let _sub = DynExpr(Arc::new(AddSym::new(x.clone(), y.clone())));
        let _mul = DynExpr(Arc::new(MulSym::new(x.clone(), y.clone())));
        //compile freeze for div
        //let _div = DynExpr(Arc::new(DivSym::new(x.clone(), y.clone())));
    }
}
