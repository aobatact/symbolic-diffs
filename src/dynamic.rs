use crate::float_ops::ExNumConsts;
use crate::ops::*;
use crate::*;
use core::any::Any;
use core::ops::{Add, Div, Mul, Neg, Sub};
use std::sync::Arc;

pub struct DynExpr<Out, In: ?Sized>(pub(crate) Arc<dyn DynamicSymbol<Out, In>>);

impl<Out, In> DynamicSymbol<Out, In> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync,
    In: ?Sized + Any + Send + Sync,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.0.calc_dyn(value)
    }
    fn diff_dyn(&self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In>)> {
        self.0.diff_dyn(dim)
    }
    fn as_any(&self) -> &(dyn Any + Send + Sync) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync,
    In: ?Sized + Any + Send + Sync,
{
    type Derivative = DynExpr<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    fn diff(self, dim: usize) -> DynExpr<Out, In> {
        DynExpr(self.diff_dyn(dim))
    }
}

impl<Out, In: ?Sized> Clone for DynExpr<Out, In> {
    fn clone(&self) -> Self {
        DynExpr(self.0.clone())
    }
}

impl<Out, In> Add<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Add<Out, Output = Out> + Zero,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn add(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        if self.is_zero() {
            other
        } else if other.is_zero() {
            self
        } else {
            DynExpr(Arc::new(AddSym::new(self.0, other.0)))
        }
    }
}

impl<Out, In> Sub<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Sub<Out, Output = Out> + Zero,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn sub(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        if self.is_zero() {
            other
        } else if other.is_zero() {
            self
        } else {
            DynExpr(Arc::new(SubSym::new(self.0, other.0)))
        }
    }
}

impl<Out, In> Mul<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Add<Out, Output = Out> + Mul<Out, Output = Out>,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn mul(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        let l = self.0.as_ref().as_any();
        let r = other.0.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() || r.downcast_ref::<OneSym>().is_some() {
            self
        } else if r.downcast_ref::<ZeroSym>().is_some() || l.downcast_ref::<OneSym>().is_some() {
            other
        } else {
            DynExpr(Arc::new(MulSym::new(self.0, other)))
        }
    }
}

impl<Out, In> Div<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Clone
        + Any
        + Send
        + Sync
        + Add<Out, Output = Out>
        + Mul<Out, Output = Out>
        + Sub<Out, Output = Out>
        + Div<Out, Output = Out>,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn div(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        let l = self.0.as_ref().as_any();
        let r = other.0.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() || r.downcast_ref::<OneSym>().is_some() {
            self
        } else {
            DynExpr(Arc::new(MulSym::new(self.0, other)))
        }
    }
}

impl<Out, In> Zero for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Add<Output = Out> + Zero,
    In: ?Sized + Any + Send + Sync,
{
    #[inline]
    fn zero() -> Self {
        DynExpr(Arc::new(ZeroSym))
    }
    fn is_zero(&self) -> bool {
        self.0.as_ref().as_any().downcast_ref::<ZeroSym>().is_some()
    }
}

impl<Out, In> One for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Add<Output = Out> + Zero + One,
    In: ?Sized + Any + Send + Sync,
{
    #[inline]
    fn one() -> Self {
        DynExpr(Arc::new(OneSym))
    }
    //fn is_one(&self) -> bool { self.0.as_ref().as_any().downcast_ref::<OneSym>().is_some() }
}

impl<Out, In> Neg for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Neg<Output = Out> + Zero,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn neg(self) -> DynExpr<Out, In> {
        if self.is_zero() {
            DynExpr::zero()
        } else {
            DynExpr(Arc::new(NegSym::new_with_op(NegOp, self.0)))
        }
    }
}

impl<Out, In> ExNumConsts for DynExpr<Out, In>
where
    Out: ExNumConsts + Any + Send + Sync + Clone + Zero,
{
    fn e() -> Self {
        DynExpr(Arc::new(Const(Out::e())))
    }
    fn ln_10() -> Self {
        DynExpr(Arc::new(Const(Out::ln_10())))
    }
    fn ln_2() -> Self {
        DynExpr(Arc::new(Const(Out::ln_2())))
    }
    fn log10_e() -> Self {
        DynExpr(Arc::new(Const(Out::log10_e())))
    }
    fn log10_2() -> Self {
        DynExpr(Arc::new(Const(Out::log10_2())))
    }
    fn log2_10() -> Self {
        DynExpr(Arc::new(Const(Out::log2_10())))
    }
    fn log2_e() -> Self {
        DynExpr(Arc::new(Const(Out::log2_e())))
    }
    fn two() -> Self {
        DynExpr(Arc::new(Const(Out::two())))
    }
}

/*
//needs specialization
impl<Out, In> Add<Arc<dyn DynamicSymbol<Out, In>>> for Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>
    where Out : Clone + Any + Send + Sync + Add<Out, Output = Out>,In : ?Sized  + Any + Send + Sync,
{
    type Output = Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>;
    fn add(self, other : Arc<dyn DynamicSymbol<Out, In>>) -> Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In> {
        let l = self.0.as_ref().as_any();
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

#[cfg(test)]
mod tests {
    //use crate::dynamic::*;
    //use crate::float_ops::*;
    use crate::*;
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
        let v = arr![f32; 2.0];
        assert_eq!(16., x.calc_dyn(&v));
        let y = x + x;
        assert_eq!(32., y.calc_dyn(&v));
        let z = y.diff_dyn(0);
        assert_eq!(48., z.calc_dyn(&v));

        let a = z.to_expr() + x;
        assert_eq!(64., a.calc_dyn(&v));
        assert_eq!(64., a.calc_ref(&v));
    }
}
