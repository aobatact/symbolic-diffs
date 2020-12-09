use crate::ops::*;
use crate::*;
use core::any::Any;
use core::ops::{Add, Div, Mul, Sub};
use std::sync::Arc;

pub struct DynExpr<Out, In: ?Sized>(pub(crate) Arc<dyn DynamicSymbol<Out, In> + 'static>);

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

impl<Out, In> Add<Arc<dyn DynamicSymbol<Out, In>>> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Add<Out, Output = Out>,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn add(self, other: Arc<dyn DynamicSymbol<Out, In>>) -> DynExpr<Out, In> {
        let l = self.0.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() {
            DynExpr(other)
        } else if other.as_ref().as_any().downcast_ref::<ZeroSym>().is_some() {
            self
        } else {
            DynExpr(Arc::new(AddSym::new(self.0, other)))
        }
    }
}

impl<Out, In> Sub<Arc<dyn DynamicSymbol<Out, In>>> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Sub<Out, Output = Out>,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn sub(self, other: Arc<dyn DynamicSymbol<Out, In>>) -> DynExpr<Out, In> {
        let l = self.0.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() {
            DynExpr(other)
        } else if other.as_ref().as_any().downcast_ref::<ZeroSym>().is_some() {
            self
        } else {
            DynExpr(Arc::new(SubSym::new(self.0, other)))
        }
    }
}

impl<Out, In> Mul<Arc<dyn DynamicSymbol<Out, In>>> for DynExpr<Out, In>
where
    Out: Clone + Any + Send + Sync + Add<Out, Output = Out> + Mul<Out, Output = Out>,
    In: ?Sized + Any + Send + Sync,
{
    type Output = DynExpr<Out, In>;
    fn mul(self, other: Arc<dyn DynamicSymbol<Out, In>>) -> DynExpr<Out, In> {
        let l = self.0.as_ref().as_any();
        let r = other.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() || r.downcast_ref::<OneSym>().is_some() {
            self
        } else if r.downcast_ref::<ZeroSym>().is_some() || l.downcast_ref::<OneSym>().is_some() {
            DynExpr(other)
        } else {
            DynExpr(Arc::new(MulSym::new(self.0, other)))
        }
    }
}

impl<Out, In> Div<Arc<dyn DynamicSymbol<Out, In>>> for DynExpr<Out, In>
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
    fn div(self, other: Arc<dyn DynamicSymbol<Out, In>>) -> DynExpr<Out, In> {
        let l = self.0.as_ref().as_any();
        let r = other.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() || r.downcast_ref::<OneSym>().is_some() {
            self
        } else {
            DynExpr(Arc::new(MulSym::new(self.0, other)))
        }
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
