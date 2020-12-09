use crate::ops::AddOp;
use crate::*;
use core::any::Any;
use core::ops::Add;
use std::sync::Arc;

/// Trait for Symbol using dynamic.
///
/// This is separate from `Symbol` for some reason.
pub trait DynamicSymbol<Out, In: ?Sized>  {
    fn calc_dyn(&self, value: &In) -> Out;
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>>;
}

pub trait DynamicSymbolEx<Out, In: ?Sized>: DynamicSymbol<Out, In> + Any + Send + Sync {
    fn as_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync>;
    fn as_expr(self: Arc<Self>) -> DynExpr<Out, In>;
}

impl<Sym, Out: 'static, In: 'static + ?Sized> DynamicSymbol<Out, In> for Sym
where
    Sym: Symbol<Out, In> + 'static,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(self.clone().diff(dm))
    }
}

impl<Sym, Out, In> DynamicSymbolEx<Out, In> for Sym
where
    Sym: DynamicSymbol<Out, In> + Any + Send + Sync,
    In: ?Sized,
{
    fn as_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync>
    {
        self
    }
    fn as_expr(self: Arc<Self>) -> DynExpr<Out, In>
    {
        DynExpr(self, PhantomData, PhantomData)
    }
}


/*
impl<Out: 'static, In> DynamicSymbolEx<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    In: ?Sized + 'static,
{
    fn as_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync>
    where
        Self: Any + Send + Sync,
    {
        self
    }
    fn as_expr(self: Arc<Self>) -> DynExpr<Out, In>
    where
        Self: Any + Send + Sync,
    {
        DynExpr(self, PhantomData, PhantomData)
    }
}
*/


impl<Out, In: ?Sized> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>> {
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    fn calc_ref(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.as_ref().diff_dyn(dm)
    }
}

pub struct DynExpr<Out, In: ?Sized>(
    Arc<dyn DynamicSymbolEx<Out, In>>,
    PhantomData<Out>,
    PhantomData<In>,
);

impl<Out, In: ?Sized> Clone for DynExpr<Out, In> {
    fn clone(&self) -> Self {
        DynExpr(self.0.clone(), PhantomData, PhantomData)
    }
}

impl<Out: 'static, In: 'static + ?Sized> Symbol<Out, In> for DynExpr<Out, In>
where
    Self: Sync + Send + Sized,
    
{
    type Derivative = DynExpr<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    fn diff(self, dim: usize) -> <Self as Symbol<Out, In>>::Derivative {
        let d = self.0.diff_dyn(dim);
        //d.as_expr()
        todo!()
    }
}

impl<Out, In> Add<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Add<Output = Out> + 'static + Send + Sync,
    In: ?Sized + Send + Sync + 'static,
{
    type Output = DynExpr<Out, In>;
    fn add(self, r: DynExpr<Out, In>) -> DynExpr<Out, In> {
        if self.clone().0.as_any().downcast::<ZeroSym>().is_ok() {
            return self;
        } else if r.clone().0.as_any().downcast::<ZeroSym>().is_ok() {
            return r;
        } else {
            let a = BinarySym::new_with_op(AddOp, self, r);
            DynExpr(Arc::new(a), PhantomData, PhantomData)
        }
    }
}

/*
impl<Out, In: ?Sized> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>> {
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    fn calc_ref(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.as_ref().diff_dyn(dm)
    }
}*/

#[cfg(test)]
mod tests {
    use crate::dynamic::*;
    //use crate::float_ops::*;
    //use crate::*;
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
