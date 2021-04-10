use crate::ops::*;
use crate::*;
use core::{
    any::Any,
    ops::{Add, Div, Mul, Neg, Sub},
};
use std::sync::Arc;

/*
unsafe impl<Out: Send + Sync, In: ?Sized + Send + Sync> Send for DynExpr<Out, In> {}
unsafe impl<Out: Send + Sync, In: ?Sized + Send + Sync> Sync for DynExpr<Out, In> {}

impl<Out, In: ?Sized> From<Arc<dyn DynamicSymbol<Out, In>>> for DynExpr<Out, In> {
    fn from(sym: Arc<dyn DynamicSymbol<Out, In>>) -> Self {
        DynExpr(sym)
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
    fn diff_dyn(&self) -> Arc<(dyn DynamicSymbol<Out, In>)> {
        self.0.diff_dyn()
    }
}

impl<Out, In> Symbol<Out, In> for DynExpr<Out, In>
where
    Out: Any,
    In: ?Sized + Any,
{
    type Derivative = DynExpr<Out, In>;
    fn diff(self) -> DynExpr<Out, In> {
        self.diff_dyn().into()
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
        AddSym::new(self.0, other.0).to_dyn_expr()
    }
}

impl<Out, In> Sub<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Any + Sub<Output = Out> + Zero + Neg<Output = Out>,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn sub(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        SubSym::new(self.0, other.0).to_dyn_expr()
    }
}

impl<Out, In> Mul<DynExpr<Out, In>> for DynExpr<Out, In>
where
    Out: Any + Add<Output = Out> + Mul<Output = Out> + Zero,
    In: ?Sized + Any,
{
    type Output = DynExpr<Out, In>;
    fn mul(self, other: DynExpr<Out, In>) -> DynExpr<Out, In> {
        MulSym::new(self, other).to_dyn_expr()
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
        unimplemented!("with div, compile freeze");
        DivSym::new(self.0, other).to_dyn_expr()
    }
}
*/

#[cfg(test)]
mod tests {
    use crate::dynamic::*;
    use std::sync::Arc;

    #[test]
    fn variable() {
        let x: Expr<Variable, isize> = Variable.into();
        let y: Expr<Variable, isize> = Variable.into();

        let n = DynExpr(Arc::new(DivSym::new(x.clone(), y.clone())));
    }
}
