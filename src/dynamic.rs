use crate::*;
use std::sync::Arc;

pub trait DynamicSymbol<Out, In: ?Sized> {
    fn calc_dyn(&self, value: &In) -> Out;
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>>;
}

impl<Sym, Out: 'static, In: 'static> DynamicSymbol<Out, In> for Sym
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

impl<Out, In: ?Sized> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>> {
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    fn calc_ref(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        self.as_ref().diff_dyn(dm.dim())
    }
}

pub trait DynamicSymbolEx<Out, In: ?Sized> {
    fn to_dyn_expr(self) -> Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>;
}

impl<Out, In: ?Sized> DynamicSymbolEx<Out, In> for Arc<dyn DynamicSymbol<Out, In>>{
    fn to_dyn_expr(self) -> Expr<std::sync::Arc<(dyn dynamic::DynamicSymbol<Out, In> + 'static)>, Out, In> { 
        self.into()
    }
}

pub struct DynUnarySym<Op: UnaryOp, Out, In>(
    Op,
    Arc<dyn DynamicSymbol<Out, In>>,
    PhantomData<Out>,
    PhantomData<In>,
);

pub struct DynBinarySym<Op: BinaryOp, Out, In>(
    Op,
    Arc<dyn DynamicSymbol<Out, In>>,
    Arc<dyn DynamicSymbol<Out, In>>,
    PhantomData<Out>,
    PhantomData<In>,
);

#[cfg(test)]
mod tests {
    use crate::dynamic::DynamicSymbol;
    use crate::*;
    use std::sync::Arc;

    #[test]
    fn variable() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(1, x.calc_dyn(&1));
        let y = x + x;
        assert_eq!(2, y.calc_dyn(&1));
        let z = y.diff_dyn(0);
        assert_eq!(0, z.calc_dyn(&1));

        let w = Arc::new(x);
        assert_eq!(1, x.calc_dyn(&1));
        let w = (w as Arc<dyn DynamicSymbol<isize, isize>>).to_expr();
        assert_eq!(1, x.calc_dyn(&1));
        let y = w.clone() + w.clone();
        assert_eq!(2, y.calc_dyn(&1));
        let y = w.clone() + x;
        assert_eq!(2, y.calc_dyn(&1));
        let y = x + w.clone();
        assert_eq!(2, y.calc_dyn(&1));
        let z = y.diff_dyn(0);
        assert_eq!(0, z.calc_dyn(&1));
    }
}
