use crate::ops::*;
use crate::*;

pub enum EExpr<Out, In: ?Sized = Out> {
    Zero,
    One,
    Const(Out),
    Variable(usize),
    Unary(UnarySym<UnaryOpSet, Arc<EExpr<Out, In>>, Out, In>),
    Binary(BinarySym<BinaryOpSet, Arc<EExpr<Out, In>>, Arc<EExpr<Out, In>>, Out, In>),
    Dyn(DynExpr<Out, In>),
}

impl<Out, In: ?Sized> Clone for EExpr<Out, In> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<Out, In: ?Sized> Display for EExpr<Out, In> {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}

impl<Out, In> DynamicSymbol<Out, In> for EExpr<Out, In>
where
    Out: BasicNumOps + Any,
    In: NumsIn<Out> + ?Sized + Any,
{
    fn calc_ref(&self, i: &In) -> Out {
        match self {
            EExpr::Zero => Out::zero(),
            EExpr::One => Out::one(),
            EExpr::Const(c) => c.clone(),
            EExpr::Variable(d) => i.get_variable(*d),
            EExpr::Unary(u) => u.calc_ref(i),
            EExpr::Binary(b) => b.calc_ref(i),
            EExpr::Dyn(d) => d.calc_ref(i),
        }
    }
    fn diff_dyn(&self, dim: usize) -> DynExpr<Out, In> {
        match self {
            EExpr::Zero | EExpr::One | EExpr::Const(_) => DynExpr::zero(),
            EExpr::Variable(d) => DimVariable::with_dimension(*d).diff_dyn(dim),
            EExpr::Unary(u) => u.diff_dyn(dim),
            EExpr::Binary(b) => b.diff_dyn(dim),
            EExpr::Dyn(d) => d.diff_dyn(dim),
        }
    }
    fn as_any(&self) -> &(dyn std::any::Any) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for EExpr<Out, In>
where
    Out: BasicNumOps + Any,
    In: NumsIn<Out> + ?Sized + Any,
{
    type Derivative = EExpr<Out, In>;
    fn diff(self, _: usize) -> EExpr<Out, In> {
        todo!()
    }
}

impl<Out, In, S> DynamicSymbol<Out, In> for Arc<S>
where
    Out: NumOut + Any,
    In: Any + ?Sized,
    S: DynamicSymbol<Out, In>,
{
    fn calc_ref(&self, i: &In) -> Out {
        self.as_ref().calc_ref(i)
    }
    fn diff_dyn(&self, dm: usize) -> symbols::dyn_expr::DynExpr<Out, In> {
        self.as_ref().diff_dyn(dm)
    }
    fn as_any(&self) -> &(dyn std::any::Any + 'static) {
        self.as_ref().as_any()
    }
}

impl<Out, In, S> Symbol<Out, In> for Arc<S>
where
    Out: NumOut + Any,
    In: Any + ?Sized,
    S: Symbol<Out, In>,
{
    type Derivative = Arc<S::Derivative>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        Arc::new((*self).clone().diff(dm))
    }
}
