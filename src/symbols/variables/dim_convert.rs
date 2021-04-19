use crate::DimMarker;
use crate::DynExpr;
use crate::DynamicSymbol;
use crate::One;
use crate::Symbol;
use core::any::Any;
use core::fmt::Display;
use core::marker::PhantomData;
use num_traits::Zero;
use std::sync::Arc;

pub struct DimConverter<Sym, Fc, Fd, In2>(Sym, Fc, Fd, PhantomData<In2>);

impl<Sym: Clone, F: Clone, Fd: Clone, In2> Clone for DimConverter<Sym, F, Fd, In2> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone(), self.2.clone(), PhantomData)
    }
}

impl<Sym, F, Fd, In1> Display for DimConverter<Sym, F, Fd, In1> {
    fn fmt(&self, _: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        todo!()
    }
}

impl<Sym, F, Fd, Out, In1, In2> DynamicSymbol<Out, In1> for DimConverter<Sym, F, Fd, In2>
where
    Sym: DynamicSymbol<Out, In2> + Any,
    F: Fn(&In1) -> In2 + Any + Clone,
    Fd: Fn(usize) -> usize + Clone + Any + Clone,
    Out: Any + Clone + Zero + One + Display,
    In2: Any,
{
    fn calc_ref(&self, i: &In1) -> Out {
        self.0.calc_ref(&(self.1)(i))
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In1> {
        DynExpr::Dynamic(Arc::new(DimConverter(
            self.0.diff_dyn(self.2(dm)),
            self.1.clone(),
            self.2.clone(),
            PhantomData,
        )))
    }
    fn as_any(&self) -> &(dyn Any) {
        todo!()
    }
}

impl<Sym, F, Fd, Out, In1, In2> Symbol<Out, In1> for DimConverter<Sym, F, Fd, In2>
where
    Sym: Symbol<Out, In2> + Any + Clone,
    F: Fn(&In1) -> In2 + Any + Clone,
    Fd: Fn(usize) -> usize + Clone + Any,
    Out: Any + Clone + Zero + One + Display,
    In2: Any,
{
    type Derivative = DimConverter<Sym::Derivative, F, Fd, In2>;
    fn diff(self, dm: usize) -> Self::Derivative {
        todo!()
    }
}
