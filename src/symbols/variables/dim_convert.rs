use crate::*;
use core::any::Any;
use core::fmt::Display;
use std::sync::Arc;

pub struct DimConverter<Sym, D1, D2>(pub Sym, pub D1, pub D2);

impl<Sym: Clone, D1: Clone, D2: Clone> Clone for DimConverter<Sym, D1, D2> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

impl<Sym: Display, D1, D2> Display for DimConverter<Sym, D1, D2> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        self.0.fmt(fmt)
    }
}

impl<Sym, D1, D2, Out, In> DynamicSymbol<Out, In> for DimConverter<Sym, D1, D2>
where
    Sym: DynamicSymbol<Out, (usize, Out)> + Any,
    D1: DimMarker + Clone + Any,
    D2: DimMarker + Clone + Any,
    Out: DynamicOut + Any,
    In: AsRef<[Out]>,
{
    fn calc_ref(&self, i: &In) -> Out {
        self.0
            .calc_ref(&(self.2.dim(), i.as_ref()[self.1.dim()].clone()))
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        let inner = self
            .0
            .diff_dyn(if dm == self.1.dim() { self.2.dim() } else { dm });
        match inner {
            DynExpr::Dynamic(d) => {
                DynExpr::Dynamic(Arc::new(DimConverter(DynExpr::Dynamic(d), self.1, self.2)))
            }
            DynExpr::Zero => DynExpr::Zero,
            DynExpr::One => DynExpr::One,
            DynExpr::Const(c) => DynExpr::Const(c),
        }
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym, D1, D2, Out, In> Symbol<Out, In> for DimConverter<Sym, D1, D2>
where
    Sym: Symbol<Out, (usize, Out)> + Any,
    D1: DimMarker + Clone + Any,
    D2: DimMarker + Clone + Any,
    Out: DynamicOut + Any,
    In: AsRef<[Out]>,
{
    type Derivative = DimConverter<Sym::Derivative, D1, D2>;
    fn diff(self, dm: usize) -> Self::Derivative {
        DimConverter(
            self.0
                .diff(if dm == self.1.dim() { self.2.dim() } else { dm }),
            self.1.clone(),
            self.2.clone(),
        )
    }
}
