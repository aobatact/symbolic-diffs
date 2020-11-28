use crate::*;

pub trait DynamicSymbol<Out, In: ?Sized> {
    type DynamicDerivative : DynamicSymbol<Out, In>;
    fn calc_dyn(&self, value: &In) -> Out;
    fn diff_dyn<Dm>(&self, dm: Dm) -> Self::DynamicDerivative where Dm: DiffMarker;
}

impl<Sym,Out,In> DynamicSymbol<Out,In> for Sym where Sym : Symbol<Out, In> {
    type DynamicDerivative = Sym::Derivative;
    fn calc_dyn(&self, value: &In) -> Out { self.calc_ref(value) }
    fn diff_dyn<Dm>(&self, dm: Dm) -> <Self as dynamic_sym::DynamicSymbol<Out, In>>::DynamicDerivative  where Dm: DiffMarker { self.clone().diff(dm) }
}
