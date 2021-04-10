use crate::*;
use core::{any::Any, borrow::Borrow};
use num_traits::{One, Zero};
use std::sync::Arc;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Const<T>(pub T);
impl<Out, In> DynamicSymbol<Out, In> for Const<Out>
where
    Out: Any + Zero + Clone,
    In: ?Sized,
{
    fn calc_dyn(&self, _value: &In) -> Out {
        self.0.clone()
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(Const(Out::zero()))
    }
}

impl<Out, In> Symbol<Out, In> for Const<Out>
where
    Out: Zero + Clone + Any,
    In: ?Sized,
{
    type Derivative = Const<Out>;
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        Const(Out::zero())
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable;
impl<Out, In> DynamicSymbol<Out, In> for Variable
where
    Out: Clone + Zero + Any,
    In: ToOwned<Owned = Out> + ?Sized,
{
    fn calc_dyn(&self, value: &In) -> Out {
        value.to_owned()
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(Const(Out::zero()))
    }
}

impl<Out, In> Symbol<Out, In> for Variable
where
    Out: Clone + Zero + One + Borrow<In> + Any,
    In: ToOwned<Owned = Out> + ?Sized,
{
    type Derivative = Const<Out>;
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        Const(Out::zero())
    }
}
