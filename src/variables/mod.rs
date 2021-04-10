use crate::*;
use core::{any::Any, borrow::Borrow, ops::Mul};
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

    fn as_any(&self) -> &(dyn Any) {
        self
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

impl<T> From<T> for Const<T>
where
    T: Clone,
{
    fn from(v: T) -> Const<T> {
        Const(v)
    }
}

impl<T> Mul for Const<T>
where
    T: Mul<Output = T> + Zero + Clone,
{
    type Output = Self;
    fn mul(self, r: Self) -> Self {
        (self.0 * r.0).into()
    }
}

impl<T> One for Const<T>
where
    T: Zero + One + Clone + Mul<Output = T>,
{
    fn one() -> Self {
        T::one().into()
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

    fn as_any(&self) -> &(dyn Any) {
        self
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
