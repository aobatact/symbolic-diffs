#![feature(min_type_alias_impl_trait)]

use core::{any::Any, fmt::Display, marker::PhantomData};
use num_traits::{One, Pow, Zero};
use std::fmt;
use std::sync::Arc;

mod display;
//#[doc(hidden)]
mod dynamic;
mod enum_based;
pub mod float_ops;
pub mod ops;
pub mod symbols;

pub use float_ops::{ExNumConsts, ExNumOps};
pub use symbols::variables::*;

/// Trait for Symbol using dynamic.
pub trait DynamicSymbol<Out, In: ?Sized>: Any + Display {
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::SymbolEx::calc`) for owned value for convenience.
    fn calc_ref(&self, value: &In) -> Out;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>>;
    /// Convert to any for downcast.
    fn as_any(&self) -> &(dyn Any);
}

///Expression symbol for calculating and differentiation.
pub trait Symbol<Out, In: ?Sized>: DynamicSymbol<Out, In> + Clone {
    /// return type for `diff`
    type Derivative: Symbol<Out, In>;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff(self, dm: usize) -> Self::Derivative;

    /// Shortcut for calculating owned value from [`calc_ref`](`crate::DynamicSymbol::calc_ref`).
    #[inline]
    fn calc(&self, value: In) -> Out
    where
        In: Sized,
    {
        self.calc_ref(&value)
    }
}

///Extention for [`Symbol`](`crate::Symbol`).
pub trait SymbolEx<Out, In: ?Sized>: Symbol<Out, In> {
    ///Wrap this symbol to [`Expr`](`crate::Expr`)
    fn to_expr(self) -> Expr<Self, Out, In> {
        self.into()
    }

    ///Wrap this symbol to [`DynExpr`]
    fn to_dyn_expr(self) -> DynExpr<Out, In> {
        DynExpr(Arc::new(self))
    }
}

impl<Sym: Symbol<O, I>, O, I: ?Sized> SymbolEx<O, I> for Sym {}

impl<Out, In> DynamicSymbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    Out: Any,
    In: ?Sized + Any,
{
    fn calc_ref(&self, value: &In) -> Out {
        self.as_ref().calc_ref(value)
    }
    fn diff_dyn(&self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.as_ref().diff_dyn(dim)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    Out: Any,
    In: ?Sized + Any,
{
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    #[inline]
    fn diff(self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.diff_dyn(dim)
    }
}

pub struct DynExpr<Out, In: ?Sized>(pub(crate) Arc<dyn DynamicSymbol<Out, In>>);

///Wrapper for [`Symbol`](`crate::Symbol`) for some operation.
/// We currently needs this because of the restriction around specialization.
/// (We cannot impl Ops like Add because downside crate may impl Symbol for integer and this conflicts with current Add of integer)
/// Use this when your operation is statically known. Use [`DynExpr`] for dynamic operation.
#[repr(transparent)]
#[derive(PartialEq, Eq, Debug)]
pub struct Expr<Sym: Symbol<Out, In>, Out, In: ?Sized = Out>(
    Sym,
    PhantomData<Out>,
    PhantomData<In>,
);

impl<Sym, O, I: ?Sized> Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
    pub fn inner(self) -> Sym {
        self.0
    }

    pub fn inner_borrow(&self) -> &Sym {
        &self.0
    }
}

impl<S, O, I: ?Sized> Clone for Expr<S, O, I>
where
    S: Symbol<O, I>,
{
    fn clone(&self) -> Self {
        self.0.clone().into()
    }
}

impl<S, O, I: ?Sized> Copy for Expr<S, O, I> where S: Copy + Symbol<O, I> {}

impl<Sym, O, I: ?Sized> From<Sym> for Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
    #[inline]
    fn from(v: Sym) -> Self {
        Expr(v, PhantomData, PhantomData)
    }
}

impl<Sym, Out, In> Symbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Clone + Any,
    In: ?Sized + Any,
{
    type Derivative = Expr<Sym::Derivative, Out, In>;
    #[inline]
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.0.diff(dm).into()
    }
}

impl<Sym, Out: Clone, In> DynamicSymbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Clone + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.0.calc_ref(value)
    }
    #[inline]
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        self.0.diff_dyn(dm)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}
