//! Set of symbols for node in expression.

mod binary_sym;
mod unary_sym;
pub mod variables;

use crate::*;
pub use binary_sym::*;
use core::any::Any;
use core::fmt::Display;
use core::marker::PhantomData;
pub use dyn_expr::DynExpr;
pub use unary_sym::*;
pub use variables::*;
mod dyn_expr;

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

    fn to_dyn_expr(self) -> DynExpr<Out, In> {
        self.0.to_dyn_expr()
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
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.0.diff_dyn(dm)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym: Symbol<Out, In>, Out, In: ?Sized> Display for Expr<Sym, Out, In> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::result::Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}
