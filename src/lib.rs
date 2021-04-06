#![feature(min_type_alias_impl_trait, min_specialization)]

use core::{any::Any, fmt::Display, marker::PhantomData};
use num_traits::{One, Pow, Zero};
use std::fmt;
use std::sync::Arc;

#[doc(hidden)]
mod display;
mod dynamic;
mod float_ops;
mod ops;
mod variables;

pub use float_ops::{ExNumConsts, ExNumOps};
pub use variables::*;

/// Trait for Symbol using dynamic.
pub trait DynamicSymbol<Out, In: ?Sized>: Any + Display {
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::SymbolEx::calc`) for owned value for convenience.
    /// This is for dynamic and must be same as [`calc_ref`](`crate::Symbol::calc_ref`)
    fn calc_dyn(&self, value: &In) -> Out;
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
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::SymbolEx::calc`) for owned value for convenience.
    fn calc_ref(&self, value: &In) -> Out;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff(self, dm: usize) -> Self::Derivative;
}

///Extention for [`Symbol`](`crate::Symbol`).
pub trait SymbolEx<Out, In: ?Sized>: Symbol<Out, In> {
    /// Shortcut for calculating owned value from [`calc_ref`](`crate::Symbol::calc_ref`).
    #[inline]
    fn calc(&self, value: In) -> Out
    where
        In: Sized,
    {
        self.calc_ref(&value)
    }
    ///Wrap this symbol to [`Expr`](`crate::Expr`)
    #[inline]
    fn to_expr(self) -> Expr<Self, Out, In> {
        self.into()
    }

    fn to_dyn_expr(self) -> DynExpr<Out,In>{
        DynExpr(Arc::new(self))
    }
}

impl<Sym: Symbol<O, I>, O, I: ?Sized> SymbolEx<O, I> for Sym {}

impl<Out, In> DynamicSymbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    Out: Any,
    In: ?Sized + Any,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
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
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    #[inline]
    fn diff(self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.diff_dyn(dim)
    }
}

pub struct DynExpr<Out, In: ?Sized>(pub(crate) Arc<dyn DynamicSymbol<Out, In>>);

///Wrapper for [`Symbol`](`crate::Symbol`) for some operation.
/// We currently needs this because of the restriction around specialization.
/// (We cannot impl Ops like Add because downside crate may impl Symbol for integer and this conflicts with current Add of integer)
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
    fn calc_ref(&self, value: &In) -> Out {
        self.0.calc_ref(value)
    }
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
    fn calc_dyn(&self, value: &In) -> Out {
        self.0.calc_dyn(value)
    }
    #[inline]
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        self.0.diff_dyn(dm)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/// Marker for Unary Operation used in [`UnarySym`](`crate::UnarySym`).
pub trait UnaryOp {
    ///Returns the op name.
    fn op_name<'a>() -> &'a str {
        let s = std::any::type_name::<Self>();
        debug_assert!(s.ends_with("Op"));
        let op_name = &s[..s.len() - 2];
        op_name
    }

    ///Formats the expression to display.
    fn format_expression(
        f: &mut fmt::Formatter<'_>,
        inner: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
    ) -> Result<(), fmt::Error> {
        f.write_fmt(format_args!("{}( ", Self::op_name()))?;
        inner(f)?;
        f.write_str(")")
    }
}

/// [`Symbol`](`crate::Symbol`) represent Unary Operation.
#[derive(Debug, PartialEq, Eq)]
pub struct UnarySym<Op, Sym, Out, In: ?Sized = Out>
where
    Op: UnaryOp,
    Sym: Symbol<Out, In>,
{
    op: Op,
    sym: Sym,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op, Sym, Out, In: ?Sized> UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp,
    Sym: Symbol<Out, In>,
{
    fn new_with_op(op: Op, sym: Sym) -> Self {
        UnarySym {
            op: op,
            sym: sym,
            po: PhantomData,
            pi: PhantomData,
        }
    }
}

impl<Op, Sym, Out, In: ?Sized> Clone for UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp + Clone,
    Sym: Symbol<Out, In>,
{
    fn clone(&self) -> Self {
        UnarySym {
            op: self.op.clone(),
            sym: self.sym.clone(),
            po: PhantomData,
            pi: PhantomData,
        }
    }
}

impl<Op, Sym, Out, In: ?Sized> From<Sym> for UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp + Default,
    Sym: Symbol<Out, In>,
{
    #[inline]
    fn from(v: Sym) -> Self {
        UnarySym {
            op: Op::default(),
            sym: v,
            po: PhantomData,
            pi: PhantomData,
        }
    }
}

impl<Op, Sym, Out, In> DynamicSymbol<Out, In> for UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp + Default,
    Sym: Symbol<Out, In>,
    In: ?Sized,
    Self: Symbol<Out, In>,
{
    #[inline]
    default fn calc_dyn(&self, value: &In) -> Out {
        self.calc_ref(value)
    }
    #[inline]
    default fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(self.clone().diff(dm))
    }

    default fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/// Marker for Binary Operation used in [`BinarySym`](`crate::BinarySym`).
pub trait BinaryOp {
    /// Symbol for this expression.
    fn op_symbol() -> Option<&'static str> {
        None
    }

    fn format_expression(
        f: &mut fmt::Formatter<'_>,
        left: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
        right: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
    ) -> Result<(), fmt::Error> {
        let s = std::any::type_name::<Self>();
        debug_assert!(s.ends_with("Op"));
        let op_name = &s[..s.len() - 2];
        if let Some(sym) = Self::op_symbol() {
            left(f)?;
            f.write_fmt(format_args!(" {} ", sym))?;
            right(f)
        } else {
            f.write_fmt(format_args!("{}( ", op_name))?;
            left(f)?;
            right(f)?;
            f.write_str(")")
        }
    }
}

/// [`Symbol`](`crate::Symbol`) represent Binary Operation.
#[derive(Debug, PartialEq, Eq)]
pub struct BinarySym<Op, Sym1, Sym2, Out, In: ?Sized = Out>
where
    Op: BinaryOp,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    op: Op,
    sym1: Sym1,
    sym2: Sym2,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op: BinaryOp, Sym1: Symbol<Out, In>, Sym2: Symbol<Out, In>, Out, In: ?Sized>
    BinarySym<Op, Sym1, Sym2, Out, In>
{
    pub fn new_with_op(op: Op, sym1: Sym1, sym2: Sym2) -> Self {
        BinarySym {
            op: op,
            sym1: sym1,
            sym2: sym2,
            po: PhantomData,
            pi: PhantomData,
        }
    }

    pub fn new(sym1: Sym1, sym2: Sym2) -> Self
    where
        Op: Default,
    {
        BinarySym {
            op: Op::default(),
            sym1: sym1,
            sym2: sym2,
            po: PhantomData,
            pi: PhantomData,
        }
    }
}

impl<Op, Sym1, Sym2, Out, In: ?Sized> Clone for BinarySym<Op, Sym1, Sym2, Out, In>
where
    Op: BinaryOp + Clone,
    Sym1: Symbol<Out, In> + Clone,
    Sym2: Symbol<Out, In> + Clone,
{
    fn clone(&self) -> Self {
        Self::new_with_op(self.op.clone(), self.sym1.clone(), self.sym2.clone())
    }
}

impl<Op, Sym1, Sym2, Out, In: ?Sized> From<(Sym1, Sym2)> for BinarySym<Op, Sym1, Sym2, Out, In>
where
    Op: BinaryOp + Default,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    #[inline]
    fn from(v: (Sym1, Sym2)) -> Self {
        BinarySym::new(v.0, v.1)
    }
}
