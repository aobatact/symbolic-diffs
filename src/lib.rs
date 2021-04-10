use core::{any::Any, marker::PhantomData};
use num_traits::Zero;
use std::sync::Arc;

mod dynamic;
pub mod ops;
pub mod variables;

pub use variables::*;

/// Trait for Symbol using dynamic.
pub trait DynamicSymbol<Out, In: ?Sized>: Any {
    fn calc_dyn(&self, value: &In) -> Out;
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>>;
}

pub trait Symbol<Out, In: ?Sized>: DynamicSymbol<Out, In> + Clone {
    type Derivative: Symbol<Out, In>;
    fn diff(self) -> Self::Derivative;
}

pub trait SymbolEx<Out, In: ?Sized>: Symbol<Out, In> {
    fn calc(&self, value: In) -> Out
    where
        In: Sized,
    {
        self.calc_dyn(&value)
    }

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
    fn calc_dyn(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
    }
    fn diff_dyn(&self) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.as_ref().diff_dyn()
    }
}

impl<Out, In> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    Out: Any,
    In: ?Sized + Any,
{
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    #[inline]
    fn diff(self) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.diff_dyn()
    }
}

pub struct DynExpr<Out, In: ?Sized>(pub(crate) Arc<dyn DynamicSymbol<Out, In>>);

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

impl<Sym, O, I: ?Sized> From<Sym> for Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
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
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        self.0.diff().into()
    }
}

impl<Sym, Out: Clone, In> DynamicSymbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Clone + Any,
    In: ?Sized + Any,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.0.calc_dyn(value)
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        self.0.diff_dyn()
    }
}

pub trait BinaryOp {}

#[derive(Debug, PartialEq, Eq)]
pub struct BinarySym<Op, Sym1, Sym2, Out, In: ?Sized = Out> {
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
