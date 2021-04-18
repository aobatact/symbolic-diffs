use crate::*;
use core::marker::PhantomData;
use std::fmt;

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
pub struct UnarySym<Op, Sym, Out, In: ?Sized = Out> {
    pub(crate) op: Op,
    pub(crate) sym: Sym,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op, Sym, Out, In: ?Sized> UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp,
    Sym: DynamicSymbol<Out, In>,
{
    pub fn new(sym: Sym) -> Self
    where
        Op: Default,
    {
        UnarySym {
            op: Op::default(),
            sym: sym,
            po: PhantomData,
            pi: PhantomData,
        }
    }

    pub fn new_with_op(op: Op, sym: Sym) -> Self {
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
