use crate::*;
use core::marker::PhantomData;
use std::fmt;

/// Marker for Binary Operation used in [`BinarySym`].
pub trait BinaryOp {
    /// Symbol for this expression.
    fn op_symbol(&self) -> Option<&'static str> {
        None
    }

    fn format_expression(
        &self,
        f: &mut fmt::Formatter<'_>,
        left: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
        right: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
    ) -> Result<(), fmt::Error> {
        let s = std::any::type_name::<Self>();
        debug_assert!(s.ends_with("Op"));
        let op_name = &s[..s.len() - 2];
        if let Some(sym) = self.op_symbol() {
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
pub struct BinarySym<Op, Sym1, Sym2, Out, In: ?Sized = Out> {
    pub(crate) op: Op,
    pub(crate) sym1: Sym1,
    pub(crate) sym2: Sym2,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op: BinaryOp, Sym1: DynamicSymbol<Out, In>, Sym2: DynamicSymbol<Out, In>, Out, In: ?Sized>
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

impl<Op: BinaryOp, Sym1: DynamicSymbol<Out, In>, Sym2: DynamicSymbol<Out, In>, Out, In: ?Sized>
    Display for BinarySym<Op, Sym1, Sym2, Out, In>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::result::Result<(), core::fmt::Error> {
        self.op
            .format_expression(f, |f| self.sym1.fmt(f), |f| self.sym2.fmt(f))
    }
}
