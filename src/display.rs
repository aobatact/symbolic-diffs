use crate::*;
use core::fmt::Display;

impl Display for ZeroSym {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}

impl Display for OneSym {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}

impl<T> Display for Const<T> {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}

impl<Dim: typenum::Unsigned> Display for DimVariable<Dim> {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}
impl<Dim: typenum::Unsigned, Coefficient, Degree> Display
    for DimMonomial<Dim, Coefficient, Degree>
{
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}

impl<Op: UnaryOp, Sym: Symbol<Out, In>, Out, In: ?Sized> Display for UnarySym<Op, Sym, Out, In> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        Op::format_expression(f, |f| self.sym.fmt(f))
    }
}

impl<Op: BinaryOp, Sym1: Symbol<Out, In>, Sym2: Symbol<Out, In>, Out, In: ?Sized> Display
    for BinarySym<Op, Sym1, Sym2, Out, In>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        Op::format_expression(f, |f| self.sym1.fmt(f), |f| self.sym2.fmt(f))
    }
}

impl<Sym: Symbol<Out, In>, Out, In: ?Sized> Display for Expr<Sym, Out, In> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str("x")
    }
}
