use crate::*;
use core::fmt::Display;

impl Display for ZeroSym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str("0")
    }
}

impl Display for OneSym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str("1")
    }
}

impl<T: Display> Display for Const<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str("x")
    }
}

impl<Dim: typenum::Unsigned> Display for DimVariable<Dim> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("x_{}", Dim::to_i64()))
    }
}

impl<Dim: typenum::Unsigned, Coefficient: Display, Degree: Display> Display
    for DimMonomial<Dim, Coefficient, Degree>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("{} x_{}^{}", self.0, Dim::to_i64(), self.1))
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

#[cfg(test)]
mod tests {
    use crate::*;
    #[test]
    fn diplay_test() {
        let x: Expr<Variable, f32> = Variable.into();
        assert_eq!("x", x.to_string());
        let x1 = x + Const(1.);
        assert_eq!("x + 1", x1.to_string());
        let exp = x.exp();
        assert_eq!("exp( x)", exp.to_string());
        let exp1 = x1.exp();
        assert_eq!("exp( x + 1)", exp1.to_string());
        let xexp = x * exp;
        assert_eq!("(x)(exp( x))", xexp.to_string());
    }
}
