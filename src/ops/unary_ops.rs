use crate::ops::*;

/// [`UnaryOp`] marker for [`-`](`core::ops::Neg`) with [`NegSym`](`crate::ops::NegSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct NegOp;
impl UnaryOp for NegOp {
    fn format_expression<Out, In: ?Sized>(
        &self,
        f: &mut fmt::Formatter<'_>,
        inner: &impl DynamicSymbol<Out, In>,
    ) -> Result<(), fmt::Error> {
        f.write_str("-(")?;
        inner.fmt(f)?;
        f.write_str(")")
    }
}

/// Represent Unary[`-`](`core::ops::Neg`) Symbol
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let x = DimMonomial::<U0,i32,u8>::new(6,2).to_expr();
/// let y = -x;
/// let v = [1, 1];
/// let v1 = [6, 3];
/// assert_eq!(-6,y.calc(v));
/// assert_eq!(-216,y.calc(v1));
/// ```
pub type NegSym<Sym, Out, In> = UnarySym<NegOp, Sym, Out, In>;

impl<Sym, Out, In> DynamicSymbol<Out, In> for NegSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Neg<Output = Out> + Any,
    In: ?Sized + Any,
{
    fn calc_ref(&self, value: &In) -> Out {
        -self.sym.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.clone().diff(dm).to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym, Out, In> Symbol<Out, In> for NegSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Neg<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = NegSym<Sym::Derivative, Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.sym.diff(dm).into()
    }
}

impl<S, O, I> Neg for Expr<S, O, I>
where
    S: Symbol<O, I>,
    O: Neg<Output = O> + Any,
    I: ?Sized + Any,
{
    type Output = Expr<NegSym<S, O, I>, O, I>;
    fn neg(self) -> Self::Output {
        NegSym::from(self.inner()).into()
    }
}

/// [`UnaryOp`] marker for `x` [*](`core::ops::Mul`)`x`
///
/// This is same as `x * x`, but for optimization used in [`UnaryFloatSymbolEx`](`crate::float_ops::UnaryFloatSymbolEx`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SquareOp;
impl UnaryOp for SquareOp {}
pub type SquareSym<Sym, Out, In> = UnarySym<SquareOp, Sym, Out, In>;
impl<Sym, Out, In> DynamicSymbol<Out, In> for SquareSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + DynamicOut + Any,
    In: ?Sized + Any,
{
    fn calc_ref(&self, value: &In) -> Out {
        let x = self.sym.calc_ref(value);
        x.clone() * x
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        let one = Out::one();
        let two = one.clone() + one;
        Const::from(two).to_dyn_expr()
            * self.sym.clone().diff_dyn(dm)
            * self.sym.clone().to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym, Out, In> Symbol<Out, In> for SquareSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + DynamicOut + Any,
    In: ?Sized + Any,
{
    type Derivative = impl Symbol<Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        let one = Out::one();
        let two = one.clone() + one;
        (Expr::from(Const::from(two)) * self.sym.clone().diff(dm) * self.sym).inner()
    }
}

impl<Sym, Out, In> Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + DynamicOut + Any,
    In: ?Sized + Any,
{
    pub fn square(self) -> Expr<UnarySym<SquareOp, Sym, Out, In>, Out, In> {
        let sq: UnarySym<SquareOp, Sym, Out, In> = self.inner().into();
        sq.into()
    }
}

/// [`UnaryOp`] marker for [`pow`](`num_traits::pow::Pow`)
///
/// Unlike other [`UnaryOp`], this has an field to represent the pow.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let x = Variable.to_expr();
/// let x4 = x.pow_t(4_u8);
/// assert_eq!(16,x4.calc(2));
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct UnaryPowOp<Exp>(pub(crate) Exp);
impl<Exp> UnaryOp for UnaryPowOp<Exp> {}

impl<Sym, Out, In, Exp> DynamicSymbol<Out, In> for UnarySym<UnaryPowOp<Exp>, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out>
        + Mul<Output = Out>
        + Pow<Exp, Output = Out>
        + Clone
        + Any
        + Zero
        + One
        + Display,
    Exp: Sub<Output = Exp> + One + Clone + Default + Any,
    In: ?Sized + Any,
{
    fn calc_ref(&self, value: &In) -> Out {
        self.sym.calc_ref(value).pow(self.op.0.clone())
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.clone().diff(dm).to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym, Out, In, Exp> Symbol<Out, In> for UnarySym<UnaryPowOp<Exp>, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out>
        + Mul<Output = Out>
        + Pow<Exp, Output = Out>
        + Clone
        + Any
        + Zero
        + One
        + Display,
    Exp: Sub<Output = Exp> + One + Clone + Default + Any,
    In: ?Sized + Any,
{
    type Derivative = impl Symbol<Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        (Expr::from(self.sym.clone().diff(dm))
            * UnarySym::new_with_op(UnaryPowOp(self.op.0 - Exp::one()), self.sym))
        .inner()
    }
}

/// Operation for pow
impl<Sym, Out, In> Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + DynamicOut + Any,
    In: ?Sized + Any,
{
    pub fn pow_t<Exp>(self, r: Exp) -> Expr<UnarySym<UnaryPowOp<Exp>, Sym, Out, In>, Out, In>
    where
        Out: Pow<Exp, Output = Out>,
        Exp: Sub<Output = Exp> + One + Clone + Any + Default,
    {
        UnarySym::new_with_op(UnaryPowOp(r), self.inner()).into()
    }
}

pub mod ops_set {
    use crate::ops::*;
    use crate::symbols::enum_based::EExpr;

    #[derive(Clone, PartialEq, Eq, Hash, Debug)]
    pub enum UnaryOpSet {
        Neg,
        Square,
        FloatOp(FloatOpSet),
    }

    #[derive(Clone, PartialEq, Eq, Hash, Debug)]
    pub enum FloatOpSet {}

    impl UnaryOp for UnaryOpSet {
        fn op_name<'a>(&self) -> &'a str {
            match self {
                UnaryOpSet::Neg => NegOp.op_name(),
                UnaryOpSet::Square => SquareOp.op_name(),
                _ => unimplemented!(),
            }
        }

        ///Formats the expression to display.
        fn format_expression<Out, In: ?Sized>(
            &self,
            f: &mut fmt::Formatter<'_>,
            inner: &impl DynamicSymbol<Out, In>,
        ) -> Result<(), fmt::Error> {
            match self {
                UnaryOpSet::Neg => NegOp.format_expression(f, inner),
                UnaryOpSet::Square => SquareOp.format_expression(f, inner),
                _ => unimplemented!(),
            }
        }
    }

    impl<Sym, Out, In: ?Sized> DynamicSymbol<Out, In> for UnarySym<UnaryOpSet, Sym, Out, In>
    where
        Sym: Symbol<Out, In>,
        Out: BasicNumOps + Any,
        In: Any,
    {
        fn calc_ref(&self, i: &In) -> Out {
            match &self.op {
                UnaryOpSet::Neg => UnarySym::new_with_op(NegOp, self.sym.clone()).calc_ref(i),
                UnaryOpSet::Square => UnarySym::new_with_op(SquareOp, self.sym.clone()).calc_ref(i),
                UnaryOpSet::FloatOp(fop) => todo!(),
            }
        }
        fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
            match &self.op {
                UnaryOpSet::Neg => UnarySym::new_with_op(NegOp, self.sym.clone()).diff_dyn(dm),
                UnaryOpSet::Square => {
                    UnarySym::new_with_op(SquareOp, self.sym.clone()).diff_dyn(dm)
                }
                UnaryOpSet::FloatOp(fop) => todo!(),
            }
        }
        fn as_any(&self) -> &(dyn std::any::Any) {
            todo!()
        }
    }

    impl<Sym, Out, In: ?Sized> Symbol<Out, In> for UnarySym<UnaryOpSet, Sym, Out, In>
    where
        Sym: Symbol<Out, In>,
        Out: BasicNumOps + Any,
        In: Any,
        EExpr<Out, In>: Symbol<Out, In>,
    {
        type Derivative = EExpr<Out, In>;
        fn diff(self, _: usize) -> <Self as Symbol<Out, In>>::Derivative {
            todo!()
        }
    }
}
