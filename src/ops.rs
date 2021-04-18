//! Set of basic numerical operations
//! These are internaly used from `Expr`.  
use super::*;
use crate::symbols::*;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// [`BinaryOp`] marker for [`+`](`core::ops::Add`) with [`AddSym`](`crate::ops::AddSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct AddOp;
impl BinaryOp for AddOp {
    fn op_symbol() -> Option<&'static str> {
        Some("+")
    }
}
/// Represent [`+`](`core::ops::Add`) Symbol
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x + y;
/// let v = [1, 1];
/// let v1 = [2, 3];
/// assert_eq!(5,xy.calc(v));
/// assert_eq!(4,xy.clone().diff(0).calc(v));
/// assert_eq!(3,xy.clone().diff(1).calc(v));
/// assert_eq!(17,xy.calc(v1));
/// assert_eq!(8,xy.clone().diff(0).calc(v1));
/// assert_eq!(3,xy.diff(1).calc(v1));
/// ```
pub type AddSym<Sym1, Sym2, Out, In> = BinarySym<AddOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: DynamicSymbol<Out, In>,
    Sym2: DynamicSymbol<Out, In>,
    Out: Add<Output = Out> + Any + Zero + One + Clone + Display,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) + self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        BinarySym::new_with_op(AddOp, self.sym1.diff_dyn(dm), self.sym2.diff_dyn(dm)).to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Any + Zero + One + Clone + Display,
    In: ?Sized + Any,
{
    type Derivative = AddSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

/// [`BinaryOp`] marker for [`-`](`core::ops::Sub`) with [`SubSym`](`crate::ops::SubSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SubOp;
impl BinaryOp for SubOp {
    fn op_symbol() -> Option<&'static str> {
        Some("-")
    }
}

/// Represent [`-`](`core::ops::Sub`) Symbol
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x - y;
/// let v = [1, 1];
/// let v1 = [2, 3];
/// assert_eq!(-1,xy.calc(v));
/// assert_eq!(4,xy.clone().diff(0).calc(v));
/// assert_eq!(-3,xy.clone().diff(1).calc(v));
/// assert_eq!(-1,xy.calc(v1));
/// assert_eq!(8,xy.clone().diff(0).calc(v1));
/// assert_eq!(-3,xy.diff(1).calc(v1));
/// ```
pub type SubSym<Sym1, Sym2, Out, In> = BinarySym<SubOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: DynamicSymbol<Out, In>,
    Sym2: DynamicSymbol<Out, In>,
    Out: Sub<Output = Out> + Any + Display + One + Zero + Clone,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) - self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        BinarySym::new_with_op(SubOp, self.sym1.diff_dyn(dm), self.sym2.diff_dyn(dm)).to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + Any + Zero + Clone + One + Display,
    In: ?Sized + Any,
{
    type Derivative = SubSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

/// [`BinaryOp`] marker for [`*`](`core::ops::Mul`) with [`MulSym`](`crate::ops::MulSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct MulOp;
impl BinaryOp for MulOp {
    fn op_symbol() -> Option<&'static str> {
        Some("*")
    }

    fn format_expression(
        f: &mut fmt::Formatter<'_>,
        left: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
        right: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
    ) -> Result<(), fmt::Error> {
        f.write_str("(")?;
        left(f)?;
        f.write_str(")(")?;
        right(f)?;
        f.write_str(")")
    }
}

/// Represent [`*`](`core::ops::Mul`) Symbol
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x * y;
/// let v = [1, 1];
/// let v1 = [2, 3];
/// assert_eq!(6,xy.calc(v));
/// assert_eq!(12,xy.clone().diff(0).calc(v));
/// assert_eq!(6,xy.clone().diff(1).calc(v));
/// assert_eq!(72,xy.calc(v1));
/// assert_eq!(72,xy.clone().diff(0).calc(v1));
/// assert_eq!(24,xy.diff(1).calc(v1));
/// ```
pub type MulSym<Sym1, Sym2, Out, In> = BinarySym<MulOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: DynamicSymbol<Out, In> + Clone,
    Sym2: DynamicSymbol<Out, In> + Clone,
    Out: Add<Output = Out> + Mul<Output = Out> + Any + Zero + Clone + One + Display,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) * self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        let sym2diff = self.sym2.diff_dyn(dm);
        let df = BinarySym::new_with_op(
            AddOp,
            BinarySym::new_with_op(MulOp, self.sym1.diff_dyn(dm), self.sym2.clone()),
            BinarySym::new_with_op(MulOp, self.sym1.clone(), sym2diff),
        );
        DynExpr::Dynamic(Arc::new(df))
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Any + Zero + Clone + One + Display,
    In: ?Sized + Any,
{
    type Derivative = AddSym<
        MulSym<Sym1::Derivative, Sym2, Out, In>,
        MulSym<Sym1, Sym2::Derivative, Out, In>,
        Out,
        In,
    >;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        let sym2diff = self.sym2.clone().diff(dm);
        BinarySym::new(
            BinarySym::new(self.sym1.clone().diff(dm), self.sym2),
            BinarySym::new(self.sym1, sym2diff),
        )
    }
}

/// [`BinaryOp`] marker for [`/`](`core::ops::Div`) with [`DivSym`](`crate::ops::DivSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct DivOp;
impl BinaryOp for DivOp {
    fn op_symbol() -> Option<&'static str> {
        Some("/")
    }

    fn format_expression(
        f: &mut fmt::Formatter<'_>,
        left: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
        right: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
    ) -> Result<(), fmt::Error> {
        f.write_str("(")?;
        left(f)?;
        f.write_str(")/(")?;
        right(f)?;
        f.write_str(")")
    }
}
/// Represent [`/`](`core::ops::Div`) Symbol
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// let x = DimMonomial::<U0,f32,u8>::new(6.,2).to_expr();
/// let y = DimMonomial::<U1,f32,u8>::new(3.,1);
/// let xy = x / y;
/// let v = [1., 1.];
/// let v1 = [6., 3.];
/// assert_eq!(2.,xy.calc(v));
/// assert_eq!(4.,xy.clone().diff(0).calc(v));
/// assert_eq!(-2.,xy.clone().diff(1).calc(v));
/// assert_eq!(24.,xy.calc(v1));
/// assert_eq!(8.,xy.clone().diff(0).calc(v1));
/// assert_eq!(-8.,xy.diff(1).calc(v1));
/// ```
pub type DivSym<Sym1, Sym2, Out, In> = BinarySym<DivOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out>
        + Sub<Output = Out>
        + Mul<Output = Out>
        + Div<Output = Out>
        + Any
        + Clone
        + Zero
        + One
        + Display,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) / self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.clone().diff(dm).to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/*
impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out>
        + Sub<Output = Out>
        + Mul<Output = Out>
        + Div<Output = Out>
        + Any
        + Clone
        + Zero
        + One
        + Display,
    In: ?Sized + Any,
{
    type Derivative = DivSym<
        SubSym<
            MulSym<Sym1::Derivative, Sym2, Out, In>,
            MulSym<Sym1, Sym2::Derivative, Out, In>,
            Out,
            In,
        >,
        UnarySym<SquareOp, Sym2, Out, In>,
        Out,
        In,
    >;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        DivSym::new(
            SubSym::new(
                MulSym::new(self.sym1.clone().diff(dm), self.sym2.clone()),
                MulSym::new(self.sym1, self.sym2.clone().diff(dm)),
            ),
            UnarySym::new(self.sym2),
        )
    }
}
*/
impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out>
        + Sub<Output = Out>
        + Mul<Output = Out>
        + Div<Output = Out>
        + Any
        + Clone
        + Zero
        + One
        + Display,
    In: ?Sized + Any,
{
    //type Derivative = DivSym<DynExpr<Out, In>, UnarySym<SquareOp, Sym2, Out, In>, Out, In>;
    type Derivative = DynExpr<Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        DivSym::new(
            SubSym::new(
                self.sym1.clone().diff_dyn(dm) * self.sym2.clone().to_dyn_expr(),
                self.sym1.to_dyn_expr() * self.sym2.clone().diff_dyn(dm),
            )
            .to_dyn_expr(),
            UnarySym::new(self.sym2).to_dyn_expr(),
        )
        .to_dyn_expr()
    }
}

macro_rules! op_expr {
    ($t:ident,$tsym:ident,$op:ident, [$($cond:ident),* $(,)*] $(,)* $($cond_nonop:ident),* $(,)*) => {
        impl<L, R, O, I> $t<R> for Expr<L, O, I>
        where
            L: Symbol<O, I>,
            R: Symbol<O, I>,
            O: $( $cond<Output = O> + )* $t<Output = O> + $( $cond_nonop + )* Any + Zero + Clone + One + Display,
            I: ?Sized + Any,
        {
            type Output = Expr<$tsym<L, R, O, I>, O, I>;
            fn $op(self, r: R) -> Self::Output {
                BinarySym::new(self.0, r).into()
            }
        }
    };
}

op_expr!(Add, AddSym, add, []);
op_expr!(Sub, SubSym, sub, []);
op_expr!(Mul, MulSym, mul, [Add]);
op_expr!(Div, DivSym, div, [Add, Sub, Mul], Clone, Zero, One, Display);

/// [`UnaryOp`] marker for [`-`](`core::ops::Neg`) with [`NegSym`](`crate::ops::NegSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct NegOp;
impl UnaryOp for NegOp {
    fn format_expression(
        f: &mut fmt::Formatter<'_>,
        inner: impl FnOnce(&mut fmt::Formatter<'_>) -> Result<(), fmt::Error>,
    ) -> Result<(), fmt::Error> {
        f.write_str("-(")?;
        inner(f)?;
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
        NegSym::from(self.0).into()
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
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero + Any + Display,
    In: ?Sized + Any,
{
    fn calc_ref(&self, value: &In) -> Out {
        let x = self.sym.calc_ref(value);
        x.clone() * x
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.clone().diff(dm).to_dyn_expr()
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym, Out, In> Symbol<Out, In> for SquareSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero + Any + Display,
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
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero + Any + Display,
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

/*
//needs specialization
impl<L, R, Out, In> Pow<R> for Expr<L, Out, In>
where
    L: Symbol<Out, In>,
    R: Sub<Output = R> + One + Clone,
    Out: ExNumOps + Pow<R, Output = Out> + Clone,
{
    type Output = Expr<UnarySym<UnaryPowOp<R>, L, Out, In>, Out, In>;
    fn pow(self, r: R) -> Self::Output {
        UnarySym::new_with_op(UnaryPowOp(r), self.0).to_expr()
    }
}
*/

/// Operation for pow
impl<Sym, Out, In> Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Any + Zero + Clone + One + Display,
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
