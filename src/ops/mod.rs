//! Set of basic numerical operations
//! These are internaly used from `Expr`.  
use super::*;
use crate::symbols::*;
pub use binary_ops::*;
use core::ops::{Add, Div, Mul, Neg, Sub};
pub use unary_ops::ops_set::*;
pub use unary_ops::*;
mod binary_ops;
pub mod float_ops;
mod unary_ops;

pub trait BasicNumOps:
    Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
    + NumOut
{
}
impl<T> BasicNumOps for T where
    T: Add<Output = Self>
        + Sub<Output = Self>
        + Mul<Output = Self>
        + Div<Output = Self>
        + Neg<Output = Self>
        + NumOut
{
}

/// [`BinaryOp`] marker for [`+`](`core::ops::Add`) with [`AddSym`](`crate::ops::AddSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct AddOp;
impl BinaryOp for AddOp {
    fn op_symbol(&self) -> Option<&'static str> {
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
    Out: Add<Output = Out> + NumOut + Any,
    In: ?Sized + Any + NumsIn<Out>,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) + self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.sym1.diff_dyn(dm) + self.sym2.diff_dyn(dm)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + NumOut + Any,
    In: ?Sized + Any + NumsIn<Out>,
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
    fn op_symbol(&self) -> Option<&'static str> {
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
    Out: NumOut + Any + Sub<Output = Out> + Neg<Output = Out>,
    In: ?Sized + Any + NumsIn<Out>,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) - self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.sym1.diff_dyn(dm) - self.sym2.diff_dyn(dm)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + NumOut + Any + Neg<Output = Out>,
    In: ?Sized + Any + NumsIn<Out>,
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
    fn op_symbol(&self) -> Option<&'static str> {
        Some("*")
    }

    fn format_expression(
        &self,
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
    Sym1: Symbol<Out, In> + Clone,
    Sym2: Symbol<Out, In> + Clone,
    Out: Add<Output = Out> + Mul<Output = Out> + NumOut + Any,
    In: ?Sized + Any + NumsIn<Out>,
{
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) * self.sym2.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        self.sym1.diff_dyn(dm) * self.sym2.clone().to_dyn_expr()
            + self.sym1.clone().to_dyn_expr() * self.sym2.diff_dyn(dm)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + NumOut + Any,
    In: ?Sized + Any + NumsIn<Out>,
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
    fn op_symbol(&self) -> Option<&'static str> {
        Some("/")
    }

    fn format_expression(
        &self,
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
        + Neg<Output = Out>
        + NumOut
        + Any,
    In: ?Sized + Any + NumsIn<Out>,
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
        + NumOut
        + Any
        + Neg<Output = Out>,
    In: ?Sized + Any + NumsIn<Out>,
{
    //type Derivative = DivSym<DynExpr<Out, In>, UnarySym<SquareOp, Sym2, Out, In>, Out, In>;
    type Derivative = DynExpr<Out, In>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        (self.sym1.clone().diff_dyn(dm) * self.sym2.clone().to_dyn_expr()
            - self.sym1.to_dyn_expr() * self.sym2.clone().diff_dyn(dm))
            / UnarySym::new_with_op(SquareOp, self.sym2).to_dyn_expr()
    }
}

macro_rules! op_expr {
    ($t:ident,$tsym:ident,$op:ident, [$($cond:ident),* $(,)*] $(,)* $($cond_nonop:ident),* $(,)*) => {
        impl<L, R, O, I> $t<R> for Expr<L, O, I>
        where
            L: Symbol<O, I>,
            R: Symbol<O, I>,
            O: $( $cond<Output = O> + )* $t<Output = O> + $( $cond_nonop + )* Any + NumOut,
            I: ?Sized + Any + NumsIn<O>,
        {
            type Output = Expr<$tsym<L, R, O, I>, O, I>;
            fn $op(self, r: R) -> Self::Output {
                BinarySym::new(self.inner(), r).into()
            }
        }
    };
}

op_expr!(Add, AddSym, add, []);
op_expr!(Sub, SubSym, sub, [Neg]);
op_expr!(Mul, MulSym, mul, [Add]);
op_expr!(Div, DivSym, div, [Add, Sub, Mul, Neg]);
