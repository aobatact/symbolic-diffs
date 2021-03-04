//! Set of basic numerical operations
//! These are internaly used from `Expr`.  
use super::*;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`+`](`core::ops::Add`) with [`AddSym`](`crate::ops::AddSym`)
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
/// # use generic_array::*;
/// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x + y;
/// let v = arr![i32; 1, 1];
/// let v1 = arr![i32; 2, 3];
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
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) + self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(BinarySym::new_with_op(
            AddOp,
            self.sym1.diff_dyn(dm),
            self.sym2.diff_dyn(dm),
        ))
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = AddSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) + self.sym2.calc_ref(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`-`](`core::ops::Sub`) with [`SubSym`](`crate::ops::SubSym`)
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
/// # use generic_array::*;
/// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x - y;
/// let v = arr![i32; 1, 1];
/// let v1 = arr![i32; 2, 3];
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
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) - self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(BinarySym::new_with_op(
            SubOp,
            self.sym1.diff_dyn(dm),
            self.sym2.diff_dyn(dm),
        ))
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = SubSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) - self.sym2.calc_ref(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`*`](`core::ops::Mul`) with [`MulSym`](`crate::ops::MulSym`)
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
/// # use generic_array::*;
/// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x * y;
/// let v = arr![i32; 1, 1];
/// let v1 = arr![i32; 2, 3];
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
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) * self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        let sym2diff = self.sym2.diff_dyn(dm);
        let df = BinarySym::new_with_op(
            AddOp,
            BinarySym::new_with_op(MulOp, self.sym1.diff_dyn(dm), self.sym2.clone()),
            BinarySym::new_with_op(MulOp, self.sym1.clone(), sym2diff),
        );
        Arc::new(df)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = AddSym<
        MulSym<Sym1::Derivative, Sym2, Out, In>,
        MulSym<Sym1, Sym2::Derivative, Out, In>,
        Out,
        In,
    >;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) * self.sym2.calc_ref(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        let sym2diff = self.sym2.clone().diff(dm);
        BinarySym::new(
            BinarySym::new(self.sym1.clone().diff(dm), self.sym2),
            BinarySym::new(self.sym1, sym2diff),
        )
    }
}

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`/`](`core::ops::Div`) with [`DivSym`](`crate::ops::DivSym`)
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
/// # use generic_array::*;
/// let x = DimMonomial::<U0,i32,u8>::new(6,2).to_expr();
/// let y = DimMonomial::<U1,i32,u8>::new(3,1);
/// let xy = x / y;
/// let v = arr![i32; 1, 1];
/// let v1 = arr![i32; 6, 3];
/// assert_eq!(2,xy.calc(v));
/// assert_eq!(4,xy.clone().diff(0).calc(v));
/// assert_eq!(-2,xy.clone().diff(1).calc(v));
/// assert_eq!(24,xy.calc(v1));
/// assert_eq!(8,xy.clone().diff(0).calc(v1));
/// assert_eq!(-8,xy.diff(1).calc(v1));
/// ```
pub type DivSym<Sym1, Sym2, Out, In> = BinarySym<DivOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) / self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        let res = BinarySym::new_with_op(
            DivOp,
            BinarySym::new_with_op(
                SubOp,
                BinarySym::new_with_op(MulOp, self.sym1.diff_dyn(dm), self.sym2.clone()),
                BinarySym::new_with_op(MulOp, self.sym1.clone(), self.sym2.diff_dyn(dm)),
            ),
            BinarySym::new_with_op(MulOp, self.sym2.clone(), self.sym2.clone()),
        );
        Arc::new(res)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = DivSym<
        SubSym<
            MulSym<Sym1::Derivative, Sym2, Out, In>,
            MulSym<Sym1, Sym2::Derivative, Out, In>,
            Out,
            In,
        >,
        MulSym<Sym2, Sym2, Out, In>,
        Out,
        In,
    >;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) / self.sym2.calc_ref(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(
            BinarySym::new(
                BinarySym::new(self.sym1.clone().diff(dm), self.sym2.clone()),
                BinarySym::new(self.sym1, self.sym2.clone().diff(dm)),
            ),
            BinarySym::new(self.sym2.clone(), self.sym2),
        )
    }
}

macro_rules! op_expr {
    ($t:ident,$tsym:ident,$op:ident, [$($cond:ident),* $(,)*] ) => {
        impl<L, R, O, I> $t<R> for Expr<L, O, I>
        where
            L: Symbol<O, I>,
            R: Symbol<O, I>,
            O: $( $cond<Output = O> + )* $t<Output = O> + Any,
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
op_expr!(Div, DivSym, div, [Add, Sub, Mul]);

/// [`UnaryOp`](`crate::UnaryOp`) marker for [`-`](`core::ops::Neg`) with [`NegSym`](`crate::ops::NegSym`)
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
/// let v = arr![i32; 1, 1];
/// let v1 = arr![i32; 6, 3];
/// assert_eq!(-6,y.calc(v));
/// assert_eq!(-216,y.calc(v1));
/// ```
pub type NegSym<Sym, Out, In> = UnarySym<NegOp, Sym, Out, In>;

impl<Sym, Out, In> Symbol<Out, In> for NegSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Neg<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = NegSym<Sym::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        -self.sym.calc_ref(value)
    }
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

/// [`UnaryOp`](`crate::UnaryOp`) marker for `x` [*](`core::ops::Mul`)`x`
///
/// This is same as `x * x`, but for optimization used in [`UnaryFloatSymbolEx`](`crate::float_ops::UnaryFloatSymbolEx`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SquareOp;
impl UnaryOp for SquareOp {}

impl<Sym, Out, In> Symbol<Out, In> for UnarySym<SquareOp, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero + Any,
    In: ?Sized + Any,
{
    type Derivative = impl Symbol<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        let x = self.sym.calc_ref(value);
        x.clone() * x
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        let one = Out::one();
        let two = one.clone() + one;
        Expr::from(Const::from(two)) * self.sym.clone().diff(dm) * self.sym
    }
}

impl<Sym, Out, In> Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero + Any,
    In: ?Sized + Any,
{
    pub fn square(self) -> Expr<UnarySym<SquareOp, Sym, Out, In>, Out, In> {
        let sq: UnarySym<SquareOp, Sym, Out, In> = self.inner().into();
        sq.into()
    }
}

/// [`UnaryOp`](`crate::UnaryOp`) marker for [`pow`](`num_traits::pow::Pow`)
///
/// Unlike other [`UnaryOp`](`crate::UnaryOp`), this has an field to represent the pow.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let x = Variable.to_expr();
/// let x4 = x.pow_t(4_u8);
/// assert_eq!(16,x4.calc(2));
/// ```
/// Since i32 doesn't impliment [`Pow`](`num_traits::pow::Pow`)`<i32>`, should use i8 as power.
/// ```compile_fail
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let x = Variable.to_expr();
/// let x4 = x.pow_t(4);
/// assert_eq!(16,x4.calc(2));
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct UnaryPowOp<T>(pub(crate) T);
impl<T> UnaryOp for UnaryPowOp<T> {}

impl<Sym, Out, In, T> Symbol<Out, In> for UnarySym<UnaryPowOp<T>, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Pow<T, Output = Out> + Clone + Any,
    T: Sub<Output = T> + One + Clone + Default + Any,
    In: ?Sized + Any,
{
    type Derivative = impl Symbol<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym.calc_ref(value).pow(self.op.0.clone())
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        Expr::from(self.sym.clone().diff(dm))
            * UnarySym::new_with_op(UnaryPowOp(self.op.0 - T::one()), self.sym)
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
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + Any,
    In: ?Sized + Any,
{
    pub fn pow_t<T>(self, r: T) -> Expr<UnarySym<UnaryPowOp<T>, Sym, Out, In>, Out, In>
    where
        Out: Pow<T, Output = Out>,
        T: Sub<Output = T> + One + Clone + Any + Default,
    {
        UnarySym::new_with_op(UnaryPowOp(r), self.inner()).into()
    }
}

/*
#[cfg(test)]
mod tests {
    use crate::*;
    #[test]
    fn add() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(2, x.calc(2));
        assert_eq!(0, x.diff(1).calc(2));
        let _x_m2 = x.clone() + x.clone();
        let x_m2 = x + x;
        assert_eq!(4, x_m2.calc(2));
        assert_eq!(6, x_m2.calc(3));
        let c2: Const<isize> = 2.into();
        let x_2 = x + c2;
        assert_eq!(4, x_2.calc(2));
        assert_eq!(5, x_2.calc(3));
    }
}
*/
