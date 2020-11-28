use super::*;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`+`](`core::ops::Add`) with [`AddSym`](`crate::ops::AddSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct AddOp;
impl BinaryOp for AddOp {}
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
/// assert_eq!(4,xy.clone().diff(U0::new()).calc(v));
/// assert_eq!(3,xy.clone().diff(U1::new()).calc(v));
/// assert_eq!(17,xy.calc(v1));
/// assert_eq!(8,xy.clone().diff(U0::new()).calc(v1));
/// assert_eq!(3,xy.diff(U1::new()).calc(v1));
/// ```
pub type AddSym<Sym1, Sym2, Out, In> = BinarySym<AddOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out>,
    In: ?Sized,
{
    type Derivative = AddSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) + self.sym2.calc_ref(value)
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`-`](`core::ops::Sub`) with [`SubSym`](`crate::ops::SubSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SubOp;
impl BinaryOp for SubOp {}
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
/// assert_eq!(4,xy.clone().diff(U0::new()).calc(v));
/// assert_eq!(-3,xy.clone().diff(U1::new()).calc(v));
/// assert_eq!(-1,xy.calc(v1));
/// assert_eq!(8,xy.clone().diff(U0::new()).calc(v1));
/// assert_eq!(-3,xy.diff(U1::new()).calc(v1));
/// ```
pub type SubSym<Sym1, Sym2, Out, In> = BinarySym<SubOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out>,
    In: ?Sized,
{
    type Derivative = SubSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) - self.sym2.calc_ref(value)
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`*`](`core::ops::Mul`) with [`MulSym`](`crate::ops::MulSym`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct MulOp;
impl BinaryOp for MulOp {}
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
/// assert_eq!(12,xy.clone().diff(U0::new()).calc(v));
/// assert_eq!(6,xy.clone().diff(U1::new()).calc(v));
/// assert_eq!(72,xy.calc(v1));
/// assert_eq!(72,xy.clone().diff(U0::new()).calc(v1));
/// assert_eq!(24,xy.diff(U1::new()).calc(v1));
/// ```
pub type MulSym<Sym1, Sym2, Out, In> = BinarySym<MulOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out>,
    In: ?Sized,
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
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
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
impl BinaryOp for DivOp {}
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
/// assert_eq!(4,xy.clone().diff(U0::new()).calc(v));
/// assert_eq!(-2,xy.clone().diff(U1::new()).calc(v));
/// assert_eq!(24,xy.calc(v1));
/// assert_eq!(8,xy.clone().diff(U0::new()).calc(v1));
/// assert_eq!(-8,xy.diff(U1::new()).calc(v1));
/// ```
pub type DivSym<Sym1, Sym2, Out, In> = BinarySym<DivOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out>,
    In: ?Sized,
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
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
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
            O: $( $cond<Output = O> + )* $t<Output = O>,
            I: ?Sized,
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
impl UnaryOp for NegOp {}
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
    Out: Neg<Output = Out>,
    In: ?Sized,
{
    type Derivative = NegSym<Sym::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        -self.sym.calc_ref(value)
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        self.sym.diff(dm).into()
    }
}

impl<S, O, I> Neg for Expr<S, O, I>
where
    S: Symbol<O, I>,
    O: Neg<Output = O>,
    I: ?Sized,
{
    type Output = Expr<NegSym<S, O, I>, O, I>;
    fn neg(self) -> Self::Output {
        NegSym::from(self.0).into()
    }
}

/// [`UnaryOp`](`crate::UnaryOp`) marker for `x` [*](`core::ops::Mul`)`x`
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SquareOp;
impl UnaryOp for SquareOp {}

impl<Sym, Out, In> Symbol<Out, In> for UnarySym<SquareOp, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero,
    In: ?Sized,
{
    type Derivative = impl Symbol<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        let x = self.sym.calc_ref(value);
        x.clone() * x
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        let one = Out::one();
        let two = one.clone() + one;
        Expr::from(Const::from(two)) * self.sym.clone().diff(dm) * self.sym
    }
}

impl<Sym, Out, In: ?Sized> Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone + One + Zero,
{
    pub fn square(self) -> Expr<UnarySym<SquareOp, Sym, Out, In>, Out, In> {
        let sq: UnarySym<SquareOp, Sym, Out, In> = self.inner().into();
        sq.into()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct UnaryPowOp<T>(T);
impl<T> UnaryOp for UnaryPowOp<T> {}

impl<Sym, Out, In: ?Sized, T> Symbol<Out, In> for UnarySym<UnaryPowOp<T>, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Pow<T, Output = Out> + Clone,
    T: Sub<Output = T> + One + Clone,
{
    type Derivative = impl Symbol<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym.calc_ref(value).pow(self.op.0.clone())
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
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
impl<Sym, Out, In: ?Sized> Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone,
{
    pub fn pow_t<T>(self, r: T) -> Expr<UnarySym<UnaryPowOp<T>, Sym, Out, In>, Out, In>
    where
        Out: Pow<T, Output = Out>,
        T: Sub<Output = T> + One + Clone,
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
