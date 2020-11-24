use core::marker::PhantomData;
use core::ops::{Mul, Sub};
use generic_array::{ArrayLength, GenericArray};
use num_traits::{One, Pow, Zero};
use typenum::{
    marker_traits::{Bit, Unsigned},
    operator_aliases::Le,
    type_operators::IsLess,
};

mod ops;
pub use ops::*;

pub trait Symbol<Out, In = Out>: Clone {
    type Diff: Symbol<Out, In>;
    fn calc(&self, value: In) -> Out;
    fn diff<Dm>(&self, dm: Dm) -> Self::Diff
    where
        Dm: DiffMarker;
}

pub trait DiffMarker: Copy {
    fn dim(self) -> usize;
}
impl DiffMarker for usize {
    fn dim(self) -> usize {
        self
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Expr<Sym, Out, In = Out>(Sym, PhantomData<Out>, PhantomData<In>);

impl<S, O, I> Copy for Expr<S, O, I>
where
    S: Copy,
    O: Clone,
    I: Clone,
{
}

impl<Sym, O, I> From<Sym> for Expr<Sym, O, I> {
    #[inline]
    fn from(v: Sym) -> Self {
        Expr(v, PhantomData, PhantomData)
    }
}

impl<Sym, Out: Clone, In: Clone> Symbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
{
    type Diff = Expr<Sym::Diff, Out, In>;
    fn calc(&self, v: In) -> Out {
        self.0.calc(v)
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Diff
    where
        Dm: DiffMarker,
    {
        self.0.diff(dm).into()
    }
}

pub trait UnaryOp {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnarySym<Op, Sym, Out, In = Out>
where
    Op: UnaryOp,
    Sym: Symbol<Out, In>,
{
    op: Op,
    sym: Sym,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op, Sym, Out, In> From<Sym> for UnarySym<Op, Sym, Out, In>
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

pub trait BinaryOp {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinarySym<Op, Sym1, Sym2, Out, In = Out>
where
    Op: BinaryOp,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    op: Op,
    sym1: Sym1,
    sym2: Sym2,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op: BinaryOp, Sym1: Symbol<Out, In>, Sym2: Symbol<Out, In>, Out, In>
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

impl<Op, Sym1, Sym2, Out, In> From<(Sym1, Sym2)> for BinarySym<Op, Sym1, Sym2, Out, In>
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

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ZeroSym;
impl<Out, In> Symbol<Out, In> for ZeroSym
where
    Out: Zero,
{
    type Diff = ZeroSym;
    fn calc(&self, _v: In) -> Out {
        Out::zero()
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<Out, In>>::Diff
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

impl<T> Symbol<T, T> for T
where
    T: Zero + Clone,
{
    type Diff = ZeroSym;
    fn calc(&self, _v: T) -> T {
        self.clone()
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, T>>::Diff
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Variable;
impl<T> Symbol<T, T> for Variable
where
    T: Clone + Zero,
{
    type Diff = ZeroSym;
    fn calc(&self, v: T) -> T {
        v.clone()
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, T>>::Diff
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimVariable<Dim: Unsigned>(PhantomData<Dim>);

impl<Dim, T, N: ArrayLength<T>> Symbol<T, &GenericArray<T, N>> for DimVariable<Dim>
where
    T: Clone + Zero,
    Dim: Unsigned + IsLess<N>,
{
    type Diff = ZeroSym;
    fn calc(&self, v: &GenericArray<T, N>) -> T {
        if <Le<Dim, N> as Bit>::BOOL {
            v[Dim::USIZE].clone()
        } else {
            T::zero()
        }
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, &GenericArray<T, N>>>::Diff
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimMonomial<Dim: Unsigned, Coefficient, Degree>(Coefficient, Degree, PhantomData<Dim>);

impl<Dim, T, Degree, N: ArrayLength<T>> Symbol<T, &GenericArray<T, N>>
    for DimMonomial<Dim, T, Degree>
where
    T: Clone + Zero + Mul<Output = T> + Pow<Degree, Output = T> + From<Degree>,
    Dim: Unsigned + IsLess<N>,
    Degree: Clone + Sub<Output = Degree> + One,
{
    type Diff = DimMonomial<Dim, T, Degree>;
    fn calc(&self, v: &GenericArray<T, N>) -> T {
        if <Le<Dim, N> as Bit>::BOOL {
            self.0.clone() * v[Dim::USIZE].clone().pow(self.1.clone())
        } else {
            T::zero()
        }
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, &GenericArray<T, N>>>::Diff
    where
        Dm: DiffMarker,
    {
        DimMonomial(
            self.0.clone() * T::from(self.1.clone()),
            self.1.clone() - Degree::one(),
            PhantomData,
        )
    }
}
/*
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimMonomial<Dim: Unsigned, T, Degree: Integer>(T, PhantomData<Dim>, PhantomData<Degree>);

impl<Dim, T, Degree, N: ArrayLength<T>> Symbol<T, GenericArray<T, N>>
    for DimMonomial<Dim, T, Degree>
where
    T: Clone + Zero + Mul<Output = T> + Pow<i8, Output = T> + From<i8>,
    Dim: Unsigned + IsLess<N>,
    Degree: Integer + Clone + Sub<B1> + Sub<P1>,
    <Degree as Sub<P1>>::Output: Integer + Clone + Sub<B1>
{
    type Diff = DimMonomial<Dim, T, <Degree as Sub<P1>> :: Output>;
    fn calc(&self, v: &GenericArray<T, N>) -> T {
        if <Le<Dim, N> as Bit>::BOOL {
            self.0.clone() * v[Dim::USIZE].clone().pow(<Degree as Integer>::I8)
        } else {
            T::zero()
        }
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, GenericArray<T, N>>>::Diff
    where
        Dm: DiffMarker,
    {
        DimMonomial(self.0.clone() * T::from(<Degree as Integer>::I8),PhantomData,PhantomData)
    }
}
*/

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
