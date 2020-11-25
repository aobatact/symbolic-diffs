use core::marker::PhantomData;
use core::ops::{Mul, Sub};
use generic_array::{ArrayLength, GenericArray};
use num_traits::{One, Pow, Zero};
use typenum::{
    marker_traits::{Bit, Unsigned},
    operator_aliases::Le,
    type_operators::IsLess,
    uint::{UInt, UTerm},
};

///Set of basic numerical operations
pub mod ops;

///Expression symbol for calculating and differentiation.
pub trait Symbol<Out, In = Out>: Clone {
    type Derivative: Symbol<Out, In>;
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::SymbolEx::calc`) for owned value for convenience.
    fn calc_ref(&self, value: &In) -> Out;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 1 or [`U1`](`typenum::U1`) if there is only one variable.
    fn diff<Dm>(&self, dm: Dm) -> Self::Derivative
    where
        Dm: DiffMarker;
}

///Extention for [`Symbol`](`crate::Symbol`).
pub trait SymbolEx<Out, In>: Symbol<Out, In> {
    /// Shortcut for calculating owned value from [`calc_ref`](`crate::Symbol::calc_ref`).
    #[inline]
    fn calc(&self, value: In) -> Out {
        self.calc_ref(&value)
    }
}

impl<Sym: Symbol<O, I>, O, I> SymbolEx<O, I> for Sym {}

///Marker for the dimention of partial differntiation. See [`diff`](`crate::Symbol::diff`)
pub trait DiffMarker: Copy {
    fn dim(self) -> usize;
}

impl DiffMarker for usize {
    fn dim(self) -> usize {
        self
    }
}

impl DiffMarker for UTerm {
    fn dim(self) -> usize {
        <Self as Unsigned>::USIZE
    }
}

impl<U: Unsigned, B: Bit> DiffMarker for UInt<U, B> {
    fn dim(self) -> usize {
        <Self as Unsigned>::USIZE
    }
}

///Wrapper for [`Symbol`](`crate::Symbol`) for some operation.
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Expr<Sym: Symbol<Out, In>, Out, In = Out>(Sym, PhantomData<Out>, PhantomData<In>);

impl<Sym, O, I> Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
    pub fn inner(&self) -> &Sym {
        &self.0
    }
}

impl<S, O, I> Copy for Expr<S, O, I>
where
    S: Copy + Symbol<O, I>,
    O: Clone,
    I: Clone,
{
}

impl<Sym, O, I> From<Sym> for Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
    #[inline]
    fn from(v: Sym) -> Self {
        Expr(v, PhantomData, PhantomData)
    }
}

impl<Sym, Out: Clone, In: Clone> Symbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
{
    type Derivative = Expr<Sym::Derivative, Out, In>;
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.0.calc_ref(value)
    }
    #[inline]
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        self.0.diff(dm).into()
    }
}

/// Marker for Unary Operation used in [`UnarySym`](`crate::UnarySym`).
pub trait UnaryOp {}

/// Symbol represent Unary Operation.
#[derive(Debug, PartialEq, Eq)]
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

impl<Op, Sym, Out, In> Clone for UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp + Clone,
    Sym: Symbol<Out, In> + Clone,
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

/// Marker for Binary Operation used in [`BinarySym`](`crate::BinarySym`).
pub trait BinaryOp {}

/// Symbol represent Binary Operation.
#[derive(Debug, PartialEq, Eq)]
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

impl<Op, Sym1, Sym2, Out, In> Clone for BinarySym<Op, Sym1, Sym2, Out, In>
where
    Op: BinaryOp + Clone,
    Sym1: Symbol<Out, In> + Clone,
    Sym2: Symbol<Out, In> + Clone,
{
    fn clone(&self) -> Self {
        Self::new_with_op(self.op.clone(), self.sym1.clone(), self.sym2.clone())
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

/// Symbol represent Zero.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ZeroSym;
impl<Out, In> Symbol<Out, In> for ZeroSym
where
    Out: Zero,
{
    type Derivative = ZeroSym;
    ///Returns zero.
    #[inline]
    fn calc_ref(&self, _value: &In) -> Out {
        Out::zero()
    }

    ///Returns Zero Symbol.
    #[inline]
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

///Symbol represent an constant value.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Const<T>(T);
impl<Out, In> Symbol<Out, In> for Const<Out>
where
    Out: Zero + Clone,
{
    type Derivative = ZeroSym;
    /// returns self.
    fn calc_ref(&self, _value: &In) -> Out {
        self.0.clone()
    }
    /// returns [`ZeroSym`](`crate::ZeroSym`)
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

impl<T> From<T> for Const<T>
where
    T: Zero + Clone,
{
    fn from(v: T) -> Const<T> {
        Const(v)
    }
}

impl<O: Zero, I, Sym: Symbol<O, I>> Symbol<O, I> for Option<Sym> {
    type Derivative = Option<Sym::Derivative>;
    fn calc_ref(&self, value: &I) -> O {
        if let Some(sym) = self {
            sym.calc_ref(value)
        } else {
            O::zero()
        }
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<O, I>>::Derivative
    where
        Dm: DiffMarker,
    {
        if let Some(sym) = self {
            Some(sym.diff(dm))
        } else {
            None
        }
    }
}

impl<O: Zero, I, Sym1: Symbol<O, I>, Sym2: Symbol<O, I>> Symbol<O, I> for Result<Sym1, Sym2> {
    type Derivative = Result<Sym1::Derivative, Sym2::Derivative>;
    fn calc_ref(&self, value: &I) -> O {
        match self {
            Ok(sym) => sym.calc_ref(value),
            Err(sym) => sym.calc_ref(value),
        }
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<O, I>>::Derivative
    where
        Dm: DiffMarker,
    {
        match self {
            Ok(sym) => Ok(sym.diff(dm)),
            Err(sym) => Err(sym.diff(dm)),
        }
    }
}

///Represents an single variable.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Variable;
impl<T> Symbol<T, T> for Variable
where
    T: Clone + Zero,
{
    type Derivative = ZeroSym;
    /// Returns cloned "value"
    fn calc_ref(&self, value: &T) -> T {
        value.clone()
    }
    /// returns [`ZeroSym`](`crate::ZeroSym`)
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, T>>::Derivative
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

///Represents an single variable in mulit variable context.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimVariable<Dim: Unsigned>(PhantomData<Dim>);

impl<Dim, T, N: ArrayLength<T>> Symbol<T, GenericArray<T, N>> for DimVariable<Dim>
where
    T: Clone + Zero,
    Dim: Unsigned + IsLess<N>,
{
    type Derivative = ZeroSym;
    fn calc_ref(&self, v: &GenericArray<T, N>) -> T {
        if <Le<Dim, N> as Bit>::BOOL {
            v[Dim::USIZE].clone()
        } else {
            T::zero()
        }
    }
    /// returns [`ZeroSym`](`crate::ZeroSym`)
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, GenericArray<T, N>>>::Derivative
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

///Represents an monomial with coefficient and degree in mulit variable context.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimMonomial<Dim: Unsigned, Coefficient, Degree>(Coefficient, Degree, PhantomData<Dim>);

impl<Dim, T, Degree, N: ArrayLength<T>> Symbol<T, GenericArray<T, N>>
    for DimMonomial<Dim, T, Degree>
where
    T: Clone + Zero + Mul<Output = T> + Pow<Degree, Output = T> + From<Degree>,
    Dim: Unsigned + IsLess<N>,
    Degree: Clone + Sub<Output = Degree> + One,
{
    type Derivative = DimMonomial<Dim, T, Degree>;
    /// Picks the value in the Dim-th dimmension and calculate as `coefficient * (v_dim ^ degree)`
    fn calc_ref(&self, v: &GenericArray<T, N>) -> T {
        if <Le<Dim, N> as Bit>::BOOL && !self.0.is_zero() {
            self.0.clone() * v[Dim::USIZE].clone().pow(self.1.clone())
        } else {
            T::zero()
        }
    }
    /// Differentiate if `dm == dim`, else return zeroed DimMonomial
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<T, GenericArray<T, N>>>::Derivative
    where
        Dm: DiffMarker,
    {
        if dm.dim() == Dim::USIZE {
            DimMonomial(
                self.0.clone() * T::from(self.1.clone()),
                self.1.clone() - Degree::one(),
                PhantomData,
            )
        } else {
            DimMonomial(T::zero(), Degree::one(), PhantomData)
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
