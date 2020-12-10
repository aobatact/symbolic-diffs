#![feature(type_alias_impl_trait)]

use crate::dynamic::DynExpr;
use core::{
    any::Any,
    borrow::Borrow,
    marker::PhantomData,
    ops::{Mul, Sub},
};
use generic_array::{ArrayLength, GenericArray};
use num_traits::{One, Pow, Zero};
use std::sync::Arc;
use typenum::{
    marker_traits::{Bit, Unsigned},
    operator_aliases::Le,
    type_operators::{IsLess, Same},
    True,
};

#[doc(hidden)]
pub mod dynamic;
mod float_ops;
mod ops;

/// Trait for Symbol using dynamic.
pub trait DynamicSymbol<Out, In: ?Sized>: Any {
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::SymbolEx::calc`) for owned value for convenience.
    /// This is for dynamic and must be same as [`calc_ref`](`crate::Symbol::calc_ref`)
    fn calc_dyn(&self, value: &In) -> Out;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>>;
    fn as_any(&self) -> &(dyn Any);
}

///Expression symbol for calculating and differentiation.
pub trait Symbol<Out, In: ?Sized>: DynamicSymbol<Out, In> + Clone {
    /// return type for `diff`
    type Derivative: Symbol<Out, In>;
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::SymbolEx::calc`) for owned value for convenience.
    fn calc_ref(&self, value: &In) -> Out;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff(self, dm: usize) -> Self::Derivative;
}

///Extention for [`Symbol`](`crate::Symbol`).
pub trait SymbolEx<Out, In: ?Sized>: Symbol<Out, In> {
    /// Shortcut for calculating owned value from [`calc_ref`](`crate::Symbol::calc_ref`).
    #[inline]
    fn calc(&self, value: In) -> Out
    where
        In: Sized,
    {
        self.calc_ref(&value)
    }
    ///Wrap this symbol to [`Expr`](`crate::Expr`)
    #[inline]
    fn to_expr(self) -> Expr<Self, Out, In> {
        self.into()
    }
    fn to_dyn_expr(self) -> DynExpr<Out, In> {
        DynExpr(Arc::new(self))
    }
}

impl<Sym: Symbol<O, I>, O, I: ?Sized> SymbolEx<O, I> for Sym {}

/*
impl<Out, In> DynamicSymbol<Out, In> for &'static dyn DynamicSymbol<Out, In>
where
    Out: Clone + Any,
    In: ?Sized + Any,
{
    fn calc_dyn(&self, value: &In) -> Out {
        (*self).calc_dyn(value)
    }
    fn diff_dyn(&self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        (*self).diff_dyn(dim)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}
*/

impl<Out, In> DynamicSymbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    Out: Clone + Any,
    In: ?Sized + Any,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
    }
    fn diff_dyn(&self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.as_ref().diff_dyn(dim)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/*
impl<Out, In> Symbol<Out, In> for &'static dyn DynamicSymbol<Out, In>
where
    Out: Clone + Any,
    In: ?Sized + Any,
{
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    #[inline]
    fn diff(self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.diff_dyn(dim)
    }
}
*/

impl<Out, In> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>>
where
    Out: Clone + Any,
    In: ?Sized + Any,
{
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    #[inline]
    fn diff(self, dim: usize) -> Arc<(dyn DynamicSymbol<Out, In> + 'static)> {
        self.diff_dyn(dim)
    }
}

///Wrapper for [`Symbol`](`crate::Symbol`) for some operation.
#[repr(transparent)]
#[derive(PartialEq, Eq, Debug)]
pub struct Expr<Sym: Symbol<Out, In>, Out, In: ?Sized = Out>(
    Sym,
    PhantomData<Out>,
    PhantomData<In>,
);

impl<Sym, O, I: ?Sized> Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
    /*
    fn new(sym : Sym) -> Self {
        Expr(sym, PhantomData, PhantomData)
    }
    */

    pub fn inner(self) -> Sym {
        self.0
    }

    pub fn inner_borrow(&self) -> &Sym {
        &self.0
    }
}

impl<S, O, I: ?Sized> Clone for Expr<S, O, I>
where
    S: Symbol<O, I>,
{
    fn clone(&self) -> Self {
        self.0.clone().into()
    }
}

impl<S, O, I: ?Sized> Copy for Expr<S, O, I> where S: Copy + Symbol<O, I> {}

impl<Sym, O, I: ?Sized> From<Sym> for Expr<Sym, O, I>
where
    Sym: Symbol<O, I>,
{
    #[inline]
    fn from(v: Sym) -> Self {
        Expr(v, PhantomData, PhantomData)
    }
}

impl<Sym, Out, In> Symbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Clone + Any,
    In: ?Sized + Any,
{
    type Derivative = Expr<Sym::Derivative, Out, In>;
    #[inline]
    fn calc_ref(&self, value: &In) -> Out {
        self.0.calc_ref(value)
    }
    #[inline]
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.0.diff(dm).into()
    }
}

impl<Sym, Out: Clone, In> DynamicSymbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Clone + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.0.calc_dyn(value)
    }
    #[inline]
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        self.0.diff_dyn(dm)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/// Marker for Unary Operation used in [`UnarySym`](`crate::UnarySym`).
pub trait UnaryOp {}

/// [`Symbol`](`crate::Symbol`) represent Unary Operation.
#[derive(Debug, PartialEq, Eq)]
pub struct UnarySym<Op, Sym, Out, In: ?Sized = Out>
where
    Op: UnaryOp,
    Sym: Symbol<Out, In>,
{
    op: Op,
    sym: Sym,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op, Sym, Out, In: ?Sized> UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp,
    Sym: Symbol<Out, In>,
{
    fn new_with_op(op: Op, sym: Sym) -> Self {
        UnarySym {
            op: op,
            sym: sym,
            po: PhantomData,
            pi: PhantomData,
        }
    }
}

impl<Op, Sym, Out, In: ?Sized> Clone for UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp + Clone,
    Sym: Symbol<Out, In>,
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

impl<Op, Sym, Out, In: ?Sized> From<Sym> for UnarySym<Op, Sym, Out, In>
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

impl<Op, Sym, Out, In> DynamicSymbol<Out, In> for UnarySym<Op, Sym, Out, In>
where
    Op: UnaryOp + Default,
    Sym: Symbol<Out, In>,
    In: ?Sized,
    Self: Symbol<Out, In>,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.calc_ref(value)
    }
    #[inline]
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(self.clone().diff(dm))
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/// Marker for Binary Operation used in [`BinarySym`](`crate::BinarySym`).
pub trait BinaryOp {}

/// [`Symbol`](`crate::Symbol`) represent Binary Operation.
#[derive(Debug, PartialEq, Eq)]
pub struct BinarySym<Op, Sym1, Sym2, Out, In: ?Sized = Out>
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

impl<Op: BinaryOp, Sym1: Symbol<Out, In>, Sym2: Symbol<Out, In>, Out, In: ?Sized>
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

impl<Op, Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for BinarySym<Op, Sym1, Sym2, Out, In>
where
    Op: BinaryOp + Default,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    In: ?Sized,
    Self: Symbol<Out, In>,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.calc_ref(value)
    }
    #[inline]
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(self.clone().diff(dm))
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

/// [`Symbol`](`crate::Symbol`) represent Zero.
/// ```
/// # use symbolic_diffs::*;
/// let x = ZeroSym;
/// assert_eq!(0,x.calc(6));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ZeroSym;
impl<Out, In> DynamicSymbol<Out, In> for ZeroSym
where
    Out: Zero,
    In: ?Sized,
{
    #[inline]
    fn calc_dyn(&self, _value: &In) -> Out {
        Out::zero()
    }
    #[inline]
    fn diff_dyn(&self, _dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for ZeroSym
where
    Out: Zero,
    In: ?Sized,
{
    type Derivative = ZeroSym;
    ///Returns zero.
    #[inline]
    fn calc_ref(&self, _value: &In) -> Out {
        Out::zero()
    }

    ///Returns Zero Symbol.
    #[inline]
    fn diff(self, _dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        ZeroSym
    }
}

/// [`Symbol`](`crate::Symbol`) represent Zero.
/// ```
/// # use symbolic_diffs::*;
/// let x = ZeroSym;
/// assert_eq!(0,x.calc(6));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct OneSym;
impl<Out, In> DynamicSymbol<Out, In> for OneSym
where
    Out: One + Zero,
    In: ?Sized,
{
    fn calc_dyn(&self, _value: &In) -> Out {
        Out::one()
    }
    fn diff_dyn(&self, _dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for OneSym
where
    Out: Zero + One,
    In: ?Sized,
{
    type Derivative = ZeroSym;
    ///Returns zero.
    #[inline]
    fn calc_ref(&self, _value: &In) -> Out {
        Out::one()
    }

    ///Returns Zero Symbol.
    #[inline]
    fn diff(self, _dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        ZeroSym
    }
}

///[`Symbol`](`crate::Symbol`) represent an constant value.
/// ```
/// # use symbolic_diffs::*;
/// let x : Const<isize> = 3.into();
/// assert_eq!(3,x.calc(6));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Const<T>(pub(crate) T);
impl<Out, In> DynamicSymbol<Out, In> for Const<Out>
where
    Out: Any + Zero + Clone,
    In: ?Sized,
{
    fn calc_dyn(&self, _value: &In) -> Out {
        self.0.clone()
    }
    fn diff_dyn(&self, _dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In> Symbol<Out, In> for Const<Out>
where
    Out: Zero + Clone + Any,
    In: ?Sized,
{
    type Derivative = ZeroSym;
    /// returns self.
    fn calc_ref(&self, _value: &In) -> Out {
        self.0.clone()
    }
    /// returns [`ZeroSym`](`crate::ZeroSym`)
    fn diff(self, _dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        ZeroSym
    }
}

impl<T> From<T> for Const<T>
where
    T: Clone,
{
    fn from(v: T) -> Const<T> {
        Const(v)
    }
}

impl<T> Mul for Const<T>
where
    T: Mul<Output = T> + Zero + Clone,
{
    type Output = Self;
    fn mul(self, r: Self) -> Self {
        (self.0 * r.0).into()
    }
}

impl<T> One for Const<T>
where
    T: Zero + One + Clone + Mul<Output = T>,
{
    fn one() -> Self {
        T::one().into()
    }
}

impl<Out, In, Sym> DynamicSymbol<Out, In> for Option<Sym>
where
    Out: Zero,
    In: ?Sized,
    Sym: Symbol<Out, In>,
{
    fn calc_dyn(&self, value: &In) -> Out {
        match self {
            Some(sym) => sym.calc_ref(value),
            None => Out::zero(),
        }
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        match self {
            Some(sym) => sym.diff_dyn(dm),
            None => Arc::new(ZeroSym),
        }
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<O, I, Sym> Symbol<O, I> for Option<Sym>
where
    O: Zero,
    I: ?Sized,
    Sym: Symbol<O, I>,
{
    type Derivative = Option<Sym::Derivative>;
    fn calc_ref(&self, value: &I) -> O {
        match self {
            Some(sym) => sym.calc_ref(value),
            None => O::zero(),
        }
    }
    fn diff(self, dm: usize) -> <Self as Symbol<O, I>>::Derivative {
        match self {
            Some(sym) => Some(sym.diff(dm)),
            None => None,
        }
    }
}

impl<Out, In, Sym1, Sym2> DynamicSymbol<Out, In> for Result<Sym1, Sym2>
where
    Out: Zero,
    In: ?Sized,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    fn calc_dyn(&self, value: &In) -> Out {
        match self {
            Ok(sym) => sym.calc_ref(value),
            Err(sym) => sym.calc_ref(value),
        }
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        match self {
            Ok(sym) => sym.diff_dyn(dm),
            Err(sym) => sym.diff_dyn(dm),
        }
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Out, In, Sym1, Sym2> Symbol<Out, In> for Result<Sym1, Sym2>
where
    Out: Zero,
    In: ?Sized,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    type Derivative = Result<Sym1::Derivative, Sym2::Derivative>;
    fn calc_ref(&self, value: &In) -> Out {
        self.calc_dyn(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        match self {
            Ok(sym) => Ok(sym.diff(dm)),
            Err(sym) => Err(sym.diff(dm)),
        }
    }
}

///[`Symbol`](`crate::Symbol`) represents an single variable.
/// ```
/// # use symbolic_diffs::*;
/// let x = Variable;
/// assert_eq!(6,x.calc(6));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Variable;
impl<Out, In> DynamicSymbol<Out, In> for Variable
where
    Out: Zero + One,
    In: ToOwned<Owned = Out> + ?Sized,
{
    fn calc_dyn(&self, value: &In) -> Out {
        value.to_owned()
    }
    fn diff_dyn(&self, _dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(OneSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}
impl<Out, In> Symbol<Out, In> for Variable
where
    Out: Clone + Zero + One + Borrow<In>,
    In: ToOwned<Owned = Out> + ?Sized,
{
    type Derivative = OneSym;
    /// Returns cloned `value`
    fn calc_ref(&self, value: &In) -> Out {
        value.to_owned()
    }
    /// Returns [`ZeroSym`](`crate::ZeroSym`)
    ///
    /// There are some limitation for [`diff`](`crate::Symbol::diff`), so you cann't call like bellow.
    /// ```compile_fail
    /// let x = Variable;
    /// let _ = x.diff(0);
    /// ```
    /// So use like bellow.
    /// ```
    /// # use symbolic_diffs::*;
    /// # use typenum::U0;
    /// let x = Variable;
    /// assert_eq!(1,<Variable as Symbol<i32,i32>>::diff(x,1).calc(2));
    /// //use Expr for convinience
    /// let y = Variable.to_expr();
    /// assert_eq!(1,y.clone().diff(0).calc(3));
    /// assert_eq!(1,y.diff(0).calc(4));
    /// ```
    fn diff(self, _dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        OneSym
    }
}

///[`Symbol`](`crate::Symbol`) represents an single variable in mulit variable context.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = arr![i32; 2,3];
/// let x = DimVariable::<U0>::new();
/// assert_eq!(2,x.calc(v));
/// let y = DimVariable::<U1>::new();
/// assert_eq!(3,y.calc(v));
/// ```
/// The dimention of variable is statically checked.
/// ```compile_fail
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = arr![i32; 2,3];
/// let x = DimVariable::<U2>::new();
/// assert_eq!(0,x.calc(v));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimVariable<Dim: Unsigned>(PhantomData<Dim>);

impl<Dim> DimVariable<Dim>
where
    Dim: Unsigned,
{
    pub fn new() -> DimVariable<Dim> {
        DimVariable(PhantomData)
    }
}

impl<Dim, T, N> DynamicSymbol<T, GenericArray<T, N>> for DimVariable<Dim>
where
    T: Clone + Zero + One,
    Dim: Unsigned + IsLess<N> + Any,
    N: ArrayLength<T>,
    True: Same<<Dim as IsLess<N>>::Output>,
{
    fn calc_dyn(&self, v: &GenericArray<T, N>) -> T {
        debug_assert!(<Le<Dim, N> as Bit>::BOOL);
        v[Dim::USIZE].clone()
    }
    fn diff_dyn(&self, _dm: usize) -> Arc<dyn DynamicSymbol<T, GenericArray<T, N>>> {
        Arc::new(OneSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T, N> Symbol<T, GenericArray<T, N>> for DimVariable<Dim>
where
    T: Clone + Zero + One,
    Dim: Unsigned + IsLess<N> + Any,
    N: ArrayLength<T>,
    True: Same<<Dim as IsLess<N>>::Output>,
{
    type Derivative = OneSym;
    fn calc_ref(&self, v: &GenericArray<T, N>) -> T {
        debug_assert!(<Le<Dim, N> as Bit>::BOOL);
        v[Dim::USIZE].clone()
    }

    /// Returns [`ZeroSym`](`crate::ZeroSym`).
    ///
    /// There are some limitation for [`diff`](`crate::Symbol::diff`), so you can't call like bellow.
    /// ```compile_fail
    /// let x = DimVariable::<U0>::new();
    /// let _ = x.diff(0);
    /// ```
    /// So use [`to_expr`](`crate::SymbolEx::to_expr`) like bellow.
    /// ```
    /// # use symbolic_diffs::*;
    /// # use typenum::*;
    /// # use generic_array::*;
    /// let v = arr![i32; 2,3];
    /// let x = DimVariable::<U0>::new().to_expr();
    /// assert_eq!(1,x.diff(0).calc(v));
    /// let y = DimVariable::<U1>::new().to_expr();
    /// assert_eq!(1,y.diff(0).calc(v));
    /// ```
    fn diff(self, _dm: usize) -> <Self as Symbol<T, GenericArray<T, N>>>::Derivative {
        OneSym
    }
}

///[`Symbol`](`crate::Symbol`) represents an monomial with coefficient and degree in mulit variable context.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = arr![i32; 2,3];
/// let x = DimMonomial::<U0,i32,u8>::new(2,2);
/// assert_eq!(8,x.calc(v));
/// ```
/// The dimention of variable is statically checked.
/// ```compile_fail
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = arr![i32; 2,3];
/// let x = DimMonomial::<U2,i32,u8>::new(2,2);
/// assert_eq!(0,x.calc(v));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DimMonomial<Dim: Unsigned, Coefficient, Degree>(Coefficient, Degree, PhantomData<Dim>);
impl<Dim, Coefficient, Degree> DimMonomial<Dim, Coefficient, Degree>
where
    Dim: Unsigned,
{
    /// create new instance
    pub fn new(c: Coefficient, d: Degree) -> Self {
        Self(c, d, PhantomData)
    }

    /// change the dimension
    pub fn change_dim<NewDim>(self) -> DimMonomial<NewDim, Coefficient, Degree>
    where
        NewDim: Unsigned,
    {
        DimMonomial(self.0, self.1, PhantomData)
    }
}

impl<Dim, T, Degree, N> DynamicSymbol<T, GenericArray<T, N>> for DimMonomial<Dim, T, Degree>
where
    T: Clone + Zero + One + Mul<Output = T> + Pow<Degree, Output = T> + From<Degree> + Any,
    Dim: Unsigned + IsLess<N> + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
    N: ArrayLength<T>,
    True: Same<<Dim as IsLess<N>>::Output>,
{
    fn calc_dyn(&self, v: &GenericArray<T, N>) -> T {
        debug_assert!(<Le<Dim, N> as Bit>::BOOL);
        if !self.0.is_zero() {
            /*if self.1.is_one() {
                self.0.clone() * v[Dim::USIZE].clone()
            } else */
            {
                self.0.clone() * v[Dim::USIZE].clone().pow(self.1.clone())
            }
        } else {
            T::zero()
        }
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<T, GenericArray<T, N>>> {
        if dm == Dim::USIZE {
            if self.1.is_one() {
                return Arc::new(Const::from(T::one()));
            } else if !self.1.is_zero() {
                return Arc::new(DimMonomial::<Dim, _, _>(
                    self.0.clone() * T::from(self.1.clone()),
                    self.1.clone() - Degree::one(),
                    PhantomData,
                ));
            }
        }
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T, Degree, N> Symbol<T, GenericArray<T, N>> for DimMonomial<Dim, T, Degree>
where
    T: Clone + Zero + One + Mul<Output = T> + Pow<Degree, Output = T> + From<Degree> + Any,
    Dim: Unsigned + IsLess<N> + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
    N: ArrayLength<T>,
    True: Same<<Dim as IsLess<N>>::Output>,
{
    type Derivative = DimMonomial<Dim, T, Degree>;
    /// Picks the value in the Dim-th dimmension and calculate as `coefficient * (v_dim ^ degree)`
    #[inline]
    fn calc_ref(&self, v: &GenericArray<T, N>) -> T {
        self.calc_dyn(v)
    }
    /// Differentiate if `dm == dim`, else return zeroed DimMonomial.
    ///
    /// There are some limitation for using [`diff`](`crate::Symbol::diff`) directory, so you can't call like bellow.
    /// ```compile_fail
    /// let x = DimVariable::<U0>::new();
    /// let _ = x.diff(0);
    /// ```
    /// So use [`to_expr`](`crate::SymbolEx::to_expr`) like bellow.
    /// ```
    /// # use symbolic_diffs::*;
    /// # use typenum::*;
    /// # use generic_array::*;
    /// let v = arr![i32; 2,3];
    /// let x = DimMonomial::<U0,i32,u8>::new(2,2).to_expr();
    /// assert_eq!(8,x.diff(0).calc(v));
    /// assert_eq!(0,x.diff(1).calc(v));
    /// assert_eq!(4,x.diff(0).diff(0).calc(v));
    /// assert_eq!(0,x.diff(0).diff(1).calc(v));
    /// //let y = DimMonomial::<U1,i32,u8>::new(2,2).to_expr();
    /// let y = x.inner_borrow().change_dim::<U1>().to_expr();
    /// assert_eq!(0,y.diff(0).calc(v));
    /// assert_eq!(12,y.diff(1).calc(v));
    /// ```
    fn diff(self, dm: usize) -> <Self as Symbol<T, GenericArray<T, N>>>::Derivative {
        if dm == Dim::USIZE && !self.1.is_zero() {
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
