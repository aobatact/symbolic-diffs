use crate::*;
use core::{any::Any, fmt::Display};
use num_traits::{One, Zero};
#[cfg(feature = "generic-array1")]
use typenum::marker_traits::Unsigned;

#[cfg(feature = "generic-array1")]
use generic_array::{ArrayLength, GenericArray};
#[cfg(feature = "generic-array1")]
use typenum::{
    marker_traits::Bit,
    operator_aliases::Le,
    type_operators::{IsLess, Same},
    True,
};

///[`Symbol`](`crate::Symbol`) represents an single variable in mulit variable context.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = [2, 3];
/// let x = DimVariable::<U0>::new();
/// assert_eq!(2,x.calc(v));
/// let y = DimVariable::<U1>::new();
/// assert_eq!(3,y.calc(v));
/// ```
/// The dimension of variable is statically checked for typenum.
/// ```compile_fail
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = arr![i32; 2,3];
/// let x = DimVariable::<U2>::new();
/// assert_eq!(0,x.calc(v));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DimVariable<Dim: DimMarker>(Dim);

impl<Dim> DimVariable<Dim>
where
    Dim: DimMarker,
{
    pub fn new() -> DimVariable<Dim>
    where
        Dim: Default,
    {
        DimVariable(Default::default())
    }

    pub fn with_dimension(d: Dim) -> DimVariable<Dim> {
        DimVariable(d)
    }

    pub fn dim(&self) -> usize {
        self.0.clone().dim()
    }
}

impl<Dim: DimMarker> Display for DimVariable<Dim> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("x_{}", self.dim()))
    }
}

impl<Dim: DimMarker + Default> From<Variable> for DimVariable<Dim> {
    fn from(_: Variable) -> Self {
        DimVariable::new()
    }
}

#[cfg(feature = "generic-array1")]
impl<Dim, T, N> DynamicSymbol<T, GenericArray<T, N>> for DimVariable<Dim>
where
    T: Clone + Zero + One,
    Dim: DimMarker + IsLess<N> + Any + Unsigned,
    N: ArrayLength<T>,
    True: Same<<Dim as IsLess<N>>::Output>,
{
    fn calc_ref(&self, v: &GenericArray<T, N>) -> T {
        debug_assert!(<Le<Dim, N> as Bit>::BOOL);
        v[Dim::USIZE].clone()
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<T, GenericArray<T, N>> {
        if dm == self.0.dim() {
            DynExpr::One
        } else {
            DynExpr::Zero
        }
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T> DynamicSymbol<T, [T]> for DimVariable<Dim>
where
    T: Clone + Zero + One,
    Dim: DimMarker + Any,
{
    fn calc_ref(&self, v: &[T]) -> T {
        v[self.0.dim()].clone()
    }

    fn diff_dyn(&self, dm: usize) -> DynExpr<T, [T]> {
        if dm == self.0.dim() {
            DynExpr::One
        } else {
            DynExpr::Zero
        }
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T, const D: usize> DynamicSymbol<T, [T; D]> for DimVariable<Dim>
where
    T: Clone + Zero + One,
    Dim: DimMarker + Any,
{
    fn calc_ref(&self, v: &[T; D]) -> T {
        v[self.0.dim()].clone()
    }

    fn diff_dyn(&self, dm: usize) -> DynExpr<T, [T; D]> {
        debug_assert!(dm < D, "larger dimention {} for {}", dm, D);
        if dm == self.0.dim() {
            DynExpr::One
        } else {
            DynExpr::Zero
        }
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

#[cfg(feature = "generic-array1")]
impl<Dim, T, N> Symbol<T, GenericArray<T, N>> for DimVariable<Dim>
where
    T: Clone + Zero + One + Display + Any,
    Dim: Unsigned + IsLess<N> + Any,
    N: ArrayLength<T>,
    True: Same<<Dim as IsLess<N>>::Output>,
{
    type Derivative = Const<T>;
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
    /// let v = [2,3];
    /// let x = DimVariable::<U0>::new().to_expr();
    /// assert_eq!(1,x.diff(0).calc(v));
    /// let y = DimVariable::<U1>::new().to_expr();
    /// assert_eq!(0,y.diff(0).calc(v));
    /// ```
    fn diff(self, dm: usize) -> <Self as Symbol<T, GenericArray<T, N>>>::Derivative {
        if dm == self.0.dim() {
            Const(T::one())
        } else {
            Const(T::zero())
        }
    }
}

impl<Dim, T> Symbol<T, [T]> for DimVariable<Dim>
where
    T: Clone + Zero + One + Display + Any,
    Dim: DimMarker + Any,
{
    type Derivative = Const<T>;

    fn diff(self, dm: usize) -> <Self as Symbol<T, [T]>>::Derivative {
        if dm == self.0.dim() {
            Const(T::one())
        } else {
            Const(T::zero())
        }
    }
}

impl<Dim, T, const D: usize> Symbol<T, [T; D]> for DimVariable<Dim>
where
    T: Clone + Zero + One + Display + Any,
    Dim: DimMarker + Any,
{
    type Derivative = Const<T>;

    fn diff(self, dm: usize) -> <Self as Symbol<T, [T; D]>>::Derivative {
        debug_assert!(dm < D, "larger dimention {} for {}", dm, D);
        if dm == self.0.dim() {
            Const(T::one())
        } else {
            Const(T::zero())
        }
    }
}
