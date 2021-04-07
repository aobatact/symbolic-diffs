use crate::*;
use core::{
    any::Any,
    fmt::Display,
    ops::{Add, Mul, Sub},
};
use num_traits::{One, Pow, Zero};
use std::sync::Arc;
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

///[`Symbol`](`crate::Symbol`) represents an monomial with coefficient and degree in mulit variable context.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// let v = [2_i32, 3];
/// let x = DimMonomial::<U0,i32,u8>::new(2,2);
/// assert_eq!(8,x.calc_ref(&v));
/// ```
/// The dimension of variable is statically checked for generic_array.
/// ```compile_fail
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let v = arr![i32; 2,3];
/// let x = DimMonomial::<U2,i32,u8>::new(2,2);
/// assert_eq!(0,x.calc(v));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DimMonomial<Dim: DimMarker, Coefficient, Degree>(
    pub(crate) Coefficient,
    pub(crate) Degree,
    pub(crate) Dim,
);
impl<Dim, Coefficient, Degree> DimMonomial<Dim, Coefficient, Degree>
where
    Dim: DimMarker,
{
    /// create new instance
    pub fn new(c: Coefficient, d: Degree) -> Self
    where
        Dim: Default,
    {
        Self(c, d, Default::default())
    }

    pub fn with_dimension(c: Coefficient, d: Degree, dim: Dim) -> Self {
        Self(c, d, dim)
    }

    /// change the dimension
    pub fn change_dim<NewDim>(self, d: NewDim) -> DimMonomial<NewDim, Coefficient, Degree>
    where
        NewDim: DimMarker,
    {
        DimMonomial(self.0, self.1, d)
    }

    pub fn dim(&self) -> usize {
        self.2.dim()
    }
}

#[cfg(feature = "generic-array1")]
impl<Dim, T, Degree, N> DynamicSymbol<T, GenericArray<T, N>> for DimMonomial<Dim, T, Degree>
where
    T: Clone
        + Zero
        + One
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + From<Degree>
        + Any
        + Display,
    Dim: DimMarker + IsLess<N> + Any + Unsigned,
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
                    self.2,
                ));
            }
        }
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

#[cfg(feature = "generic-array1")]
impl<Dim, T, Degree, N> Symbol<T, GenericArray<T, N>> for DimMonomial<Dim, T, Degree>
where
    T: Clone
        + Zero
        + One
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + From<Degree>
        + Any
        + Display,
    Dim: IsLess<N> + Any + Unsigned,
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
    /// let y = x.inner_borrow().change_dim(U1::default()).to_expr();
    /// assert_eq!(0,y.diff(0).calc(v));
    /// assert_eq!(12,y.diff(1).calc(v));
    /// ```
    fn diff(self, dm: usize) -> <Self as Symbol<T, GenericArray<T, N>>>::Derivative {
        if dm == Dim::USIZE && !self.1.is_zero() {
            DimMonomial(
                self.0.clone() * T::from(self.1.clone()),
                self.1.clone() - Degree::one(),
                self.2,
            )
        } else {
            DimMonomial(T::zero(), Degree::one(), self.2)
        }
    }
}

impl<Dim, T, Degree> DynamicSymbol<T, [T]> for DimMonomial<Dim, T, Degree>
where
    T: Clone
        + Zero
        + One
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + From<Degree>
        + Any
        + Display,
    Dim: DimMarker + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
{
    fn calc_dyn(&self, v: &[T]) -> T {
        if !self.0.is_zero() {
            /*if self.1.is_one() {
                self.0.clone() * v[Dim::USIZE].clone()
            } else */
            {
                self.0.clone() * v[self.dim()].clone().pow(self.1.clone())
            }
        } else {
            T::zero()
        }
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<T, [T]>> {
        if dm == self.dim() {
            if self.1.is_one() {
                return Arc::new(Const::from(T::one()));
            } else if !self.1.is_zero() {
                return Arc::new(DimMonomial::<Dim, _, _>(
                    self.0.clone() * T::from(self.1.clone()),
                    self.1.clone() - Degree::one(),
                    self.2,
                ));
            }
        }
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T, Degree> Symbol<T, [T]> for DimMonomial<Dim, T, Degree>
where
    T: Clone
        + Zero
        + One
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + From<Degree>
        + Any
        + Display,
    Dim: DimMarker + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
{
    type Derivative = DimMonomial<Dim, T, Degree>;
    /// Picks the value in the Dim-th dimmension and calculate as `coefficient * (v_dim ^ degree)`
    #[inline]
    fn calc_ref(&self, v: &[T]) -> T {
        self.calc_dyn(v)
    }

    fn diff(self, dm: usize) -> <Self as Symbol<T, [T]>>::Derivative {
        if dm == self.dim() && !self.1.is_zero() {
            DimMonomial(
                self.0.clone() * T::from(self.1.clone()),
                self.1.clone() - Degree::one(),
                self.2,
            )
        } else {
            DimMonomial(T::zero(), Degree::one(), self.2)
        }
    }
}

impl<Dim, T, Degree, const D: usize> DynamicSymbol<T, [T; D]> for DimMonomial<Dim, T, Degree>
where
    T: Clone
        + Zero
        + One
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + From<Degree>
        + Any
        + Display,
    Dim: DimMarker + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
{
    fn calc_dyn(&self, v: &[T; D]) -> T {
        if !self.0.is_zero() {
            /*if self.1.is_one() {
                self.0.clone() * v[Dim::USIZE].clone()
            } else */
            {
                self.0.clone() * v[self.dim()].clone().pow(self.1.clone())
            }
        } else {
            T::zero()
        }
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<T, [T; D]>> {
        debug_assert!(dm < D);
        if dm == self.dim() {
            if self.1.is_one() {
                return Arc::new(Const::from(T::one()));
            } else if !self.1.is_zero() {
                return Arc::new(DimMonomial::<Dim, _, _>(
                    self.0.clone() * T::from(self.1.clone()),
                    self.1.clone() - Degree::one(),
                    self.2,
                ));
            }
        }
        Arc::new(ZeroSym)
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T, Degree, const D: usize> Symbol<T, [T; D]> for DimMonomial<Dim, T, Degree>
where
    T: Clone
        + Zero
        + One
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + From<Degree>
        + Any
        + Display,
    Dim: DimMarker + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
{
    type Derivative = DimMonomial<Dim, T, Degree>;
    /// Picks the value in the Dim-th dimmension and calculate as `coefficient * (v_dim ^ degree)`
    #[inline]
    fn calc_ref(&self, v: &[T; D]) -> T {
        self.calc_dyn(v)
    }

    fn diff(self, dm: usize) -> <Self as Symbol<T, [T; D]>>::Derivative {
        debug_assert!(dm < D);
        if dm == self.dim() && !self.1.is_zero() {
            DimMonomial(
                self.0.clone() * T::from(self.1.clone()),
                self.1.clone() - Degree::one(),
                self.2,
            )
        } else {
            DimMonomial(T::zero(), Degree::one(), self.2)
        }
    }
}

//T = Coefficient
impl<Dim, T, Degree, const N: usize> From<DimMonomial<Dim, T, Degree>>
    for crate::ops::MulSym<
        UnarySym<crate::ops::UnaryPowOp<Degree>, DimVariable<Dim>, T, [T; N]>,
        Const<T>,
        T,
        [T; N],
    >
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + num_traits::Pow<Degree, Output = T>
        + Clone
        + Zero
        + Display
        + Any,
    Dim: DimMarker + Any,
    DimVariable<Dim>: Symbol<T, [T; N]>,
    Degree: Sub<Output = Degree> + One + Clone + Default + Any,
{
    fn from(dm: DimMonomial<Dim, T, Degree>) -> Self {
        let dv = DimVariable::with_dimension(dm.2);
        crate::ops::MulSym::new(
            UnarySym::new_with_op(crate::ops::UnaryPowOp(dm.1), dv),
            Const(dm.0),
        )
    }
}

//T = Coefficient
impl<Dim, T, Degree> From<DimMonomial<Dim, T, Degree>>
    for crate::ops::MulSym<
        UnarySym<crate::ops::UnaryPowOp<Degree>, DimVariable<Dim>, T, [T]>,
        Const<T>,
        T,
        [T],
    >
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Pow<Degree, Output = T>
        + Clone
        + Zero
        + Display
        + Any,
    Dim: DimMarker + Any,
    DimVariable<Dim>: Symbol<T, [T]>,
    Degree: Sub<Output = Degree> + One + Clone + Default + Any,
{
    fn from(dm: DimMonomial<Dim, T, Degree>) -> Self {
        let dv = DimVariable::with_dimension(dm.2);
        crate::ops::MulSym::new(
            UnarySym::new_with_op(crate::ops::UnaryPowOp(dm.1), dv),
            Const(dm.0),
        )
    }
}
