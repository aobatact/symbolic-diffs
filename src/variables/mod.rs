use crate::*;
use core::{any::Any, borrow::Borrow, fmt::Display, ops::Mul};
pub use d_monomial::*;
pub use d_variable::*;
use num_traits::{One, Zero};
use std::sync::Arc;
#[cfg(feature = "typenum")]
use typenum::marker_traits::Unsigned;

mod d_monomial;
mod d_variable;

pub trait DimMarker: Copy {
    fn dim(self) -> usize;
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Dim<const DM: usize>;

impl<const DM: usize> DimMarker for Dim<DM> {
    fn dim(self) -> usize {
        DM
    }
}

#[cfg(feature = "typenum")]
impl<T: Unsigned> DimMarker for T {
    fn dim(self) -> usize {
        T::USIZE
    }
}

/// [`Symbol`](`crate::Symbol`) represent Zero.
/// ```
/// # use symbolic_diffs::*;
/// let x = ZeroSym;
/// assert_eq!(0,x.calc(6));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Const<T>(pub(crate) T);
impl<Out, In> DynamicSymbol<Out, In> for Const<Out>
where
    Out: Any + Zero + Clone + Display,
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
    Out: Zero + Clone + Any + Display,
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

///[`Symbol`](`crate::Symbol`) represents an single variable.
/// Use this when you have only one dimensions.
/// ```
/// # use symbolic_diffs::*;
/// let x = Variable;
/// assert_eq!(6,x.calc(6));
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[cfg(test)]
mod test {

    #[test]
    fn test_dim_variable_ar() {
        use crate::*;
        use typenum::*;
        let v = [2, 3];
        let dm = DimVariable::<U0>::new();

        let x = dm.to_expr();
        assert_eq!(1, x.diff(0).calc(v));
        assert_eq!(0, x.diff(1).calc(v));
        assert_eq!(0, x.diff(0).diff(0).calc(v));
        assert_eq!(0, x.diff(0).diff(1).calc(v));
    }

    #[test]
    fn test_dim_monomial_ar() {
        use crate::*;
        use typenum::*;
        let v = [2, 3];
        let dm = DimMonomial::<U0, i32, u8>::new(2, 2);

        let x = dm.to_expr();
        assert_eq!(8, x.diff(0).calc(v));
        assert_eq!(0, x.diff(1).calc(v));
        assert_eq!(4, x.diff(0).diff(0).calc(v));
        assert_eq!(0, x.diff(0).diff(1).calc(v));
        let y1 = DimMonomial::<U1, i32, u8>::new(2, 2).to_expr();
        let y = x.inner_borrow().change_dim(U1::default()).to_expr();
        assert_eq!(0, y.diff(0).calc(v));
        assert_eq!(12, y.diff(1).calc(v));
        assert_eq!(y, y1);
    }

    #[test]
    #[cfg(feature = "generic-array1")]
    fn test_dim_monomial_ga() {
        use crate::*;
        use generic_array::*;
        use typenum::*;
        let v = arr![i32; 2,3];
        let dm = DimMonomial::<U0, i32, u8>::new(2, 2);

        let x = dm.to_expr();
        assert_eq!(8, x.diff(0).calc(v));
        assert_eq!(0, x.diff(1).calc(v));
        assert_eq!(4, x.diff(0).diff(0).calc(v));
        assert_eq!(0, x.diff(0).diff(1).calc(v));
        let y1 = DimMonomial::<U1, i32, u8>::new(2, 2).to_expr();
        let y = x.inner_borrow().change_dim(U1::default()).to_expr();
        assert_eq!(0, y.diff(0).calc(v));
        assert_eq!(12, y.diff(1).calc(v));
        assert_eq!(y, y1);
    }
}
