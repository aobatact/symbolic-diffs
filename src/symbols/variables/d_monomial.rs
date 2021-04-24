use crate::symbols::*;
use crate::*;
use core::{
    any::Any,
    fmt::Display,
    ops::{Add, Mul, Sub},
};
use num_traits::{One, Pow, Zero};

///[`Symbol`](`crate::Symbol`) represents an monomial with coefficient and degree in mulit variable context.
/// ```
/// # use symbolic_diffs::*;
/// # use typenum::*;
/// let v = [2_i32, 3];
/// let x = DimMonomial::<U0,i32,u8>::new(2,2);
/// assert_eq!(8,x.calc_ref(&v));
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

impl<Dim: DimMarker, Coefficient: Display + From<Degree>, Degree: Clone> Display
    for DimMonomial<Dim, Coefficient, Degree>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_fmt(format_args!(
            "{} x_{}^{}",
            self.0,
            self.dim(),
            Coefficient::from(self.1.clone())
        ))
    }
}

impl<Dim, T, Degree, In> DynamicSymbol<T, In> for DimMonomial<Dim, T, Degree>
where
    T: NumOut + Mul<Output = T> + Pow<Degree, Output = T> + From<Degree> + Any,
    Dim: DimMarker + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
    In: NumsIn<T> + ?Sized,
{
    fn calc_ref(&self, v: &In) -> T {
        if !self.0.is_zero() {
            self.0.clone() * v.get_variable(self.dim()).clone().pow(self.1.clone())
        } else {
            T::zero()
        }
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<T, In> {
        if dm == self.dim() {
            if self.1.is_one() {
                return DynExpr::Const(Const(self.0.clone() * T::from(self.1.clone())));
            } else if !self.1.is_zero() {
                return DimMonomial::<Dim, _, _>(
                    self.0.clone() * T::from(self.1.clone()),
                    self.1.clone() - Degree::one(),
                    self.2,
                )
                .to_dyn_expr();
            }
        }
        DynExpr::Zero
    }

    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Dim, T, Degree, In> Symbol<T, In> for DimMonomial<Dim, T, Degree>
where
    T: NumOut + Mul<Output = T> + Pow<Degree, Output = T> + From<Degree> + Any,
    Dim: DimMarker + Any,
    Degree: Clone + Sub<Output = Degree> + Zero + One + PartialEq + Any,
    In: NumsIn<T> + ?Sized,
{
    type Derivative = DimMonomial<Dim, T, Degree>;

    fn diff(self, dm: usize) -> Self::Derivative {
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
impl<Dim, T, Degree, In> From<DimMonomial<Dim, T, Degree>>
    for crate::ops::MulSym<
        UnarySym<crate::ops::UnaryPowOp<Degree>, DimVariable<Dim>, T, In>,
        Const<T>,
        T,
        In,
    >
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + num_traits::Pow<Degree, Output = T>
        + NumOut
        + Any,
    Dim: DimMarker + Any,
    DimVariable<Dim>: Symbol<T, In>,
    Degree: Sub<Output = Degree> + One + Clone + Default + Any,
    In: NumsIn<T> + ?Sized + Any,
{
    fn from(dm: DimMonomial<Dim, T, Degree>) -> Self {
        let dv = DimVariable::with_dimension(dm.2);
        crate::ops::MulSym::new(
            UnarySym::new_with_op(crate::ops::UnaryPowOp(dm.1), dv),
            Const(dm.0),
        )
    }
}
