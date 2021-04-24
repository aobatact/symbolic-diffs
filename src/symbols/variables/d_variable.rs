use crate::*;
use core::{any::Any, fmt::Display};

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

impl<Dim, Out, In> DynamicSymbol<Out, In> for DimVariable<Dim>
where
    Out: NumOut,
    In: NumsIn<Out> + ?Sized,
    Dim: DimMarker + Any,
{
    fn calc_ref(&self, v: &In) -> Out {
        v.get_variable(self.dim())
    }

    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
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

impl<Dim, Out, In> Symbol<Out, In> for DimVariable<Dim>
where
    Out: NumOut + Any,
    In: NumsIn<Out> + ?Sized,
    Dim: DimMarker + Any,
{
    type Derivative = Const<Out>;

    fn diff(self, dm: usize) -> Self::Derivative {
        if dm == self.0.dim() {
            Const(Out::one())
        } else {
            Const(Out::zero())
        }
    }
}
