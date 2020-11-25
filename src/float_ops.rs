use crate::*;
use crate::ops::*;
use num_traits::{float::Float};
use core::ops::{Add, Div, Mul, Neg, Sub}; 


/// [`UnaryOp`](`crate::UnaryOp`) marker for [`exp`](`num_traits::float::Float::exp`) with [`ExpSym`](`crate::float_ops::ExpSym`) for float
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct ExpOp;
impl UnaryOp for ExpOp {}
/// Represent Unary[`exp`](`num_traits::float::Float::exp`) Symbol for float
/// ```
/// # use symbolic_diffs::*;
/// # use symbolic_diffs::float_ops::*;
/// # use typenum::*;
/// # use generic_array::*;
/// let x = DimMonomial::<U0,f32,u8>::new(2.0,1).to_expr();
/// let y = x.exp();
/// let v = arr![f32; 1., 1.];
/// let v1 = arr![f32; 2., 3.];
/// assert_eq!(2.0_f32.exp(),y.calc(v));
/// assert_eq!(4.0_f32.exp(),y.calc(v1));
/// ```
pub type ExpSym<Sym, Out, In> = UnarySym<ExpOp, Sym, Out, In>;

impl<Sym, Out, In> Symbol<Out, In> for ExpSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Float,
{
    type Derivative = MulSym<Sym::Derivative, ExpSym<Sym, Out, In>,Out,In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym.calc_ref(value).exp()
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        (self.sym.diff(dm).to_expr() * self.clone()).0
    }
}

pub trait FloatSymbolEx<Out,In> : Symbol<Out,In> where Out : Float {
    fn exp(&self) -> ExpSym<Self,Out,In> {
        self.clone().into()
    }
}

impl<Sym, Out,In> FloatSymbolEx<Out,In> for Sym where Sym : Symbol<Out,In>, Out : Float{
}
