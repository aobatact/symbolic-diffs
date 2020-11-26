use crate::ops::*;
use crate::*;
use core::ops::{Add, Div, Mul, Neg, Sub};
use num_traits::float::Float;

/*
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
/// assert_eq!(2.0_f32.exp()*2.0,y.diff(U0::new()).calc(v));
/// assert_eq!(4.0_f32.exp()*2.0,y.diff(U0::new()).calc(v1));
/// ```
pub type ExpSym<Sym, Out, In> = UnarySym<ExpOp, Sym, Out, In>;

impl<Sym, Out, In> Symbol<Out, In> for ExpSym<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: Float,
{
    type Derivative = impl Symbol<Out, In>; // MulSym<Sym::Derivative, ExpSym<Sym, Out, In>,Out,In>;
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
*/

macro_rules! FlaotSymbols {
    ( $( ($t:ident,$me:ident,$op:ident,$ex:tt); )* $(;)*  ) => {
        $(
            FloatOps!($t,$me,$op,$ex);
        )*
        pub trait UnaryFloatSymbolEx<Out, In>: Symbol<Out, In>
        where
            Out: Float,
        {
            /*
            fn exp(self) -> ExpSym<Self, Out, In> {
                self.into()
            }
            */
            $(
                fn $me(self) -> UnarySym<$op, Self, Out, In> {
                    self.into()
                }
            )*
        }
    };
}

macro_rules! FloatOps {
    ($t:ident,$me:ident,$op:ident,$ex:tt) => {
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
        pub struct $op;
        impl UnaryOp for $op {}
        impl<Sym, Out, In> Symbol<Out, In> for UnarySym<$op, Sym, Out, In>
        where 
            Sym: Symbol<Out, In>,
            In: Clone,
            Out: Float,
        {
            type Derivative = impl Symbol<Out, In>;
            fn calc_ref(&self, v: &In) -> Out {
                let inner = self.sym.calc_ref(v);
                inner.$me()
            }
            fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
            where
                Dm: DiffMarker,
            {
                let df = self.sym.diff(dm).to_expr();
                let y = $ex(&self);
                df * y
            }
        }
    };
}

FlaotSymbols!(
    (Exp,exp, ExpOp, (|x : &Self| x.clone()) );
    (Sin,sin, SinOp, (|x : &Self| x.sym.clone().cos()) );
    (Cos,cos, CosOp, (|x : &Self| -(x.sym.clone().sin().to_expr())) );
    (Tan,tan, TanOp, (|x : &Self| { let cos = x.sym.clone().cos(); Const(Out::one()).to_expr() / (cos.clone().to_expr() * cos).inner() } ));
);

//FloatOps!(Sin,sin, SinOp, (|x : Sym| x.cos()) );

/*
pub trait FloatSymbolEx<Out, In>: Symbol<Out, In>
where
    Out: Float,
{
    fn exp(self) -> ExpSym<Self, Out, In> {
        self.into()
    }
    fn sin(self) -> UnarySym<SinOp, Self, Out, In> {
        self.into()
    }
    fn cos(self) -> UnarySym<CosOp, Self, Out, In> {
        self.into()
    }
}
*/

impl<Sym, Out, In> UnaryFloatSymbolEx<Out, In> for Sym
where
    Sym: Symbol<Out, In>,
    Out: Float,
{
}

#[cfg(test)]
mod tests {
    use crate::*;
    use crate::float_ops::*;
    use typenum::*;
    use generic_array::*;

    #[test]
    fn exp() {
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