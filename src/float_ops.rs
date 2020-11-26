use crate::*;
use core::ops::{Add, Div, Mul, Neg, Sub};
use num_traits::FromPrimitive;

macro_rules! ExNumOpsMacro{
    /*
    ( trait + $($t:ident );* $(;)* [$ms:tt] ) => {
        ExNumOpsMacro!(trait [$ms]);
        $(
            ExNumOpsMacro!($t; [$ms]);
        )*
    };
    */
    ( trait [$($m:ident),* $(,)*] ) => {
        pub trait ExNumOps : Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self> +
                                Clone + Zero + Neg<Output = Self> + One + FromPrimitive{
            $(
                fn $m(self) -> Self;
            )*
        }
    };
    ( $t:ident; [$($m:ident),* $(,)*]) => {
        impl ExNumOps for $t{
        $(
            fn $m(self) -> Self { self.$m() }
        )*
        }
    }
}

ExNumOpsMacro!(trait [recip, exp, ln, log2, log10, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh] );
ExNumOpsMacro!(f32;  [recip, exp, ln, log2, log10, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh] );
ExNumOpsMacro!(f64;  [recip, exp, ln, log2, log10, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh] );

macro_rules! FlaotSymbols {
    ( $( ($t:ident,$me:ident,$op:ident,$ex:tt); )* $(;)*  ) => {
        $(
            FloatOps!($t,$me,$op,$ex);
        )*
        pub trait UnaryFloatSymbolEx<Out, In>: Symbol<Out, In>
        where
            Out: ExNumOps,
        {
            $(
                fn $me(self) -> UnarySym<$op, Self, Out, In> {
                    self.into()
                }
            )*
        }
        impl<Sym, Out, In> Expr<Sym, Out, In>
            where Sym: Symbol<Out,In>,
                  Out: ExNumOps,
        {
            $(
                pub fn $me(self) -> Expr<UnarySym<$op, Sym, Out, In>,Out,In> {
                    //let x : UnarySym<$op, Sym, Out, In> = self.inner().into();
                    //x.to_expr()
                    self.inner().$me().to_expr()
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
            Out: ExNumOps
                + Add<Output = Out>
                + Sub<Output = Out>
                + Mul<Output = Out>
                + Div<Output = Out>,
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
    (Recip, recip,  RecipOp, (|x : &Self| -(x.sym.clone().to_expr() * x.sym.clone()).recip() ));
    (Exp,   exp,    ExpOp,   (|x : &Self| x.clone() ));
    (Sin,   sin,    SinOp,   (|x : &Self| x.sym.clone().cos() ));
    (Cos,   cos,    CosOp,   (|x : &Self| -(x.sym.clone().sin().to_expr()) ));
    (Tan,   tan,    TanOp,   (|x : &Self| { let cos = x.sym.clone().cos(); (cos.clone().to_expr() * cos).recip() } ));
    (Sqrt,  sqrt,   SqrtOp,  (|x : &Self| (Const(Out::from_i32(2).unwrap()).to_expr() * x.clone()).recip() ));
    (Ln,    ln,     LnOp,    (|x : &Self| (x.sym.clone()).recip() ));
    (Sinh,  sinh,   SinhOp,  (|x : &Self| (x.sym.clone().cosh()) ));
    (Cosh,  cosh,   CoshOp,  (|x : &Self| (x.sym.clone().sinh()) ));
    (Tanh,  tanh,   TanhOp,  (|x : &Self| { let y = x.sym.clone().cosh(); (y.clone().to_expr()*y).recip()} ));
    (Asin,  asin,   AsinOp,  (|x : &Self| (Const(Out::one()).to_expr() - (x.sym.clone().to_expr() * x.sym.clone()).inner()).sqrt().recip() ));
    (Acos,  acos,   AcosOp,  (|x : &Self| -(Const(Out::one()).to_expr() - (x.sym.clone().to_expr() * x.sym.clone()).inner()).sqrt().recip() ));
    (Atan,  atan,   AtanOp,  (|x : &Self| ((x.sym.clone().to_expr() * x.sym.clone()) + Const(Out::one())).recip() ));
    (Asinh, asinh,  AsinhOp, (|x : &Self| ((x.sym.clone().to_expr() * x.sym.clone()) + Const(Out::one())).sqrt().recip() ));
    (Acosh, acosh,  AcoshOp, (|x : &Self| ((x.sym.clone().to_expr() * x.sym.clone()) - Const(Out::one())).sqrt().recip() ));
    (Atanh, atanh,  AtanhOp, (|x : &Self| (Const(Out::one()).to_expr() - (x.sym.clone().to_expr() * x.sym.clone()).inner()).recip() ));
);

impl<Sym, Out, In> UnaryFloatSymbolEx<Out, In> for Sym
where
    Sym: Symbol<Out, In>,
    Out: ExNumOps,
{
}

#[cfg(test)]
mod tests {
    use crate::float_ops::*;
    //use crate::*;
    use generic_array::*;
    use typenum::*;

    #[test]
    fn exp() {
        let x = DimMonomial::<U0, f32, u8>::new(2.0, 1).to_expr();
        let y = x.exp();
        let v = arr![f32; 1., 1.];
        let v1 = arr![f32; 2., 3.];
        assert_eq!(2.0_f32.exp(), y.calc(v));
        assert_eq!(4.0_f32.exp(), y.calc(v1));
        assert_eq!(2.0_f32.exp() * 2.0, y.diff(U0::new()).calc(v));
        assert_eq!(4.0_f32.exp() * 2.0, y.diff(U0::new()).calc(v1));
    }
}
