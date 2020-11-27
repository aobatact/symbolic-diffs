use crate::*;
use core::ops::{Add, Div, Mul, Neg, Sub};
#[cfg(feature = "num-complex")]
use num_complex::{Complex32, Complex64};
use num_traits::float::FloatConst;

macro_rules! ExNumOpsMacro{
    ( trait [$($m:ident),* $(,)*] ) => {
        pub trait ExNumOps : Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self> +
                                Clone + Zero + Neg<Output = Self> + One + ExNumConsts{
            $(
                fn $m(self) -> Self;
            )*
            fn exp_m1(self) -> Self {
                (self - Self::one()).exp()
            }
            fn exp2(self) -> Self{
                (self * Self::ln_2())
            }
            fn ln_1p(self) -> Self{
                (self + Self::one()).ln()
            }
            fn log2(self) -> Self{
                self.ln() * Self::log2_e()
            }
            fn log10(self) -> Self{
                self.ln() * Self::log10_e()
            }
            fn recip(self) -> Self{
                Self::one() / self
            }
        }
    };
    ( $t:ident; [$($m:ident),* $(,)*]) => {
        impl ExNumOps for $t{
        $(
            fn $m(self) -> Self { self.$m() }
        )*
        }
    };
}

ExNumOpsMacro!(trait [exp, ln, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh,] );
ExNumOpsMacro!(f32;  [exp, ln, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh, recip, exp_m1, exp2, ln_1p, log2, log10,] );
ExNumOpsMacro!(f64;  [exp, ln, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh, recip, exp_m1, exp2, ln_1p, log2, log10,] );
#[cfg(feature = "num-complex")]
ExNumOpsMacro!(Complex32; [exp, ln, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh,] );
#[cfg(feature = "num-complex")]
ExNumOpsMacro!(Complex64; [exp, ln, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh,] );

macro_rules! ExNumConstsMacro {
    (trait [$($constant:ident),+ $(,)*]; [$( $constant_n:ident ),+ $(,)*] ) => {
        pub trait ExNumConsts {
            $(
                fn $constant() -> Self;
            )*
            $(
                fn $constant_n() -> Self;
            )*
        }
    };
    ($t:ty; [$( ($constant:ident, $call:ident) ),+ $(,)*] ; [$( ($constant_n:ident, $const_num:expr) ),+ $(,)*]) => {
        ExNumConstsMacro!($t, $t; [ $(($constant,$call),)* ] ; [ $(($constant_n, $const_num ),)*  ] );
    };
    ($t:ty, $tw:ty ; [$( ($constant:ident, $call:ident) ),+ $(,)*] ; [$( ($constant_n:ident, $const_num:expr) ),+ $(,)*]  ) => {
        impl ExNumConsts for $t{
            $(
                fn $constant() -> Self { <$tw>::$call().into() }
            )*
            $(
                fn $constant_n() -> Self { $const_num.into() }
            )*
        }
    };
}

ExNumConstsMacro!(trait [e, ln_10, ln_2, log10_e, log10_2, log2_10, log2_e,]; [two,]);
ExNumConstsMacro!(f32;  [(e, E), (ln_10, LN_10), (ln_2, LN_2), (log10_e, LOG10_E), (log10_2, LOG10_2), (log2_10, LOG2_10), (log2_e, LOG2_E),]; [(two, 2.0_f32)]);
ExNumConstsMacro!(f64;  [(e, E), (ln_10, LN_10), (ln_2, LN_2), (log10_e, LOG10_E), (log10_2, LOG10_2), (log2_10, LOG2_10), (log2_e, LOG2_E),]; [(two, 2.0_f64)]);

#[cfg(feature = "num-complex")]
ExNumConstsMacro!(Complex32, f32;  [(e, E), (ln_10, LN_10), (ln_2, LN_2), (log10_e, LOG10_E), (log10_2, LOG10_2), (log2_10, LOG2_10), (log2_e, LOG2_E),]; [(two, 2.0_f32)]);
#[cfg(feature = "num-complex")]
ExNumConstsMacro!(Complex64, f64;  [(e, E), (ln_10, LN_10), (ln_2, LN_2), (log10_e, LOG10_E), (log10_2, LOG10_2), (log2_10, LOG2_10), (log2_e, LOG2_E),]; [(two, 2.0_f64)]);

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
                  Out: ExNumOps + ExNumConsts,
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
                + ExNumConsts
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
    (Sqrt,  sqrt,   SqrtOp,  (|x : &Self| (Const(Out::two()).to_expr() * x.clone()).recip() ));
    (Ln,    ln,     LnOp,    (|x : &Self| (x.sym.clone()).recip() ));
    (Ln_1p, ln_1p,  LnOp1p,  (|x : &Self| (x.sym.clone().to_expr() + Const::one()).recip() ));
    (Log2,  log2,   Log2,    (|x : &Self| (x.sym.clone().to_expr() * Const(Out::ln_2()) ).recip() ));
    (Sinh,  sinh,   SinhOp,  (|x : &Self| (x.sym.clone().cosh()) ));
    (Cosh,  cosh,   CoshOp,  (|x : &Self| (x.sym.clone().sinh()) ));
    (Tanh,  tanh,   TanhOp,  (|x : &Self| { let y = x.sym.clone().cosh(); (y.clone().to_expr()*y).recip()} ));
    (Asin,  asin,   AsinOp,  (|x : &Self| (Const::one().to_expr() - (x.sym.clone().to_expr() * x.sym.clone()).inner()).sqrt().recip() ));
    (Acos,  acos,   AcosOp,  (|x : &Self| -(Const::one().to_expr() - (x.sym.clone().to_expr() * x.sym.clone()).inner()).sqrt().recip() ));
    (Atan,  atan,   AtanOp,  (|x : &Self| ((x.sym.clone().to_expr() * x.sym.clone()) + Const::one()).recip() ));
    (Asinh, asinh,  AsinhOp, (|x : &Self| ((x.sym.clone().to_expr() * x.sym.clone()) + Const::one()).sqrt().recip() ));
    (Acosh, acosh,  AcoshOp, (|x : &Self| ((x.sym.clone().to_expr() * x.sym.clone()) - Const::one()).sqrt().recip() ));
    (Atanh, atanh,  AtanhOp, (|x : &Self| (Const::one().to_expr() - (x.sym.clone().to_expr() * x.sym.clone()).inner()).recip() ));
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

    #[test]
    fn sincos() {
        let v = arr![f32; 1., 1.];
        let v1 = arr![f32; 2., 3.];
        let x = DimMonomial::<U0, f32, u8>::new(2.0, 1).to_expr();
        let xsin = x.sin();
        let xcos = x.cos();
        assert_eq!(2.0_f32.sin(), xsin.calc(v));
        assert_eq!(4.0_f32.sin(), xsin.calc(v1));
        assert_eq!(2.0_f32.cos(), xcos.calc(v));
        assert_eq!(4.0_f32.cos(), xcos.calc(v1));
        assert_eq!(2.0 * xcos.calc(v), xsin.diff(U0::new()).calc(v));
        assert_eq!(2.0 * xcos.calc(v1), xsin.diff(U0::new()).calc(v1));
        assert_eq!(-2.0 * xsin.calc(v), xcos.diff(U0::new()).calc(v));
        assert_eq!(-2.0 * xsin.calc(v1), xcos.diff(U0::new()).calc(v1));
    }
}
