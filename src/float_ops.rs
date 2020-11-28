//! Module for operating float-like type.
//! Op structs defined here is used in [`Expr`](crate::Expr) with Out type impliments [`ExNumOps`]
//!
use crate::*;
use core::ops::{Add, Div, Mul, Neg, Sub};
#[cfg(feature = "num-complex")]
use num_complex::{Complex32, Complex64};
use num_traits::{float::FloatConst, pow::Pow};

macro_rules! ExNumOpsMacro{
    ( trait [$($m:ident),* $(,)*] ) => {
        /// Trait like [`Float`](`num_traits::float::Float`) but also for `Complex`
        pub trait ExNumOps : Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self> +
                                Clone + Zero + Neg<Output = Self> + One + ExNumConsts{
            $(
                fn $m(self) -> Self;
            )*
            fn exp_m1(self) -> Self {
                (self - Self::one()).exp()
            }
            fn exp2(self) -> Self{
                Self::ln_2() * self
            }
            fn ln_1p(self) -> Self{
                (self + Self::one()).ln()
            }
            fn log2(self) -> Self{
                Self::log2_e() * self.ln()
            }
            fn log10(self) -> Self{
                Self::log10_e() * self.ln()
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
        /// Constans need for Operations.
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
        /// Opreations for [`Float`](`num_traits::float::Float`) like type.
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
            fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
            where
                Dm: DiffMarker,
            {
                let df = self.sym.clone().diff(dm).to_expr();
                let y = $ex(self);
                df * y
            }
        }
    };
}

FlaotSymbols!(
    (Recip, recip,  RecipOp, (|x : Self| -(x.sym.to_expr().square()).recip() ));
    (Exp,   exp,    ExpOp,   (|x : Self| x));
    (Sin,   sin,    SinOp,   (|x : Self| x.sym.cos() ));
    (Cos,   cos,    CosOp,   (|x : Self| -(x.sym.sin().to_expr()) ));
    (Tan,   tan,    TanOp,   (|x : Self| x.sym.cos().to_expr().square().recip() ));
    (Sqrt,  sqrt,   SqrtOp,  (|x : Self| (Const(Out::two()).to_expr() * x).recip() ));
    (Ln,    ln,     LnOp,    (|x : Self| x.sym.recip() ));
    (Sinh,  sinh,   SinhOp,  (|x : Self| x.sym.cosh() ));
    (Cosh,  cosh,   CoshOp,  (|x : Self| x.sym.sinh() ));
    (Tanh,  tanh,   TanhOp,  (|x : Self| x.sym.cosh().to_expr().square().recip() ));
    (Asin,  asin,   AsinOp,  (|x : Self| (Const::one().to_expr() - x.sym.to_expr().square().inner()).sqrt().recip() ));
    (Acos,  acos,   AcosOp,  (|x : Self| -(Const::one().to_expr() - x.sym.to_expr().square().inner()).sqrt().recip() ));
    (Atan,  atan,   AtanOp,  (|x : Self| (x.sym.to_expr().square() + Const::one()).recip() ));
    (Asinh, asinh,  AsinhOp, (|x : Self| (x.sym.to_expr().square() + Const::one()).sqrt().recip() ));
    (Acosh, acosh,  AcoshOp, (|x : Self| (x.sym.to_expr().square() - Const::one()).sqrt().recip() ));
    (Atanh, atanh,  AtanhOp, (|x : Self| (Const::one().to_expr() - x.sym.to_expr().square().inner()).recip() ));
    (Ln_1p, ln_1p,  LnOp1p,  (|x : Self| (x.sym.to_expr() + Const::one()).recip() ));
    (Log2,  log2,   Log2,    (|x : Self| (x.sym.to_expr() * Const(Out::ln_2()) ).recip() ));
    (Log10, log10,  Log10,   (|x : Self| (x.sym.to_expr() * Const(Out::ln_10()) ).recip() ));
    (ExpM1, exp_m1, ExpM1Op, (|x : Self| x ));
    (Exp2,  exp2,   Exp2Op,  (|x : Self| Const(Out::ln_2()).to_expr() * x ));
);

impl<Sym, Out, In> UnaryFloatSymbolEx<Out, In> for Sym
where
    Sym: Symbol<Out, In>,
    Out: ExNumOps,
{
}

/// [`BinaryOp`](`crate::BinaryOp`) marker for [`pow`](`num_traits::pow::Pow`)
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct PowOp;
impl BinaryOp for PowOp {}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for BinarySym<PowOp, Sym1, Sym2, Out, In>
where
    Sym1: UnaryFloatSymbolEx<Out, In>,
    Sym2: SymbolEx<Out, In>,
    Out: ExNumOps + Pow<Out, Output = Out>,
{
    type Derivative = impl Symbol<Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value).pow(self.sym2.calc_ref(value))
    }
    fn diff<Dm>(self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        let sym1 = self.sym1.clone();
        let sym2 = self.sym2.clone();
        let s2dif = sym2.clone().diff(dm);
        let a = sym1.clone().diff(dm).to_expr() * sym2 / sym1.clone();
        let b = sym1.ln().to_expr() * s2dif;
        (a + b.inner()) * self
    }
}

impl<L, R, Out, In> Pow<R> for Expr<L, Out, In>
where
    L: UnaryFloatSymbolEx<Out, In>,
    R: Symbol<Out, In>,
    Out: ExNumOps + Pow<Out, Output = Out>,
{
    type Output = Expr<BinarySym<PowOp, L, R, Out, In>, Out, In>;
    fn pow(self, r: R) -> Self::Output {
        BinarySym::new(self.0, r).into()
    }
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
        assert_eq!(2.0_f32.exp() * 2.0, y.clone().diff(U0::new()).calc(v));
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
        assert_eq!(2.0 * xcos.calc(v), xsin.clone().diff(U0::new()).calc(v));
        assert_eq!(2.0 * xcos.calc(v1), xsin.clone().diff(U0::new()).calc(v1));
        assert_eq!(-2.0 * xsin.calc(v), xcos.clone().diff(U0::new()).calc(v));
        assert_eq!(-2.0 * xsin.calc(v1), xcos.diff(U0::new()).calc(v1));
    }
}
