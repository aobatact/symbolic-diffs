use crate::ops::*;
use crate::*;
use num_traits::float::Float;

macro_rules! FlaotSymbols {
    ( $( ($t:ident,$me:ident,$op:ident,$ex:tt); )* $(;)*  ) => {
        $(
            FloatOps!($t,$me,$op,$ex);
        )*
        pub trait UnaryFloatSymbolEx<Out, In>: Symbol<Out, In>
        where
            Out: Float,
        {
            $(
                fn $me(self) -> UnarySym<$op, Self, Out, In> {
                    self.into()
                }
            )*
        }
        impl<Sym, Out, In> Expr<Sym, Out, In>
            where Sym: Symbol<Out,In>,
                  Out: Float,
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
    (Sin,sin, SinOp, (|x : &Self| x.sym.clone().cos() ) );
    (Cos,cos, CosOp, (|x : &Self| -(x.sym.clone().sin().to_expr()) ) );
    (Tan,tan, TanOp, (|x : &Self| { let cos = x.sym.clone().cos(); Const(Out::one()).to_expr() / (cos.clone().to_expr() * cos).inner() } ));
);

impl<Sym, Out, In> UnaryFloatSymbolEx<Out, In> for Sym
where
    Sym: Symbol<Out, In>,
    Out: Float,
{
}

#[cfg(test)]
mod tests {
    use crate::float_ops::*;
    use crate::*;
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
