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