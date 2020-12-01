use crate::*;
use std::sync::Arc;

pub trait DynamicSymbol<Out, In: ?Sized> {
    fn calc_dyn(&self, value: &In) -> Out;
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>>;
}

impl<Sym, Out: 'static, In: 'static> DynamicSymbol<Out, In> for Sym
where
    Sym: Symbol<Out, In> + 'static,
{
    fn calc_dyn(&self, value: &In) -> Out {
        self.calc_ref(value)
    }
    fn diff_dyn(&self, dm: usize) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(self.clone().diff(dm))
    }
}

impl<Out, In: ?Sized> Symbol<Out, In> for Arc<dyn DynamicSymbol<Out, In>> {
    type Derivative = Arc<dyn DynamicSymbol<Out, In>>;
    fn calc_ref(&self, value: &In) -> Out {
        self.as_ref().calc_dyn(value)
    }
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.as_ref().diff_dyn(dm)
    }
}

#[cfg(test)]
mod tests {
    use crate::dynamic::*;
    //use crate::float_ops::*;
    //use crate::*;
    use generic_array::*;
    use std::sync::Arc;
    use typenum::*;

    #[test]
    fn variable() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(1, x.calc_dyn(&1));
        let y = x + x;
        assert_eq!(2, y.calc_dyn(&1));
        let z = y.diff_dyn(0);
        assert_eq!(2, z.calc_dyn(&2));

        let x: Expr<Variable, f32> = Variable.into();
        let w = Arc::new(x);
        assert_eq!(1., x.calc_dyn(&1.));
        let w = (w as Arc<dyn DynamicSymbol<f32, f32>>).to_expr();
        assert_eq!(1., x.calc_dyn(&1.));
        let y = w.clone() + w.clone();
        assert_eq!(2., y.calc_dyn(&1.));
        let y = w.clone() + x;
        assert_eq!(2., y.calc_dyn(&1.));
        let y = x + w.clone();
        assert_eq!(2., y.calc_dyn(&1.));
        let z = y.diff_dyn(0);
        assert_eq!(2., z.calc_dyn(&1.));

        let wexp = w.exp();
        assert_eq!(1_f32.exp(), wexp.calc_dyn(&1.));
        assert_eq!(1_f32.exp(), wexp.calc_ref(&1.));
        assert_eq!(1_f32.exp(), wexp.diff(0).calc_ref(&1.));
    }

    #[test]
    fn monomial() {
        let x = DimMonomial::<U0, f32, u8>::new(2., 3).to_expr();
        let v = arr![f32; 2.0];
        assert_eq!(16., x.calc_dyn(&v));
        let y = x + x;
        assert_eq!(32., y.calc_dyn(&v));
        let z = y.diff_dyn(0);
        assert_eq!(48., z.calc_dyn(&v));

        let a = z.to_expr() + x;
        assert_eq!(64., a.calc_dyn(&v));
        assert_eq!(64., a.calc_ref(&v));
    }
}
