use crate::ops::AddSym;
use crate::ops::AddOp;
use crate::*;
use core::any::Any;
use core::ops::Add;
use std::sync::Arc;

/*
//needs specialization
impl<Out, In> Add<Arc<dyn DynamicSymbol<Out, In>>> for Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>
    where Out : Clone + Any + Send + Sync + Add<Out, Output = Out>,In : ?Sized  + Any + Send + Sync,
{
    type Output = Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In>;
    fn add(self, other : Arc<dyn DynamicSymbol<Out, In>>) -> Expr<Arc<dyn DynamicSymbol<Out, In>>, Out, In> {
        let l = self.0.as_ref().as_any();
        if l.downcast_ref::<ZeroSym>().is_some() {
            other.to_expr()
        } else if other.as_ref().as_any().downcast_ref::<ZeroSym>().is_some() {
            self
        } else {
            Expr::new(Arc::new(AddSym::new(self.0,other)))
        }
    }
}
*/

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
