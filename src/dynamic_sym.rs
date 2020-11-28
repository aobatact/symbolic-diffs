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

#[cfg(test)]
mod tests {
    use crate::dynamic_sym::DynamicSymbol;
    use crate::*;
    use std::sync::Arc;

    #[test]
    fn variable() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(1,x.calc_dyn(&1));
        let y = x + x;
        assert_eq!(2,y.calc_dyn(&1));
        let z = y.diff_dyn(0);
        assert_eq!(0,z.calc_dyn(&1));

        let x = Arc::new(x);
        assert_eq!(1,x.calc_dyn(&1));
        //let y = x + x;
        assert_eq!(2,y.calc_dyn(&1));
        let z = y.diff_dyn(0);
        assert_eq!(0,z.calc_dyn(&1));
    }
}
