use crate::*;
use core::any::Any;
use core::fmt::Display;

pub struct DimConverter<Sym, D1, D2>(pub Sym, pub D1, pub D2);

impl<Sym: Clone, D1: Clone, D2: Clone> Clone for DimConverter<Sym, D1, D2> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

impl<Sym: Display, D1, D2> Display for DimConverter<Sym, D1, D2> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        self.0.fmt(fmt)
    }
}

impl<Sym, D1, D2, Out> DynamicSymbol<Out, [Out]> for DimConverter<Sym, D1, D2>
where
    Sym: DynamicSymbol<Out, [Out]> + Any,
    D1: DimMarker + Clone + Any,
    D2: DimMarker + Clone + Any,
    Out: DynamicOut + Any,
{
    fn calc_ref(&self, i: &[Out]) -> Out {
        let mut ni = i.to_vec();
        ni.swap(self.1.dim(), self.2.dim());
        self.0.calc_ref(&ni)
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, [Out]> {
        let d1 = self.1.dim();
        let d2 = self.2.dim();
        let d = if dm == d1 {
            d2
        } else if dm == d2 {
            d1
        } else {
            dm
        };
        self.0.diff_dyn(d)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym, D1, D2, Out> Symbol<Out, [Out]> for DimConverter<Sym, D1, D2>
where
    Sym: Symbol<Out, [Out]> + Any,
    D1: DimMarker + Clone + Any,
    D2: DimMarker + Clone + Any,
    Out: DynamicOut + Any,
{
    type Derivative = DimConverter<Sym::Derivative, D1, D2>;
    fn diff(self, dm: usize) -> Self::Derivative {
        let d1 = self.1.dim();
        let d2 = self.2.dim();
        let d = if dm == d1 {
            d2
        } else if dm == d2 {
            d1
        } else {
            dm
        };
        DimConverter(self.0.diff(d), self.1, self.2)
    }
}

#[cfg(test)]
mod test {
    use crate::variables::dim_convert::DimConverter;
    use crate::*;
    #[test]

    fn convert() {
        let x = DimMonomial::<Dim<0>, i32, u8>::new(2, 2).to_expr();
        let y = DimConverter(
            DimMonomial::<Dim<0>, i32, u8>::new(3, 1),
            Dim::<1>,
            Dim::<0>,
        );

        let v = &[1, 1];
        let v1 = &[2, 3];
        assert_eq!(3, y.calc_ref(v));
        let xy = x + y;
        assert_eq!(5, xy.calc_ref(v));
        assert_eq!(4, xy.clone().diff(0).calc_ref(v));
        assert_eq!(3, xy.clone().diff(1).calc_ref(v));
        assert_eq!(17, xy.calc_ref(v1));
        assert_eq!(8, xy.clone().diff(0).calc_ref(v1));
        assert_eq!(3, xy.diff(1).calc_ref(v1));
    }
}
