use super::*;
use core::ops::{Add, Div, Mul, Sub}; //Neg
                                     //use num_traits::Float;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct AddOp;
impl BinaryOp for AddOp {}

pub type AddSym<Sym1, Sym2, Out, In> = BinarySym<AddOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out>,
{
    type Derivative = AddSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) + self.sym2.calc_ref(value)
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SubOp;
impl BinaryOp for SubOp {}

pub type SubSym<Sym1, Sym2, Out, In> = BinarySym<SubOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out>,
{
    type Derivative = SubSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) - self.sym2.calc_ref(value)
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        BinarySym::new(self.sym1.diff(dm), self.sym2.diff(dm))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct MulOp;
impl BinaryOp for MulOp {}
pub type MulSym<Sym1, Sym2, Out, In> = BinarySym<MulOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out>,
{
    type Derivative = AddSym<
        MulSym<Sym1::Derivative, Sym2, Out, In>,
        MulSym<Sym1, Sym2::Derivative, Out, In>,
        Out,
        In,
    >;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) * self.sym2.calc_ref(value)
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        BinarySym::new(
            BinarySym::new(self.sym1.diff(dm), self.sym2.clone()),
            BinarySym::new(self.sym1.clone(), self.sym2.diff(dm)),
        )
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct DivOp;
impl BinaryOp for DivOp {}
pub type DivSym<Sym1, Sym2, Out, In> = BinarySym<DivOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out>,
{
    type Derivative = DivSym<
        SubSym<
            MulSym<Sym1::Derivative, Sym2, Out, In>,
            MulSym<Sym1, Sym2::Derivative, Out, In>,
            Out,
            In,
        >,
        MulSym<Sym2, Sym2, Out, In>,
        Out,
        In,
    >;
    fn calc_ref(&self, value: &In) -> Out {
        self.sym1.calc_ref(value) / self.sym2.calc_ref(value)
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Derivative
    where
        Dm: DiffMarker,
    {
        BinarySym::new(
            BinarySym::new(
                BinarySym::new(self.sym1.diff(dm), self.sym2.clone()),
                BinarySym::new(self.sym1.clone(), self.sym2.diff(dm)),
            ),
            BinarySym::new(self.sym2.clone(), self.sym2.clone()),
        )
    }
}

macro_rules! op_expr {
    ($t:ident,$tsym:ident,$op:ident) => {
        impl<L, R, O, I> $t<R> for Expr<L, O, I>
        where
            L: Symbol<O, I>,
            R: Symbol<O, I>,
            O: Add<Output = O> + Sub<Output = O> + Mul<Output = O> + Div<Output = O>,
        {
            type Output = Expr<$tsym<L, R, O, I>, O, I>;
            fn $op(self, r: R) -> Self::Output {
                BinarySym::new(self.0, r).into()
            }
        }
    };
}

op_expr!(Add, AddSym, add);
op_expr!(Sub, SubSym, sub);
op_expr!(Mul, MulSym, mul);
op_expr!(Div, DivSym, div);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn add() {
        let x: Expr<Variable, isize> = Variable.into();
        assert_eq!(2, x.calc(2));
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
