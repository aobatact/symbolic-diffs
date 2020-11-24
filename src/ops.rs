use super::*;
use core::ops::{Add, Div, Mul, Neg, Sub};
//use num_traits::Float;

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct AddOp;
impl BinaryOp for AddOp {}

pub type AddSym<Sym1, Sym2, Out, In> = BinarySym<AddOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Clone,
    In: Clone,
{
    type Diff = AddSym<Sym1::Diff, Sym2::Diff, Out, In>;
    fn calc(&self, value: &In) -> Out {
        self.sym1.calc(value) + self.sym2.calc(value)
    }
    fn diff(&self) -> <Self as Symbol<Out, In>>::Diff {
        BinarySym::new(self.sym1.diff(), self.sym2.diff())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct SubOp;
impl BinaryOp for SubOp {}

pub type SubSym<Sym1, Sym2, Out, In> = BinarySym<SubOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + Clone,
    In: Clone,
{
    type Diff = SubSym<Sym1::Diff, Sym2::Diff, Out, In>;
    fn calc(&self, value: &In) -> Out {
        self.sym1.calc(value) - self.sym2.calc(value)
    }
    fn diff(&self) -> <Self as Symbol<Out, In>>::Diff {
        BinarySym::new(self.sym1.diff(), self.sym2.diff())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct MulOp;
impl BinaryOp for MulOp {}
pub type MulSym<Sym1, Sym2, Out, In> = BinarySym<MulOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Clone,
    In: Clone,
{
    type Diff =
        AddSym<MulSym<Sym1::Diff, Sym2, Out, In>, MulSym<Sym1, Sym2::Diff, Out, In>, Out, In>;
    fn calc(&self, value: &In) -> Out {
        self.sym1.calc(value) * self.sym2.calc(value)
    }
    fn diff(&self) -> <Self as Symbol<Out, In>>::Diff {
        BinarySym::new(
            BinarySym::new(self.sym1.diff(), self.sym2.clone()),
            BinarySym::new(self.sym1.clone(), self.sym2.diff()),
        )
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct DivOp;
impl BinaryOp for DivOp {}
pub type DivSym<Sym1, Sym2, Out, In> = BinarySym<DivOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out> + Clone,
    In: Clone,
{
    type Diff = DivSym<
        SubSym<MulSym<Sym1::Diff, Sym2, Out, In>, MulSym<Sym1, Sym2::Diff, Out, In>, Out, In>,
        MulSym<Sym2, Sym2, Out, In>,
        Out,
        In,
    >;
    fn calc(&self, value: &In) -> Out {
        self.sym1.calc(value) / self.sym2.calc(value)
    }
    fn diff(&self) -> <Self as Symbol<Out, In>>::Diff {
        BinarySym::new(
            BinarySym::new(
                BinarySym::new(self.sym1.diff(), self.sym2.clone()),
                BinarySym::new(self.sym1.clone(), self.sym2.diff()),
            ),
            BinarySym::new(self.sym2.clone(), self.sym2.clone()),
        )
    }
}

macro_rules! op_expr {
    ($t:ident,$tsym:ident,$op:ident) => {
        impl<L, R, O, I> $t<Expr<R, O, I>> for Expr<L, O, I>
        where
            L: Symbol<O, I>,
            R: Symbol<O, I>,
        {
            type Output = Expr<$tsym<L, R, O, I>, O, I>;
            fn $op(self, r: Expr<R, O, I>) -> Self::Output {
                BinarySym::new(self.0, r.0).into()
            }
        }
    };
}

op_expr!(Add, AddSym, add);
op_expr!(Sub, SubSym, sub);
op_expr!(Mul, MulSym, mul);
op_expr!(Div, DivSym, div);
