//! Set of basic numerical operations
//! These are internaly used from `Expr`.  
use super::*;
use core::ops::{Add, Div, Mul, Sub};

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct AddOp;
impl BinaryOp for AddOp {}
pub type AddSym<Sym1, Sym2, Out, In> = BinarySym<AddOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) + self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(BinarySym::new_with_op(
            AddOp,
            self.sym1.diff_dyn(),
            self.sym2.diff_dyn(),
        ))
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for AddSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = AddSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(self.sym1.diff(), self.sym2.diff())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SubOp;
impl BinaryOp for SubOp {}

pub type SubSym<Sym1, Sym2, Out, In> = BinarySym<SubOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) - self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(BinarySym::new_with_op(
            SubOp,
            self.sym1.diff_dyn(),
            self.sym2.diff_dyn(),
        ))
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for SubSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Sub<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = SubSym<Sym1::Derivative, Sym2::Derivative, Out, In>;
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(self.sym1.diff(), self.sym2.diff())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct MulOp;
impl BinaryOp for MulOp {}

pub type MulSym<Sym1, Sym2, Out, In> = BinarySym<MulOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) * self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        let sym2diff = self.sym2.diff_dyn();
        let df = BinarySym::new_with_op(
            AddOp,
            BinarySym::new_with_op(MulOp, self.sym1.diff_dyn(), self.sym2.clone()),
            BinarySym::new_with_op(MulOp, self.sym1.clone(), sym2diff),
        );
        Arc::new(df)
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for MulSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Mul<Output = Out> + Any,
    In: ?Sized + Any,
{
    type Derivative = AddSym<
        MulSym<Sym1::Derivative, Sym2, Out, In>,
        MulSym<Sym1, Sym2::Derivative, Out, In>,
        Out,
        In,
    >;
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        let sym2diff = self.sym2.clone().diff();
        BinarySym::new(
            BinarySym::new(self.sym1.clone().diff(), self.sym2),
            BinarySym::new(self.sym1, sym2diff),
        )
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct DivOp;
impl BinaryOp for DivOp {}
pub type DivSym<Sym1, Sym2, Out, In> = BinarySym<DivOp, Sym1, Sym2, Out, In>;

impl<Sym1, Sym2, Out, In> DynamicSymbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out> + Any,
    In: ?Sized + Any,
{
    #[inline]
    fn calc_dyn(&self, value: &In) -> Out {
        self.sym1.calc_dyn(value) / self.sym2.calc_dyn(value)
    }
    fn diff_dyn(&self) -> Arc<dyn DynamicSymbol<Out, In>> {
        Arc::new(self.clone().diff())
    }
    fn as_any(&self) -> &(dyn Any) {
        self
    }
}

impl<Sym1, Sym2, Out, In> Symbol<Out, In> for DivSym<Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: Add<Output = Out> + Sub<Output = Out> + Mul<Output = Out> + Div<Output = Out> + Any,
    In: ?Sized + Any,
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
    fn diff(self) -> <Self as Symbol<Out, In>>::Derivative {
        BinarySym::new(
            BinarySym::new(
                BinarySym::new(self.sym1.clone().diff(), self.sym2.clone()),
                BinarySym::new(self.sym1, self.sym2.clone().diff()),
            ),
            BinarySym::new(self.sym2.clone(), self.sym2),
        )
    }
}
