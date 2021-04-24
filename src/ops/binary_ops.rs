use crate::ops::*;
use crate::symbols::enum_based::EExpr;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BinaryOpSet {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

impl BinaryOp for BinaryOpSet {}

impl<Sym1, Sym2, Out, In: ?Sized> DynamicSymbol<Out, In>
    for BinarySym<BinaryOpSet, Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: BasicNumOps + Any,
    In: Any + NumsIn<Out>,
{
    fn calc_ref(&self, i: &In) -> Out {
        match &self.op {
            BinaryOpSet::Add => {
                BinarySym::new_with_op(AddOp, self.sym1.clone(), self.sym2.clone()).calc_ref(i)
            }
            BinaryOpSet::Sub => {
                BinarySym::new_with_op(SubOp, self.sym1.clone(), self.sym2.clone()).calc_ref(i)
            }
            BinaryOpSet::Mul => {
                BinarySym::new_with_op(MulOp, self.sym1.clone(), self.sym2.clone()).calc_ref(i)
            }
            BinaryOpSet::Div => {
                BinarySym::new_with_op(DivOp, self.sym1.clone(), self.sym2.clone()).calc_ref(i)
            }
            _ => todo!(),
        }
    }
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In> {
        todo!()
    }
    fn as_any(&self) -> &(dyn Any) {
        todo!()
    }
}

impl<Sym1, Sym2, Out, In: ?Sized> Symbol<Out, In> for BinarySym<BinaryOpSet, Sym1, Sym2, Out, In>
where
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
    Out: BasicNumOps + Any,
    In: Any + NumsIn<Out>,
    EExpr<Out, In>: Symbol<Out, In>,
{
    type Derivative = EExpr<Out, In>;
    fn diff(self, _: usize) -> <Self as Symbol<Out, In>>::Derivative {
        todo!()
    }
}
