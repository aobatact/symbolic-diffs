use crate::*;

pub enum EExpr<Dim: DimMarker, Out, In: ?Sized> {
    Zero(ZeroSym),
    One(OneSym),
    Const(Const<Out>),
    Variable(DimVariable<Dim>),
    //Unary(UnarySym<Op,Sym,Out,In>)
    Dynamic(Arc<dyn DynamicSymbol<Out, In>>),
}
