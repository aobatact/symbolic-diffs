use crate::ops::*;
use crate::*;

pub enum EExpr<Out, In: ?Sized = Out> {
    Zero,
    One,
    Const(Out),
    Variable(usize),
    Unary(UnarySym<UnaryOpSet, Box<EExpr<Out, In>>, Out, In>),
    Binary(BinarySym<BinaryOpSet, Box<EExpr<Out, In>>, Box<EExpr<Out, In>>, Out, In>),
    Dyn(DynExpr<Out, In>),
}

impl<Out, In: ?Sized> Clone for EExpr<Out, In> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<Out, In: ?Sized> Display for EExpr<Out, In> {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}

impl<T> DynamicSymbol<T> for EExpr<T>
where
    T: BasicNumOps + Any,
{
    fn calc_ref(&self, i: &T) -> T {
        match self {
            EExpr::Zero => T::zero(),
            EExpr::One => T::one(),
            EExpr::Const(c) => c.clone(),
            EExpr::Variable(d) => {
                debug_assert_eq!(*d, 0);
                i.clone()
            }
            EExpr::Unary(u) => u.calc_ref(i),
            EExpr::Binary(b) => b.calc_ref(i),
            EExpr::Dyn(d) => d.calc_ref(i),
        }
    }
    fn diff_dyn(&self, dim: usize) -> DynExpr<T, T> {
        match self {
            EExpr::Zero | EExpr::One | EExpr::Const(_) => DynExpr::zero(),
            EExpr::Variable(d) => {
                debug_assert_eq!(dim, 0);
                DynExpr::Zero
            }
            EExpr::Unary(u) => u.diff_dyn(dim),
            EExpr::Binary(b) => b.diff_dyn(dim),
            EExpr::Dyn(d) => d.diff_dyn(dim),
        }
    }
    fn as_any(&self) -> &(dyn std::any::Any) {
        self
    }
}

impl<T> Symbol<T, T> for EExpr<T>
where
    T: BasicNumOps + Any,
{
    type Derivative = EExpr<T>;
    fn diff(self, _: usize) -> EExpr<T> {
        todo!()
    }
}

impl<Out, In, S> DynamicSymbol<Out, In> for Box<S>
where
    Out: DynamicOut + Any,
    In: Any + ?Sized,
    S: DynamicSymbol<Out, In>,
{
    fn calc_ref(&self, i: &In) -> Out {
        self.as_ref().calc_ref(i)
    }
    fn diff_dyn(&self, dm: usize) -> symbols::dyn_expr::DynExpr<Out, In> {
        self.as_ref().diff_dyn(dm)
    }
    fn as_any(&self) -> &(dyn std::any::Any + 'static) {
        self.as_ref().as_any()
    }
}

impl<Out, In, S> Symbol<Out, In> for Box<S>
where
    Out: DynamicOut + Any,
    In: Any + ?Sized,
    S: Symbol<Out, In>,
{
    type Derivative = Box<S::Derivative>;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        Box::new((*self).diff(dm))
    }
}

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
    In: Any,
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
    In: Any,
    EExpr<Out, In>: Symbol<Out, In>,
{
    type Derivative = EExpr<Out, In>;
    fn diff(self, _: usize) -> <Self as Symbol<Out, In>>::Derivative {
        todo!()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum UnaryOpSet {
    Neg,
    Square,
    FloatOp(FloatOpSet),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FloatOpSet {}

impl UnaryOp for UnaryOpSet {
    fn op_name<'a>(&self) -> &'a str {
        match self {
            UnaryOpSet::Neg => NegOp.op_name(),
            UnaryOpSet::Square => SquareOp.op_name(),
            _ => unimplemented!(),
        }
    }

    ///Formats the expression to display.
    fn format_expression<Out, In: ?Sized>(
        &self,
        f: &mut fmt::Formatter<'_>,
        inner: &impl DynamicSymbol<Out, In>,
    ) -> Result<(), fmt::Error> {
        match self {
            UnaryOpSet::Neg => NegOp.format_expression(f, inner),
            UnaryOpSet::Square => SquareOp.format_expression(f, inner),
            _ => unimplemented!(),
        }
    }
}

impl<Sym, Out, In: ?Sized> DynamicSymbol<Out, In> for UnarySym<UnaryOpSet, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: BasicNumOps + Any,
    In: Any,
{
    fn calc_ref(&self, i: &In) -> Out {
        match &self.op {
            UnaryOpSet::Neg => UnarySym::new_with_op(NegOp, self.sym.clone()).calc_ref(i),
            UnaryOpSet::Square => UnarySym::new_with_op(SquareOp, self.sym.clone()).calc_ref(i),
            UnaryOpSet::FloatOp(fop) => todo!(),
        }
    }
    fn diff_dyn(&self, dm: usize) -> symbols::dyn_expr::DynExpr<Out, In> {
        todo!()
    }
    fn as_any(&self) -> &(dyn std::any::Any) {
        todo!()
    }
}

impl<Sym, Out, In: ?Sized> Symbol<Out, In> for UnarySym<UnaryOpSet, Sym, Out, In>
where
    Sym: Symbol<Out, In>,
    Out: BasicNumOps + Any,
    In: Any,
    EExpr<Out, In>: Symbol<Out, In>,
{
    type Derivative = EExpr<Out, In>;
    fn diff(self, _: usize) -> <Self as Symbol<Out, In>>::Derivative {
        todo!()
    }
}
