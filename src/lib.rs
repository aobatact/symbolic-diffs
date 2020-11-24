use core::marker::PhantomData;
use num_traits::Zero;

mod ops;
pub use ops::*;

pub trait Symbol<Out, In = Out>: Clone {
    type Diff: Symbol<Out, In>;
    fn calc(&self, value: &In) -> Out;
    fn diff<Dm>(&self, dm: Dm) -> Self::Diff
    where
        Dm: DiffMarker;
}

pub trait DiffMarker: Copy {}
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct SingleDm;
impl DiffMarker for SingleDm {}

#[derive(Clone, PartialEq, Debug)]
pub struct Expr<Sym, Out, In = Out>(Sym, PhantomData<Out>, PhantomData<In>);

impl<Sym, O, I> From<Sym> for Expr<Sym, O, I> {
    #[inline]
    fn from(v: Sym) -> Self {
        Expr(v, PhantomData, PhantomData)
    }
}

impl<Sym, Out: Clone, In: Clone> Symbol<Out, In> for Expr<Sym, Out, In>
where
    Sym: Symbol<Out, In>,
{
    type Diff = Expr<Sym::Diff, Out, In>;
    fn calc(&self, v: &In) -> Out {
        self.0.calc(v)
    }
    fn diff<Dm>(&self, dm: Dm) -> <Self as Symbol<Out, In>>::Diff
    where
        Dm: DiffMarker,
    {
        self.0.diff(dm).into()
    }
}

pub trait UnaryOp {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnarySym<Op, Sym, Out, In = Out>
where
    Op: UnaryOp,
    Sym: Symbol<Out, In>,
{
    op: Op,
    sym: Sym,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

pub trait BinaryOp {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinarySym<Op, Sym1, Sym2, Out, In = Out>
where
    Op: BinaryOp,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    op: Op,
    sym1: Sym1,
    sym2: Sym2,
    po: PhantomData<Out>,
    pi: PhantomData<In>,
}

impl<Op: BinaryOp, Sym1: Symbol<Out, In>, Sym2: Symbol<Out, In>, Out, In>
    BinarySym<Op, Sym1, Sym2, Out, In>
{
    pub fn new_with_op(op: Op, sym1: Sym1, sym2: Sym2) -> Self {
        BinarySym {
            op: op,
            sym1: sym1,
            sym2: sym2,
            po: PhantomData,
            pi: PhantomData,
        }
    }

    pub fn new(sym1: Sym1, sym2: Sym2) -> Self
    where
        Op: Default,
    {
        BinarySym {
            op: Op::default(),
            sym1: sym1,
            sym2: sym2,
            po: PhantomData,
            pi: PhantomData,
        }
    }
}

impl<Op, Sym1, Sym2, Out, In> From<(Sym1, Sym2)> for BinarySym<Op, Sym1, Sym2, Out, In>
where
    Op: BinaryOp + Default,
    Sym1: Symbol<Out, In>,
    Sym2: Symbol<Out, In>,
{
    #[inline]
    fn from(v: (Sym1, Sym2)) -> Self {
        BinarySym::new(v.0, v.1)
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ZeroSym;
impl<Out, In> Symbol<Out, In> for ZeroSym
where
    Out: Zero,
{
    type Diff = ZeroSym;
    fn calc(&self, _v: &In) -> Out {
        Out::zero()
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<Out, In>>::Diff
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Variable;
impl<T> Symbol<T, T> for Variable
where
    T: Clone + Zero,
{
    type Diff = ZeroSym;
    fn calc(&self, v: &T) -> T {
        v.clone()
    }
    fn diff<Dm>(&self, _dm: Dm) -> <Self as Symbol<T, T>>::Diff
    where
        Dm: DiffMarker,
    {
        ZeroSym
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
