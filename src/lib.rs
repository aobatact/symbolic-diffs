#![feature(min_type_alias_impl_trait)]

use core::{any::Any, fmt::Display};
use num_traits::{One, Pow, Zero};
use std::fmt;
use std::sync::Arc;

pub mod float_ops;
pub mod ops;
pub mod symbols;

pub use float_ops::{ExNumConsts, ExNumOps};
pub(crate) use symbols::Expr;
pub use symbols::*;

/// Trait for Symbol using dynamic.
pub trait DynamicSymbol<Out, In: ?Sized>: Any + Display {
    /// Calculate the value of this expression.
    /// Use [`calc`](`crate::Symbol::calc`) for owned value for convenience.
    fn calc_ref(&self, value: &In) -> Out;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff_dyn(&self, dm: usize) -> DynExpr<Out, In>;
    /// Convert to any for downcast.
    fn as_any(&self) -> &(dyn Any);
}

///Expression symbol for calculating and differentiation.
pub trait Symbol<Out, In: ?Sized>: DynamicSymbol<Out, In> + Clone {
    /// return type for `diff`
    type Derivative: Symbol<Out, In>;
    /// Get the partial derivative of this expression.
    /// Dm is the marker of which variable for differentiation.
    /// Use usize 0 if there is only one variable.
    fn diff(self, dm: usize) -> Self::Derivative;

    /// Shortcut for calculating owned value from [`calc_ref`](`crate::DynamicSymbol::calc_ref`).
    #[inline]
    fn calc(&self, value: In) -> Out
    where
        In: Sized,
    {
        self.calc_ref(&value)
    }
    ///Wrap this symbol to [`Expr`](`crate::Expr`)
    fn to_expr(self) -> Expr<Self, Out, In> {
        self.into()
    }

    ///Wrap this symbol to [`DynExpr`]
    fn to_dyn_expr(self) -> DynExpr<Out, In> {
        DynExpr::Dynamic(Arc::new(self))
    }
}

impl<Out, In, Sym> DynamicSymbol<Out, In> for &'static Sym
where
    Out: Any,
    In: ?Sized + Any,
    Sym: DynamicSymbol<Out, In> + Any,
{
    fn calc_ref(&self, i: &In) -> Out {
        (*self).calc_ref(i)
    }
    fn diff_dyn(&self, d: usize) -> DynExpr<Out, In> {
        (*self).diff_dyn(d)
    }
    fn as_any(&self) -> &(dyn std::any::Any + 'static) {
        (*self).as_any()
    }
}

impl<Out, In, Sym> Symbol<Out, In> for &'static Sym
where
    Out: Any,
    In: ?Sized + Any,
    Sym: Symbol<Out, In> + Any,
{
    type Derivative = Sym::Derivative;
    fn diff(self, dm: usize) -> <Self as Symbol<Out, In>>::Derivative {
        self.clone().diff(dm)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    #[test]
    fn diplay_test() {
        let x: Expr<Variable, f32> = Variable.into();
        assert_eq!("x", x.to_string());
        let x1 = x + Const(1.);
        assert_eq!("x + 1", x1.to_string());
        let exp = x.exp();
        assert_eq!("exp( x)", exp.to_string());
        let exp1 = x1.exp();
        assert_eq!("exp( x + 1)", exp1.to_string());
        let xexp = x * exp;
        assert_eq!("(x)(exp( x))", xexp.to_string());
    }
}
