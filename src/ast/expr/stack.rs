//! Handling for the stack-based portion of expression parsing

use super::{
    BinOp, BinOpExpr, BindingPower, Expr, PostfixOp, PostfixOpExpr, PrefixOp, PrefixOpExpr,
};
use crate::ast::{Consumed, TokenSlice};

/// The stack of previously paresd tokens and operators that may contribute to parsing an
/// expression
#[derive(Clone)]
pub struct Stack<'a> {
    total_src: TokenSlice<'a>,
    pub(super) elems: Vec<Element<'a>>,

    /// A trailing expression, alongside its starting index in `total_src`. This is stored for
    /// additional validation at runtime
    pub(super) last_expr: Option<(usize, Expr<'a>)>,
}

/// A helper type for [`Stack`]
///
/// [`Stack`]: struct.Stack.html
#[derive(Clone)]
pub(super) enum Element<'a> {
    BinOp {
        src_offset: usize,
        lhs: Expr<'a>,
        op: BinOp,
        op_src: TokenSlice<'a>,
    },
    PrefixOp {
        src_offset: usize,
        op: PrefixOp<'a>,
        op_src: TokenSlice<'a>,
    },
}

/// An indicator for the type of syntax element that's expected by the stack
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(super) enum Expecting {
    AtomOrPrefix,
    BinOpOrPostfix,
}

impl<'a> Stack<'a> {
    /// Constructs a new `Stack` from the
    pub const fn new(total_src: TokenSlice<'a>) -> Self {
        Stack {
            total_src,
            elems: Vec::new(),
            last_expr: None,
        }
    }

    /// Returns whether the stack is empty
    ///
    /// This will be true only before any expression pieces have been added to the stack.
    pub fn is_empty(&self) -> bool {
        self.last_expr.is_none() && self.elems.is_empty()
    }

    /// Returns syntax element that the stack is currently expecting
    pub(super) fn expecting(&self) -> Expecting {
        match self.last_expr {
            None => Expecting::AtomOrPrefix,
            Some(_) => Expecting::BinOpOrPostfix,
        }
    }

    /// Pushes the given prefix operator onto the stack
    pub fn push_prefix(&mut self, src_offset: usize, op: PrefixOp<'a>, op_src: TokenSlice<'a>) {
        assert_eq!(self.expecting(), Expecting::AtomOrPrefix);
        self.elems.push(Element::PrefixOp {
            src_offset,
            op: op.clone(),
            op_src,
        });
    }

    /// Pushes the given atomic expression onto the stack
    ///
    /// This will panic if we aren't expecting one (i.e. if `self.expecting() != AtomOrPrefix`).
    pub fn push_atom(&mut self, src_offset: usize, expr: Expr<'a>) {
        assert!(self.last_expr.is_none());
        self.last_expr = Some((src_offset, expr.clone()));
    }

    /// Pushes the given binary operator onto the stack
    pub fn push_binop(&mut self, src_offset: usize, op: BinOp, op_src: TokenSlice<'a>) {
        self.collapse_bp_gt(op.bp());
        let (start, lhs) = self.last_expr.take().unwrap();

        assert_eq!(start + lhs.consumed(), src_offset);

        let elem = Element::BinOp {
            src_offset: start,
            lhs,
            op,
            op_src,
        };
        self.elems.push(elem);
    }

    /// Pushes the given postfix operator onto the stack
    pub fn push_postfix(&mut self, src_offset: usize, op: PostfixOp<'a>, op_src: TokenSlice<'a>) {
        self.collapse_bp_gt(op.bp());
        let (start, mut expr) = self.last_expr.take().unwrap();

        assert_eq!(start + expr.consumed(), src_offset);

        let src = &self.total_src[start..src_offset + op_src.len()];
        expr = Expr::PostfixOp(PostfixOpExpr {
            src,
            expr: Box::new(expr),
            op,
            op_src,
        });
        self.last_expr = Some((start, expr));
    }

    /// Consumes the stack and produces an expression from it
    pub fn finish(mut self) -> Expr<'a> {
        // Because we're finishing, we'll collapse the entire stack
        self.collapse_bp_gt(BindingPower::ReservedLowest);

        // After collapsing with the lowest binding power, there should be no more elements left,
        // and there *should* be a trailing expression
        assert!(self.elems.is_empty());
        assert!(self.last_expr.is_some());

        let (_, expr) = self.last_expr.unwrap();
        expr
    }

    fn collapse_bp_gt(&mut self, bp: BindingPower) {
        assert!(self.is_empty() || self.last_expr.is_some());

        let mut rhs = match self.last_expr.take() {
            None => return,
            Some(ex) => ex,
        };

        while let Some(elem) = self.elems.pop() {
            match elem {
                Element::BinOp {
                    src_offset,
                    lhs,
                    op,
                    op_src,
                } => {
                    // There's a little bit of explanation necessary for the choice of strictly
                    // less-than in the condition below. We'll use this example:
                    //   Given a stack and last expression that reads
                    //      [ BinOp(1, +) ]; Some(Expr(2))
                    //   and supposing we encounter the token `+`, we want to collapse the existing
                    //   stack and expression to
                    //      [ ]; Some(Expr(1 + 2))
                    //   which we then turn into:
                    //      [ BinOp(1 + 2, +) ]; None
                    //   after applying the token
                    //
                    // The collapsing process above will be done with a call to this function, so we
                    // want to collapse even if the operator's binding power is equal to the binding
                    // power we were given - i.e. only if the operator's binding power is strictly
                    // less than this `bp` will we stop collapsing the stack.
                    if op.bp() < bp {
                        self.elems.push(Element::BinOp {
                            src_offset,
                            lhs,
                            op,
                            op_src,
                        });
                        break;
                    }

                    let (_rhs_offset, mut rhs_expr) = rhs;

                    let size = lhs.consumed() + op_src.len() + rhs_expr.consumed();
                    let src = &self.total_src[src_offset..src_offset + size];

                    rhs_expr = Expr::BinOp(Box::new(BinOpExpr {
                        src,
                        lhs,
                        op,
                        op_src,
                        rhs: rhs_expr,
                    }));
                    rhs = (src_offset, rhs_expr);
                }
                Element::PrefixOp {
                    src_offset,
                    op,
                    op_src,
                } => {
                    // See justification for `<` here (instead of `<=`) above
                    if op.bp() < bp {
                        self.elems.push(Element::PrefixOp {
                            src_offset,
                            op,
                            op_src,
                        });
                        break;
                    }

                    let (_rhs_offset, mut rhs_expr) = rhs;

                    let size = op_src.len() + rhs_expr.consumed();
                    let src = &self.total_src[src_offset..src_offset + size];
                    rhs_expr = Expr::PrefixOp(Box::new(PrefixOpExpr {
                        src,
                        op,
                        op_src,
                        expr: Box::new(rhs_expr),
                    }));

                    rhs = (src_offset, rhs_expr);
                }
            }
        }

        self.last_expr = Some(rhs);
    }
}
