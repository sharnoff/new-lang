//! Handling for the stack-based portion of expression parsing

use super::{
    BinOp, BinOpExpr, BindingPower, Expr, Fixity, PostfixOp, PostfixOpExpr, PrefixOp, PrefixOpExpr,
};
use crate::files::Span;

/// The stack of previously paresd tokens and operators that may contribute to parsing an
/// expression
#[derive(Clone)]
pub struct Stack {
    pub(super) elems: Vec<Element>,

    /// A trailing expression, alongside its starting index in `total_src`. This is stored for
    /// additional validation at runtime
    pub(super) last_expr: Option<Expr>,
}

/// A helper type for [`Stack`]
///
/// [`Stack`]: struct.Stack.html
#[derive(Clone)]
pub(super) enum Element {
    BinOp { lhs: Expr, op: BinOp, op_src: Span },
    PrefixOp { op: PrefixOp, op_src: Span },
}

/// An indicator for the type of syntax element that's expected by the stack
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(super) enum Expecting {
    AtomOrPrefix,
    BinOpOrPostfix,
}

impl Stack {
    /// Constructs a new `Stack` from the
    pub const fn new() -> Self {
        Stack {
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

    /// Returns whether the stack requires an additional atomic expression in order to be completed
    ///
    /// This is exactly equal to testing if [`self.expecting()`] equals
    /// [`Expecting::AtomOrPrefix`].
    ///
    /// [`self.expecting()`]: #method.expecting
    /// [`Expecting::AtomOrPrefix`]: ../enum.Expecting.html
    pub(super) fn requires_more(&self) -> bool {
        self.expecting() == Expecting::AtomOrPrefix
    }

    /// Pushes the given prefix operator onto the stack
    pub fn push_prefix(&mut self, op: PrefixOp, op_src: Span) {
        assert_eq!(self.expecting(), Expecting::AtomOrPrefix);
        self.elems.push(Element::PrefixOp {
            op: op.clone(),
            op_src,
        });
    }

    /// Pushes the given atomic expression onto the stack
    ///
    /// This will panic if we aren't expecting one (i.e. if `self.expecting() != AtomOrPrefix`).
    pub fn push_atom(&mut self, expr: Expr) {
        assert!(self.last_expr.is_none());
        self.last_expr = Some(expr.clone());
    }

    /// Pushes the given binary operator onto the stack
    pub fn push_binop(&mut self, op: BinOp, op_src: Span) {
        self.collapse_bp_gt(op.bp(), op.fixity());
        let lhs = self.last_expr.take().unwrap();

        let elem = Element::BinOp { lhs, op, op_src };
        self.elems.push(elem);
    }

    /// Pushes the given postfix operator onto the stack
    pub fn push_postfix(&mut self, op: PostfixOp, op_src: Span) {
        // We use Fixity::Left just as a default here. Right-associative operators with the same
        // binding power as any postfix operators is a bug.
        self.collapse_bp_gt(op.bp(), Fixity::Left);
        let mut expr = self.last_expr.take().unwrap();

        let src = expr.span().join(op_src);
        expr = Expr::PostfixOp(PostfixOpExpr {
            src,
            expr: Box::new(expr),
            op,
            op_src,
        });
        self.last_expr = Some(expr);
    }

    /// Consumes the stack and produces an expression from it
    pub fn finish(mut self) -> Expr {
        // Because we're finishing, we'll collapse the entire stack
        self.collapse_bp_gt(BindingPower::ReservedLowest, Fixity::Left);

        // After collapsing with the lowest binding power, there should be no more elements left,
        // and there *should* be a trailing expression
        assert!(self.elems.is_empty());
        assert!(self.last_expr.is_some());

        self.last_expr.unwrap()
    }

    fn collapse_bp_gt(&mut self, bp: BindingPower, fixity: Fixity) {
        assert!(self.is_empty() || self.last_expr.is_some());

        let mut rhs = match self.last_expr.take() {
            None => return,
            Some(ex) => ex,
        };

        // Here, we bind `greater_than` - a function for comparing `BindingPower`s.
        //
        // Firstly: why do we need this function?
        //
        //   When we're pushing a binary- or postfix-operator to the stack, we take as the left-hand
        //   side the final expression in the stack. Because of this, we *need* all of the pending
        //   operators in the stack with *greater* binding power than the one we're adding to be
        //   collected into the single, final expression.
        //
        //   For a more concrete example, let's look at an example. Given the input:
        //     "x * y + z"
        //   We'll encounter the token '+' with a stack that looks like this:
        //     [ BinOp("x", '*') ]; last_expr = "y"
        //   But because multiplication has higher binding power than addition, we actually want the
        //   value of `last_expr` to be `x * y`.
        //
        //   So the binding to this function exists in order to make that comparison.
        //
        // Secondly: why is this conditional? and why these values in particular?
        //
        //   Suppose we have a left-associative operator (maybe '+'), and a stack with last
        //   expression that reads:
        //     [ BinOp("1", '+') ]; last_expr = "2"
        //   If we then encounter another '+' token, we'd like to fold this binary operator into
        //   the value of `last_expr`, giving `1 + 2`. This is what allows `1 + 2 + 3` to be parsed
        //   as `(1 + 2) + 3`. So clearly - for left-associative operators, we want to collapse
        //   operators that are greater than **or equal to** the one that's being added.
        //
        //   Conversely, right-associative operators (mainly '=') work the other way. If we're
        //   given `x = y = z` (an unusual case), we want to parse it as: `x = (y = z)`. So clearly
        //   here, we *don't* want any starting `x = y` to be folded into the final expression if
        //   we find a '=' as our next operator.
        //
        //   Because of the way that we always work backwards through the stack in a loop when we
        //   collapse it, a single decision to *not* group earlier operators means that they will
        //   be collected in a right-associative manner. In other words, the default method of
        //   collapsing is right-associative, so the collapses before each operator is added serves
        //   to allow others to be left-associative.
        let greater_than = match fixity {
            Fixity::Left => PartialOrd::ge,
            Fixity::Right => PartialOrd::gt,
        };

        while let Some(elem) = self.elems.pop() {
            match elem {
                Element::BinOp { lhs, op, op_src } => {
                    if !greater_than(&op.bp(), &bp) {
                        self.elems.push(Element::BinOp { lhs, op, op_src });
                        break;
                    }

                    let src = lhs.span().join(rhs.span());
                    rhs = Expr::BinOp(Box::new(BinOpExpr {
                        src,
                        lhs,
                        op,
                        op_src,
                        rhs,
                    }));
                }
                Element::PrefixOp { op, op_src } => {
                    if !greater_than(&op.bp(), &bp) {
                        self.elems.push(Element::PrefixOp { op, op_src });
                        break;
                    }

                    let src = op_src.join(rhs.span());
                    rhs = Expr::PrefixOp(Box::new(PrefixOpExpr {
                        src,
                        op,
                        op_src,
                        expr: Box::new(rhs),
                    }));
                }
            }
        }

        self.last_expr = Some(rhs);
    }
}
