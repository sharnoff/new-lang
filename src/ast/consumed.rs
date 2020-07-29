//! A wrapper module for the `Consumed` trait
//!
//! For more information, refer to [the documentation](trait.Consumed.html) for the trait.

use super::*;

/// A trait for providing the number of tokens consumed in the construction of each syntax element
///
/// This is provided as a trait (instead of individual methods) so that certain types that aren't
/// owned in this module (e.g. `Option<Vis>`) may implement this as well. To allow this, there is a
/// blanket implementation of `Consumed` for `Option<T>`, where `T: Consumed`.
pub(super) trait Consumed {
    /// Gives the number of tokens consumed to construct the syntax element
    fn consumed(&self) -> usize;
}

impl Consumed for &Token<'_> {
    fn consumed(&self) -> usize {
        1
    }
}

impl<T: Consumed> Consumed for Option<T> {
    fn consumed(&self) -> usize {
        self.as_ref().map(Consumed::consumed).unwrap_or(0)
    }
}

impl<T: Consumed> Consumed for Box<T> {
    fn consumed(&self) -> usize {
        std::ops::Deref::deref(&self).consumed()
    }
}

macro_rules! impl_all {
    ($($(@$single:ident:)? $ty:ident $({$($variants:ident),* $(,)?})?),* $(,)?) => {
        $(impl_all!(@internal $(@$single)? $ty $($($variants)*)?);)*
    };

    (@internal $ty:ident) => {
        impl<'a> Consumed for $ty<'a> {
            fn consumed(&self) -> usize {
                self.src.len()
            }
        }
    };

    (@internal @$single:ident $ty:ident) => {
        impl<'a> Consumed for $ty<'a> {
            fn consumed(&self) -> usize {
                // A compatability check to ensure that the source remains a single token
                let _: &Token = self.src;
                1
            }
        }
    };

    (@internal $ty:ident $($variants:ident)*) => {
        impl<'a> Consumed for $ty<'a> {
            fn consumed(&self) -> usize {
                match self {
                    $($ty::$variants(t) => t.consumed(),)*
                }
            }
        }
    };
}

impl_all! {
    // Items
    Item { Fn, Macro, Type, Trait, Impl, Const, Static, Import, Use },
    FnDecl,
    MacroDef,
    TypeDecl,
    TraitDef,
    ImplBlock,
    ConstStmt,
    StaticStmt,
    ImportStmt,
    UseStmt,
    // Item helper bits
    ProofStmts,
    ProofStmt,
    @Single: ImplBody,
    UsePath { Multi, Single },
    MultiUse,
    SingleUse,
    @Single: FnParams,
    FnParamsReceiver,
    GenericParams,
    GenericParam { Type, Const, Ref },
    GenericTypeParam,
    GenericConstParam,
    GenericRefParam,

    // Expressions
    Expr {
        Literal, Named, PrefixOp, BinOp, PostfixOp, Struct, Array, Tuple, Block,
        AmbiguousBlock, For, While, DoWhile, Loop, If, Match, Continue,
    },
    PrefixOpExpr,
    BinOpExpr,
    PostfixOpExpr,
    @Single: StructExpr,
    @Single: ArrayExpr,
    @Single: TupleExpr,
    @Single: BlockExpr,
    @Single: AmbiguousBlockExpr,
    ForExpr,
    WhileExpr,
    DoWhileExpr,
    LoopExpr,
    IfExpr,
    MatchExpr,
    MatchArm,
    @Single: ContinueExpr,
    // Expression helper bits
    Path,
    PathComponent,
    FnArg,
    StructFieldExpr,
    ElseBranch,

    // Statements
    Stmt { BigExpr, LittleExpr, Assign, Item },
    LittleExprStmt,
    AssignStmt,
    // Statement helper bits
    Assignee { Deref, Path },

    // Patterns
    Pattern { Named, Struct, Tuple, Array, Assign, Ref, Literal },
    NamedPattern,
    NamedPatternKind { Struct, Tuple },
    @Single: StructPattern,
    @Single: TuplePattern,
    @Single: ArrayPattern,
    AssignPattern,
    RefPattern,
    FieldPattern,
    ElementPattern { Dots, Pattern },

    // Types
    Type { Named, Ref, Mut, Array, Struct, Tuple, Enum },
    NamedType,
    RefType,
    MutType,
    @Single: StructType,
    @Single: ArrayType,
    @Single: TupleType,
    EnumType,
    // Types helper bits
    StructTypeField,
    Refinements,
    Refinement { Ref, Init },
    RefRefinement,
    InitRefinement,
    TypeBound,
    GenericArgs,
    GenericArg { Type, Const, Ref, Ambiguous },
    TypeGenericArg,
    ConstGenericArg,
    RefGenericArg,
    AmbiguousGenericArg,

    // Literals
    @Single: Ident,
    Literal { Char, String, Int, Float },
    @Single: CharLiteral,
    @Single: StringLiteral,
    IntLiteral,
    FloatLiteral,
}

impl<'a> Consumed for Vis<'a> {
    fn consumed(&self) -> usize {
        match self {
            Vis::Pub { .. } => 1,
        }
    }
}
