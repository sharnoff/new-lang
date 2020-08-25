//! An internal wrapper module for `Restrictions`

use crate::ast::errors::NoCurlyContext;

/// Restrictions on what types of expressions may be parsed
///
/// If these restrictions cause a certain region of tokens to not be parsed, please note that most
/// will not produce an error at that location. Of these, the only one that might is
/// `no_struct_postfix`, which will only produce an error if we find curly braces that *clearly*
/// indicate a struct (with [`is_definitely_struct()`]).
///
/// Most fields are named `no_*` to represent the type of construct that is disallowed. The one
/// exception is `allow_do_while` which defaults to `false`, unlike the rest.
///
/// [`is_definitely_struct()`]: fn.is_definitely_struct.html
#[derive(Debug, Copy, Clone, Default)]
pub struct Restrictions {
    pub no_struct_postfix: Option<NoCurlyContext>,
    pub no_else_branch: bool,
    pub no_pipe: bool,
    pub no_angle_bracket: bool,
    pub allow_do_while: bool,
}

impl Restrictions {
    /// Produces a new set of restrictions, where postfix structs are disallowed
    pub fn no_struct_postfix(self, ctx: NoCurlyContext) -> Self {
        Self {
            no_struct_postfix: Some(ctx),
            ..self
        }
    }

    /// Produces a new set of restrictions, where expressions that may include "else" branches are
    /// disallowed
    pub fn no_else_branch(self) -> Self {
        Self {
            no_else_branch: true,
            ..self
        }
    }

    /// Produces a new set of restrictions, where whether do-while expressions are allowed is given
    /// by the input boolaen
    pub fn with_do_while(self, allow: bool) -> Self {
        Self {
            allow_do_while: allow,
            ..self
        }
    }

    /// Produces a new set of restrictions, where angle brackets are disallowed
    pub fn no_angle_bracket(self) -> Self {
        Self {
            no_angle_bracket: true,
            ..self
        }
    }

    /// Produces a new set of restrictions, where pipes (`|`s) are disallowed
    pub fn no_pipe(self) -> Self {
        Self {
            no_pipe: true,
            ..self
        }
    }

    /// Returns whether the set of restrictions allows binary operators using angle brackets
    pub fn allows_angle_bracket(&self) -> bool {
        !self.no_angle_bracket
    }

    /// Returns whether the set of restrictions allows the [`BitOr`] binary operator
    ///
    /// [`BitOr`]: enum.BitOr.html#variant.BitOr
    pub fn allows_pipe(&self) -> bool {
        !self.no_pipe
    }

    /// Returns whether the set of restrictions allows expressions that may be followed by an
    /// [`else branch`](struct.ElseBranch.html)
    pub fn allows_else_branch(&self) -> bool {
        !self.no_else_branch
    }
}
