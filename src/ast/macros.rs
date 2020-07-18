//! Associated macros for use in parser submodules
//!
//! Most of the macros here are actually for producing *secondary* macros that are customized to a
//! local scope.

macro_rules! make_getter {
    (macro_rules! $get_name:ident, $tokens:expr, $ends_early:expr, $errors:expr) => {
        // A helper macro for local use within parsing functions
        //
        // This only works for functions returning `Result<_, Option<usize>>`, which corresponds to
        // the consume-style parsers. The macro simply wraps `tokens.get(..)` so that we can
        // extract a single `&Token` instead of a `&Result<Token, _>`. Error handling is given so
        // that we can explicitly handle the cases of tokenzier errors and running out of tokens
        // separately.
        macro_rules! $get_name {
            ($consumed:expr, Err($e:ident) => $err:expr, None => $none:expr,) => {
                match $tokens.get($consumed) {
                    Some(Ok(t)) => t,
                    Some(Err($e)) => {
                        use token_tree::Error::*;

                        // All of the errors currently assume that tokenizer errors are due to
                        // delimeters. For future compatability, we'll simply match on all of those
                        // to ensure that this stays the case.
                        //
                        // NOTE: If you come here because this match statement is missing values,
                        // there's other logic that needs to be replaced in *every* usage of this
                        // macro - DO NOT make this a quick fix.
                        match $e {
                            UnexpectedCloseDelim(_)
                            | MismatchedCloseDelim { .. }
                            | UnclosedDelim(_, _) => (),
                        }

                        $errors.push($err);
                        return Err(None);
                    }
                    // If we ran out of tokens but they were limited due to a previous error, we'll
                    // silently ignore it and indicate that this token tree should no longer be
                    // parsed.
                    None if $ends_early => return Err(None),
                    // Otherwise, we'll use the error given to us above
                    None => {
                        $errors.push($none);
                        return Err(None);
                    }
                }
            }
        }
    }
}
