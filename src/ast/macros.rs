//! Associated macros for use in parser submodules
//!
//! Most of the macros here are actually for producing *secondary* macros that are customized to a
//! local scope.

// A macro to produce closures that only partially map values
//
// Typical usage will look something like:
//   res.map_err(p!(Some(c) => Some(c + 1)))
// which would have been written without this as:
//   res.map_err(|cs| cs.map(|c| c + 1))
// While the second is shorter, I consider this less readable.
macro_rules! p {
    ($p:pat => $v:expr) => {{
        |x| match x {
            $p => $v,
            _ => x,
        }
    }};
}

macro_rules! end_source {
    ($containing_token:expr) => {{
        match $containing_token {
            Some(tt) => Source::EndDelim(tt),
            None => Source::EOF,
        }
    }};
}

macro_rules! binding_power {
    (
        $(#[$attrs:meta])*
        $vis:vis enum $binding_power:ident {
            $($($variant:ident),+;)*
        }
    ) => {
        $(#[$attrs])*
        $vis enum $binding_power {
            $($($variant,)+)*
        }

        impl $binding_power {
            // A helper function to return a unique value for each level of binding power.
            // NOTE: This does *not* start at zero.
            fn __level(&self) -> u8 {
                let mut count = 0;
                $(
                // we increment here because otherwise we get a warning at the bottom
                count += 1;

                match &self {
                    $($binding_power::$variant => return count,)+
                    _ => (),
                }
                )*

                unreachable!()
            }

            /// Returns the `BindingPower` variant corresponding to
            #[allow(unused_assignments)]
            pub fn inc(&self) -> Option<BindingPower> {
                let mut higher = None;

                $(
                match &self {
                    $($binding_power::$variant => return higher,)+
                    _ => (),
                }

                higher = Some(first!($($binding_power::$variant),+));
                )*

                unreachable!()
            }
        }

        impl PartialOrd for $binding_power {
            fn partial_cmp(&self, other: &$binding_power) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $binding_power {
            fn cmp(&self, other: &$binding_power) -> std::cmp::Ordering {
                // We reverse the ordering because high binding power is listed first in the macro,
                // causing them to have a small `__level`
                self.__level().cmp(&other.__level()).reverse()
            }
        }

        impl PartialEq for $binding_power {
            fn eq(&self, other: &$binding_power) -> bool {
                self.__level() == other.__level()
            }
        }

        impl Eq for $binding_power {}
    }
}

// A helper macro for yielding the first expression of a list
macro_rules! first {
    ($head:expr $(, $tail:expr)*) => {{
        $head
    }};
}

// We need to have rustfmt skip this, because it otherwise indents one further on every additional
// run
#[rustfmt::skip]
macro_rules! make_expect {
    ($tokens:expr, $consumed:expr, $ends_early:expr, $containing_token:expr, $errors:expr) => {
        macro_rules! expect {
            ($all:tt) => {
                make_expect!(@inner: $tokens, $consumed, $ends_early, $containing_token, $errors, $all)
            }
        }
    };
    (
        @inner:
        $tokens:expr,
        $consumed:expr,
        $ends_early:expr,
        $containing_token:expr,
        $errors:expr,
        (
            Ok(_),
            $($($token_kind:pat)|+ $(if $cond:expr)? => $arm:expr,)+
            $(@err $($err_kind:pat)|+ $(if $err_cond:expr)? => $err:expr,)*
            @else $else_tt:tt => $($expected:tt)+
        )
    ) => {
        make_expect!(
            @inner:
            $tokens, $consumed, $ends_early, $containing_token, $errors,
            (
                Ok(_t),
                $($($token_kind)|+ $(if $cond)? => $arm,)+
                $(@err $($err_kind)|+ $(if $err_cond)? => $err,)*
                @else $else_tt => $($expected)+
            )
        )
    };
    (
        @inner:
        $tokens:expr,
        $consumed:expr,
        $ends_early:expr,
        $containing_token:expr,
        $errors:expr,
        (
            Ok($token:ident),
            $($($token_kind:pat)|+ $(if $cond:expr)? => $arm:expr,)+
            $(@err $($err_kind:pat)|+ $(if $err_cond:expr)? => $err:expr,)*
            @else $else_tt:tt => $($expected:tt)+
        )
    ) => {{
        #[allow(unreachable_patterns)]
        match $tokens.get($consumed) {
            // If we run out of tokens (but it ended early), there's no point in reporting the same
            // error twice
            None if $ends_early => make_expect!(@do_else: $else_tt, $consumed),
            // Otherwise, we *were* expecting the given token kind!
            None => {
                make_expect!(@push: $errors, end_source!($containing_token), $($expected)+);
                make_expect!(@do_else: $else_tt, $consumed);
            }

            Some(Err(_e)) => {
                // Commented out because we probably don't want to *normally* generate double errors
                // make_expect!(@push: $errors, Source::TokenResult(Err(*_e)), $($expected)+);
                make_expect!(@do_else: $else_tt, $consumed);
            }

            Some(Ok($token)) => match &$token.kind {
                $($($token_kind)|+ $(if $cond)? => $arm,)+
                $($($err_kind)|+ $(if $err_cond)? => {
                    $errors.push($err);
                    make_expect!(@do_else: $else_tt, $consumed);
                })*
                #[allow(unreachable_patterns)]
                _ => {
                    make_expect!(@push: $errors, Source::TokenResult(Ok($token)), $($expected)+);
                    make_expect!(@do_else: $else_tt, $consumed);
                }
            }
        }
    }};
    (@push: $errors:expr, $source:expr, @no_error $(,)?) => {};
    (@push: $errors:expr, $source:expr, $expected_kind:expr $(,)?) => {{
        $errors.push(Error::Expected {
            kind: $expected_kind,
            found: $source,
        });
    }};
    (@do_else: (return Some), $consumed:expr) => {{ return Err(Some($consumed)) }};
    (@do_else: (return None), $consumed:expr) => {{ return Err(None) }};
    (@do_else: { $($exec:tt)* }, $consumed:expr) => {{ $($exec)* }};
}

macro_rules! assert_token {
    (
        $token_result:expr => $name:expr,
        Ok($token:ident) && $($token_kind:pat => $arm:expr),+ $(,)?
    ) => {{
        match $token_result {
            Some(Ok($token)) => match &$token.kind {
                $($token_kind => $arm,)+
                k => panic!("Expected {}, found token kind {:?}", $name, k),
            }
            t => panic!("Expected {}, found {:?}", $name, t),
        }
    }};
}

// A helper macro for constructing a closure that returns the `TokenKind` associated with a given
// index in the provided list of tokens
//
// Typical usage is simply:
//   let kind = kind!(tokens);
// The closure returned by this will return Some(kind) if the token successfully exists, and None
// otherwise.
macro_rules! kind {
    ($tokens:expr) => {{
        |idx: usize| Some(&$tokens.get(idx)?.as_ref().ok()?.kind)
    }};
}
