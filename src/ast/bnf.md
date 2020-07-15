# The syntax definition

This file gives the defnition of the syntax, along with some elaboration on the sorts of ambiguitiy
that can occur in parsing (and how those are resolved / delayed).

### Table of contents

* Notation ~ TODO
* [Givens](#givens)
* [Definition](#definition)
* [Notes on ambiguity](#notes-on-ambiguity)

### Givens

Before giving the definitions of each syntax element, we'll lay out a few of the pieces that are
taken as given by the tokenizer.

#### Comments

There are two types of comments parsed by the tokenizer - block and line comments. These are defined
such that line comments start with `//` and may occur anywhere on a line (outside of a string
literal), and block comments are delimeted by `/*` and `*/`. Block comments may themselves contain
block comments, which is handled by the tokenizer. The specifics of how this works won't be
described here.

#### Other items

Comments aside, the tokenizer produce only a few different "compound" tokens (those composed of
multiple characters) - whitespace, identifiers, and strings, character, and integer literals.

Roughly, each of these (aside from whitespace) are given by:

```
Ident          = { "_" | "a" .. "z" | "A" .. "Z" } .
StringLiteral = <"> { char } <">
CharLiteral   = "'" char '"'
IntLiteral    = { digit } .
```

Note that string and character literals currently *do not* support escaped characters. This will be
added in the future. Additionally, while integer literals are *syntactically* allowed leading
zeroes, this is semantically disallowed. The same can be said for indentifiers containing only
underscores.

### Definition

What follows is essentially the full BNF definition for the syntax. This is not written in a style
suitable for immediately translating to a recursive-descent parser, and instead written to emphasize
readability.

A single file is composed of `item`s, which essentially make up the top-level definitions and
declarations.

```
Item = FnDecl
     | MacroDef
     | TypeDef
     | TraitDecl
     | ImplBlock
     | ConstStmt
     | StaticStmt
     | ImportStmt
     | UseStmt .

FnDecl = ProofLines Vis [ "const" ] [ "pure" ] "fn" Ident [ GenericParams ]
         FnParams [ "->" Type ] ( ";" | BlockExpr ) .

MacroDef   = ProofLines Vis "macro" Ident MacroParams .
TypeDef    = ProofLines Vis "type" Ident [ GenericParams ] [ "=" ] Type .
TraitDecl  = ProofLines Vis "trait" Ident [ GenericParams ] "{" ImplBody "}" .
ImplBlock  = ProofLines     "impl" [ Trait "for" ] Ident [ GenericArgs ] "{" ImplBody "}" .
ConstStmt  = ProofLines Vis "const" VarField "=" Expr ";" .
StaticStmt = ProofLines Vis "static" VarField "=" Expr ";" .

ImportStmt = "import" StringLiteral ~ StringLiteral [ as "Ident" ] .

UseStmt = "use" Path "." "{" UseFragement [ { "," UseFragment } ] "}"
        | "use" UseFragement .
UseFragment = Path [ "as Ident ] .

Path = Ident { "." Ident } .

Vis = [ "pub" ] .

ProofLines = { "#" ProofStmt "\n" } .
ProofStmt = Expr ( "=>" | "<=>" ) Expr
          | Expr
          | "invariant" [ StringLiteral ] ":"
          | "forall" Pattern [ "in" Expr ] ":"
          | "exists" Pattern [ "in" Expr ] where ":" .

FnParams = "(" [ ] { "," } [ "," ]")" .
MacroParams = { Token } .
ImplBody = { Item } .

GenericParams = "<" GenericParam { "," GenericParam } [ "," ] ">"
GenericParam = Ident [ "::" Trait ] [ "=" Type ]
             | Ident ":" Type [ "=" Expr ] .
             | "|" "ref" Ident "|" .

GenericArgs = "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg = [ Ident "=" ] Type
           | [ Ident "=" ] "{" Expr "}"
           | "|" "ref" Expr "|" .

Trait = Ident [ GenericArgs ] .

Type = Ident [ GenericArgs ] Refinements
     | "&" Refinements Type 
     | [ "!" ] "mut" Type
     | "[" Type [ ";" Expr ] "]" Refinemnts
     | "{" { StructField "," } "}"
     | "(" { TupleField "," } ")"
     | "enum" "{" { EnumVariant "," } "}" .

Refinements = [ "|" Refinement { "," Refinement } "|" ] .
Refinement = "ref" [ "mut" ] Expr
           | [ "!" | "?" ] "init"

Stmt = BigExpr
     | Expr ";"
     | ( "*" Expr | Path ) AssignOp Expr ";" .

Expr = Literal
     | Expr "." Ident                                      # Struct fields
     | Expr "~" Type                                       # Type binding
     | PrefixOp Expr
     | Expr BinOp Expr
     | Expr PostfixOp
     | "let" Pattern [ ":" Type ] [ "=" Expr ]             # Let expressions
     | [ Expr [ GenericArgs ] ] "(" StructFieldsExpr ")"   # Function calls / (named?) tuples
     | [ Path [ GenericArgs ] ] "{" StructFieldsExpr "}"   # (Named?) structs 
     | "[" Expr { "," Expr } [ "," ] "]"                   # Array literals
     | "(" Expr { "," Expr } [ "," ] ")"                   # Tuples
     | BlockExpr                                           # Blocks
     | ForExpr                                             # For loops
     | WhileExpr                                           # While loops
     | LoopExpr                                            # "Loop" loops
     | IfExpr                                              # Ifs
     | MatchExpr .                                         # Matches

BigExpr   = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr .

IfExpr    = "if" Expr BlockExpr [ "else" BigExpr ] .
ForExpr   = "for" Pattern "in" Expr BlockExpr [ "else" BigExpr ] .
WhileExpr = "while" Expr BlockExpr [ "else" BigExpr ] .
BlockExpr = "{" { Stmt | Item } [ Expr ] "}" .

MatchExpr = "match" Expr "{" { MatchArm } "}" .
MatchArm = Pattern "=>" ( BigExpr "\n" | Expr "," ) .

PrefixOp = "!" | "-" | "&" [ "mut" ] | "*" .
BinOp = "+" | "-" | "*" | "/" | "%"
      | "&" | "|" | "<<" | ">>"
      | "<" | ">" | "<=" | ">=" | "==" | "!=" .
PostfixOp = "?" .

AssignOp = "+=" | "-=" | "*=" | "/=" | "%="
         | "&=" | "|=" | "<<=" | ">>="
         | "=" .

FnArgs = "(" StructFieldsExpr ")" .

Pattern = [ Path ] StructPattern
        | [ Path ] "(" Pattern { "," Pattern } [ "," ] ")"
        | "assign" Ident .

Literal = CharLiteral | StringLiteral | IntLiteral | FloatLiteral .
FloatLiteral = IntLiteral "." IntLiteral .

StructFieldsExpr = { StructField { "," StructField } [ "," ] } .
StructField = Ident [ ":" Expr ] .
```

### Notes on ambiguity

There are a few cases here that are ambiguous, all resulting in expression parsing. Two of these are
variants of the ambiguity that results in the infamous "turbofish" in Rust. Here are two examples:

#### "Classic" bastion of the turbofish

```
// integers oh, woe, is, me
let _: (bool, bool) = (oh<woe, is>(me));

// vs

fn oh<T,S>(x: T) -> S { ... }
let _: S = (oh<woe, is>(me))
```

#### "Struct" version

```
let x = (Foo<Bar, Baz> { y });
```

These two ambiguities aren't *too* bad to deal with - it actually happens to be the case that these
two examples are the only existing forms of this ambiguitiy. For clarity, it's exactly expressions
of the form:

```
Ident "<" Ident "," Ident ">" "(" Ident ")"
                     or
Ident "<" Ident "," Ident ">" "{" Ident "}"
```

We can therefore store exactly these cases where necessary and handle them later (once types are
known). It is also worth noting that this can only happen in comma-delimeted lists as well.

#### Single field structs

This is the third and final ambiguous case. It occurs exactly when there's a block expression
containing a single identifier, which can either be an anonymous struct with a single field being
initialized by a local variable with the same name *OR* a block expression where the identifier is a
trailing expression.

This one is somewhat more complex to handle, but is also resolved through type-checking.
