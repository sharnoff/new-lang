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
     | TypeDecl
     | TraitDef
     | ImplBlock
     | ConstStmt
     | StaticStmt
     | ImportStmt
     | UseStmt .

FnDecl = ProofStmts Vis [ "const" ] [ "pure" ] "fn" Ident [ GenericParams ]
         FnParams [ "->" Type ] ( ";" | BlockExpr ) .

MacroDef   = ProofStmts Vis "macro" Ident MacroParams MacroBody .
TypeDecl   = ProofStmts Vis "type" Ident [ GenericParams ]
             [ "::" TypeBound ] ( ";" | [ "=" ] Type [ ";" ] ) .
TraitDef   = ProofStmts Vis "trait" Ident [ GenericParams ] [ "::" TypeBound ] ( ImplBody | ";" ) .
ImplBlock  =                "impl" [ Trait "for" ] Type ( ImplBody | ";" ) .
ConstStmt  =            Vis "const"  StructField ";" .
StaticStmt = ProofStmts Vis "static" StructField ";" .

ImportStmt = "import" StringLiteral [ "~" StringLiteral ] [ "as" Ident ] .

UseStmt = Vis "use" UsePath ";" .
UsePath = Path "." "{" [ UsePath { "," UsePath } [ "," ] ] "}" .
        | UseKind Path [ "as" Ident ] .
UseKind = "fn" | "macro" | "type" | "trait" | "const" | "static" .
Path = PathComponent { "." PathComponent } .
PathComponent = Ident [ GenericArgs ] .

Vis = [ "pub" ] .

ProofStmts = { "#" ProofStmt "\n" } .
ProofStmt = Expr ( "=>" | "<=>" ) Expr
          | Expr
          | "invariant" [ StringLiteral ] ":"
          | "forall" Pattern [ "in" Expr ] ":"
          | "exists" Pattern [ "in" Expr ] where ":" .

> MacroParams = TODO
> MacroBody = TODO

FnParams = "(" [ FnParamsReceiver [ "," ] ] [ StructField { "," StructField } [ "," ] ] ")" .
FnParamsReceiver = [ "&" [ Refinements ] ] [ "mut" ] "self" [ Refinements ] .

ImplBody = "{" { Item } "}" .

GenericParams = "<" GenericParam { "," GenericParam } [ "," ] ">" .
GenericParam = Ident [ "::" TypeBound ] [ "=" Type ]
             | "const" Ident ":" Type [ "=" Expr ] .
             | "ref" Ident" .

GenericArgs = "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg = [ Ident ":" ] Type
           | [ Ident ":" ] Expr    # Limited to BindingPower::Add/Sub or greater
           | "ref" Expr .          # Limited to BindingPower::Deref or greater

Trait = Path .

Type = Path [ Refinements ]
     | "&" [ Refinements ] Type 
     | [ "!" ] "mut" Type
     | "[" Type [ ";" Expr ] "]" Refinemnts
     | "{" [ StructField { "," StructField } [ "," ] ] "}"
     | "(" [ Type        { "," Type        } [ "," ] ] ")"
     | "enum" "{" { Ident Type "," } "}" .

Refinements = "|" Refinement { "," Refinement } [ "," ] "|" .
Refinement = "ref" [ "mut" ] Expr
           | [ "!" | "?" ] "init" .
StructField = Ident ( ":" Type | "::" TypeBound ) [ "=" Expr ] .
EnumVariant = Ident Type .
TypeBound = [ Refinements ] Trait { "+" Trait } .

Stmt = BigExpr "\n"
     | Expr ";"
     | Assignee AssignOp ( Expr ";" | BigExpr "\n" )
     | Item .
Assignee = "*" Expr
         | Path .

Expr = Literal
     | NamedExpr
     | PrefixOp Expr
     | Expr BinOp Expr
     | Expr PostfixOp
     | [ Path ] "{" StructFieldsExpr "}"    # (Named?) structs 
     | "[" Expr { "," Expr } [ "," ] "]"    # Array literals
     | "(" Expr { "," Expr } [ "," ] ")"    # Tuples
     | BlockExpr                            # Blocks
     | LetExpr                              # "let" expressions
     | ForExpr                              # For loops
     | WhileExpr                            # While loops
     | DoWhileExpr                          # Do-while loops
     | LoopExpr                             # "Loop" loops
     | IfExpr                               # Ifs
     | MatchExpr .                          # Matches

NamedExpr = PathComponent .
LetExpr = "let" Pattern [ ":" Type ] "=" Expr .

BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | DoWhileExpr | LoopExpr | BlockExpr .

IfExpr      = "if" Expr BlockExpr [ "else" BigExpr ] .
ForExpr     = "for" Pattern "in" Expr BlockExpr [ "else" BigExpr ] .
DoWhileExpr = "do" BlockExpr "while" Expr [ "else" BigExpr ] .
WhileExpr   = "while" Expr BlockExpr [ "else" BigExpr ] .
BlockExpr   = "{" { Stmt } [ Expr ] "}" .

MatchExpr = "match" Expr "{" { MatchArm } "}" .
MatchArm = Pattern [ "if" Expr ] "=>" ( BigExpr "\n" | Expr "," ) .

PrefixOp = "!" | "-" | "&" [ "mut" ] | "*" .
BinOp = "+" | "-" | "*" | "/" | "%"
      | "&" | "|" | "^" | "<<" | ">>" | "&&" | "||"
      | "<" | ">" | "<=" | ">=" | "==" | "!=" .

PostfixOp = "[" Expr "]"                # Indexing
          | "." Ident [ GenericArgs ]   # Field access / method calls
          | "." IntLiteral              # Tuple indexing
          | "(" StructFieldsExpr ")"    # Function calls
          | "~" Type                    # Type binding
          | "is" Pattern                # Pattern equivalence
          | "?"                         # "try" operator

PostfixOp = "[" Expr "]" | "?" .

AssignOp = "+=" | "-=" | "*=" | "/=" | "%="
         | "&=" | "|=" | "<<=" | ">>="
         | "=" .

FnArgs = "(" StructFieldsExpr ")" .

Pattern = [ "." Ident | Path ] StructPattern
        | [ "." Ident | Path ] "(" ElementsPattern ")"
        | "[" ElementsPattern "]"
        | [ "mut" ] Ident
        | "assign" Assignee 
        | "&" Pattern .
StructPattern = "{" [ FieldPattern [ "," FieldPattern ] [ "," ] ] [ ".." ] "}" .
FieldPattern = Ident [ ":" Pattern ] .

ElementsPattern = [ Pattern { "," Pattern } [ "," ] ] [ ".." ] .

Literal = CharLiteral | StringLiteral | IntLiteral | FloatLiteral .
FloatLiteral = IntLiteral "." IntLiteral .

StructFieldsExpr = { StructFieldExpr { "," StructFieldExpr } [ "," ] } .
StructFieldExpr = Ident [ ":" Expr ] .
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
Ident "<" Ident { "," Ident } "," Ident ">" "(" Ident ")"
                     or
Ident "<" Ident { "," Ident } "," Ident ">" "{" Ident "}"
```

We can therefore store exactly these cases where necessary and handle them later (once types are
known). It is also worth noting that this can only happen in comma-delimeted lists as well.

#### Single field structs

This is the third and final ambiguous case. It occurs exactly when there's a block expression
containing a single identifier, which can either be an anonymous struct with a single field being
initialized by a local variable with the same name *OR* a block expression where the identifier is a
trailing expression.

This one is somewhat more complex to handle, but is also resolved through type-checking. These
exactly take the form of:

```
"{" Ident "}"
```
