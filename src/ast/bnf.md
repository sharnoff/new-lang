# The syntax definition

This file gives the defnition of the syntax, along with some elaboration on the sorts of ambiguitiy
that can occur in parsing (and how those are resolved / delayed).

### Table of contents

* Notation ~ TODO
* [Givens](#givens)
* [Definition](#definition)

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

FnDecl = ProofStmts [ Vis ] [ "const" ] [ "pure" ] "fn" Ident [ GenericsParams ]
         FnParams [ "->" Type ] ( ";" | BlockExpr ) .

MacroDef   = ProofStmts [ Vis ] "macro" Ident MacroParams MacroBody .
TypeDecl   = ProofStmts [ Vis ] "type" Ident [ GenericsParams ]
             [ "::" TypeBound ] ( ";" | [ "=" ] Type [ ";" ] ) .
TraitDef   = ProofStmts [ Vis ] "trait" Ident [ GenericsParams ] [ "::" TypeBound ] ( ImplBody | ";" ) .
ImplBlock  =                    "impl" [ Trait "for" ] Type ( ImplBody | ";" ) .
ConstStmt  =            [ Vis ] "const"  Field ";" .
StaticStmt = ProofStmts [ Vis ] "static" Field ";" .

ImportStmt = "import" StringLiteral [ "~" StringLiteral ] [ "as" Ident ] .

UseStmt = [ Vis ] "use" UsePath ";" .
UsePath = Path "." "{" [ UsePath { "," UsePath } [ "," ] ] "}" .
        | UseKind Path [ "as" Ident ] .
UseKind = "fn" | "macro" | "type" | "trait" | "const" | "static" .
Path = PathComponent { "." PathComponent } .
PathComponent = Ident [ GenericsArgs ] .

Vis = "pub" .

ProofStmts = { "#" ProofStmt "\n" } .
ProofStmt = Expr ( "=>" | "<=>" ) Expr
          | Expr
          | "invariant" [ StringLiteral ] ":"
          | "forall" Pattern [ "in" Expr ] ":"
          | "exists" Pattern [ "in" Expr ] where ":" .

> MacroParams = TODO
> MacroBody = TODO

FnParams = "(" [ FnParamsReceiver [ "," ] ] [ Field { "," Field } [ "," ] ] ")" .
FnParamsReceiver = [ "&" [ Refinements ] ] [ "mut" ] "self" [ Refinements ] .

ImplBody = "{" { Item } "}" .

GenericsParams = "<" GenericsParam { "," GenericsParam } [ "," ] ">" .
GenericsParam = Ident [ "::" TypeBound ] [ "=" Type ]
             | "const" Ident ":" Type [ "=" Expr ] .
             | "ref" Ident" .

GenericsArgs = "<" "(" GenericsArg { "," GenericsArg } [ "," ] ")" ">"
             | "<" GenericsArg ">"
GenericsArg = [ Ident ":" ] Type
            | [ Ident ":" ] Expr
            | "ref" Expr .

Trait = Path .

Type = NamedType
     | RefType
     | MutType
     | ArrayType
     | StructType
     | TupleType
     | EnumType .

NamedType = Path [ Refinements ] .
RefType = "&" [ Refinements ] Type [ Refinements ] .
MutType = [ "!" | "?" ] "mut" Type .
ArrayType = "[" Type [ ";" Expr ] "]" .
StructType = "{" [ StructTypeField { "," StructTypeField } [ "," ] ] "}" .
TupleType = "(" [ TupleTypeElement { "," TupleTypeElement } [ "," ] ] ")" .
EnumType = "enum" "{" { Ident [ Type ] "," } "}" .

Refinements = "|" Refinement { "," Refinement } [ "," ] "|" .
Refinement = "ref" Expr
           | [ "!" | "?" ] "init"
           | Expr .
StructTypeField = [ Vis ] Ident ":" Type [ "=" Expr ] .
TupleTypeELement = [ Vis ] Type .
EnumVariant = [ Vis ] Ident [ Type ] .
TypeBound = [ Refinements ] Trait { "+" Trait } .

Field = Ident ( ":" Type | "::" TypeBound ) [ "=" Expr ] .

Stmt = BigExpr
     | Expr ";"
     | Item .

Expr = Literal
     | NamedExpr
     | PrefixOp Expr
     | Expr BinOp Expr
     | Expr PostfixOp
     | StructExpr                               # Anonymous structs 
     | "[" [ Expr { "," Expr } [ "," ] ] "]"    # Array literals
     | "(" [ Expr { "," Expr } [ "," ] ] ")"    # Tuples
     | BlockExpr                                # Blocks
     | ForExpr                                  # For loops
     | WhileExpr                                # While loops
     | DoWhileExpr                              # Do-while loops
     | LoopExpr                                 # "Loop" loops
     | IfExpr                                   # Ifs
     | MatchExpr                                # Matches
     | "continue" .

NamedExpr = PathComponent .

StructExpr = "{" [ StructFieldExpr { "," StructFieldExpr } [ "," ] ] "}" .
StructFieldExpr = Ident [ ":" Expr ] .

LetExpr = "let" Pattern [ ":" Type ] "=" Expr .

BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr | StructExpr .

IfExpr      = "if" Expr BlockExpr [ "else" BigExpr ] .
ForExpr     = "for" Pattern "in" Expr BlockExpr [ "else" BigExpr ] .
DoWhileExpr = "do" BlockExpr "while" Expr [ "else" BigExpr ] .
WhileExpr   = "while" Expr BlockExpr [ "else" BigExpr ] .
BlockExpr   = "{" { Stmt } [ Expr ] "}" .

MatchExpr = "match" Expr "{" { MatchArm } "}" .
MatchArm = Pattern [ "if" Expr ] "=>" ( BigExpr | Expr "," ) .

PrefixOp = "!" | "-" | "&" [ "mut" ] | "*" | "break" | "return" | LetPrefix .
LetPrefix = "let" Pattern [ ":" Type ] "=" .
BinOp = "+" | "-" | "*" | "/" | "%"
      | "&" | "|" | "^" | "<<" | ">>" | "&&" | "||"
      | "<" | ">" | "<=" | ">=" | "==" | "!="
      | "+=" | "-=" | "*=" | "/=" | "%="
      | "&=" | "|=" | "<<=" | ">>=" | "=" .

PostfixOp = "[" Expr "]"                # Indexing
          | "." Ident [ GenericsArgs ]   # Field / method access
          | "." IntLiteral              # Tuple indexing
          | FnArgs                      # Function calls
          | StructExpr                  # Named structs
          | "~" Type                    # Type binding
          | "is" Pattern                # Pattern equivalence
          | "?"                         # "try" operator

PostfixOp = "[" Expr "]" | "?" .

FnArgs = "(" [ FnArg { "," FnArg } [ "," ] ] ")" .
FnArg = [ Ident ":" ] Expr .

Pattern = NamedPattern
        | StructPattern
        | TuplePattern
        | ArrayPattern
        | AssignPattern
        | RefPattern
        | Literal .
NamedPattern = PatternPath [ StructPattern | TuplePattern ] .
PatternPath = "." Ident | Ident { "." Ident } .

StructPattern = "{" [ FieldPattern [ "," FieldPattern ] [ "," ] ] [ ".." ] "}" .
FieldPattern = Ident [ ":" Pattern ] .

TuplePattern = "(" [ Pattern { "," Pattern } [ "," ] ] ")" .
ArrayPattern = "[" [ ElementPattern { "," ElementPattern } [ "," ] ]  "]" .
ElementPattern = ".." | Pattern .

AssignPattern    = "assign" Expr .
RefPattern       = "&" Pattern .

Literal = CharLiteral | StringLiteral | IntLiteral | FloatLiteral .
FloatLiteral = IntLiteral "." IntLiteral .
```
