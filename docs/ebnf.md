# Parsing

We provide the full EBNF specification below.

```ebnf
program ::= declaration+

declaration ::= 
      'let' pattern generics? annotation? '=' expr
    | 'type' IDENTIFIER generics? '=' annotation
    | 'enum' IDENTIFIER generics? '=' '|'? constructor ( '|' constructor )*

constructor ::= IDENTIFIER ( '(' annotation ')' )?

expr ::=
      'let' pattern generics? annotation? '=' expr 'in' expr
    | 'if' expr 'then' expr 'else' expr
    | 'fn' pattern annotation? '=>' expr
    | 'match' expr 'with' match_branches
    | 'rec' recursive_expr
    | or
    
recursive_expr ::=
      IDENTIFIER '=>' expr
    | '{' record_field ( ',' record_field )* '}'
    
match_branches ::= ( '|' pattern '=>' expr )+

or ::= or '||' and | and

and ::= and '&&' compare | compare

compare ::= cons ( '==' | '!=' | '<' | '>' | '<=' | '>=' | '==.' | '!=.' | '<.' | '>.' | '<=.' | '>=.' | '==b' | '!=b' ) cons 
    | cons
    
cons ::= concat '::' cons | concat

concat ::= concat '^' term | term

term ::= term ( '+' | '-' | '+.' | '-.' ) factor 
    | factor

factor ::= factor ( '*' | '/' | '*.' | '/.' ) apply | apply

apply ::=
      apply primary
    | 'fix' unary
    | unary

unary ::=
      ( '!' | '-' | '-.' ) unary
    | primary
    
primary ::= simple postfix*

simple ::=
      LITERAL
    | IDENTIFIER
    | '(' ')'
    | '[]'
    | '(' expr ( ',' expr )* ')'
    | '{' record_field ( ',' record_field )* '}'
    
record_field ::= IDENTIFIER ( ':' expr )?

postfix ::= '.' IDENTIFIER

pattern ::=
      IDENTIFIER ( '(' pattern ')' )?
    | '_'
    | '(' ')'
    | '[]'
    | '(' pattern ( ',' pattern )* ')'
    | pattern '::' pattern
    | '{' pattern_record_field ( ',' pattern_record_field )* '}'

pattern_record_field ::= IDENTIFIER ( ':' pattern )?
    
generics ::= ( '[' IDENTIFIER ']' )+

annotation ::= ':' type
```

## Type

```ebnf
type ::= type_arrow

type_arrow ::= type_product '->' type_arrow 
             | type_product

type_product ::= type_product '*' type_apply 
               | type_apply

type_apply ::= type_apply '[' type ']'
             | type_atom

type_atom ::= 'bool'
            | 'int'
            | 'float'
            | 'unit'
            | IDENTIFIER
            | '(' type ')'
            | '{' type_record_field ( ',' type_record_field )* '}'

type_record_field ::= IDENTIFIER ':' type
```