module Syntax

extend lang::std::Layout;
extend lang::std::Id;

/*
 * Concrete syntax of QL
 */

start syntax Form 
  = "form" Id name "{"Question* questions "}"; 

// TODO: question, computed question, block, if-then-else, if-then
syntax Question 
  = Str text (Id var ":" Type type)
  | Str text (Id var ":" Type type "=" Expr result)
  | "if" "(" Expr condition ")" "{" Question+ statements1 "}" "else" "{" Question+ statements2 "}"
  | "if" "(" Expr condition ")" "{" Question+ statements "}"
  ;

// TODO: +, -, *, /, &&, ||, !, >, <, <=, >=, ==, !=, literals (bool, int, str)
// Think about disambiguation using priorities and associativity
// and use C/Java style precedence rules (look it up on the internet)
syntax Expr 
  = Id \ "true" \ "false" // true/false are reserved keywords.
  | Int number
  | Str string
  | Bool boolVal
  | "(" Expr ")"
  | left "-" Expr
  > left (Expr "*" Expr
  | Expr "/" Expr)
  > left (Expr "+" Expr
  | Expr "-" Expr)
  > left (Expr "&&" Expr
  | Expr "||" Expr
  | "!" Expr)
  > non-assoc (Expr "\>" Expr
  | Expr "\<" Expr
  | Expr "\>=" Expr
  | Expr "\<=" Expr
  | Expr "==" Expr
  | Expr "!=" Expr)
  ;
  
syntax Type = "integer" | "string" | "boolean";

lexical Str = [\"][a-zA-Z][a-zA-Z0-9\ _?:]*[\"];

lexical Int 
  = [0-9]+("."[0-9]+([eE]("+"|"-")?[0-9]+)?)?;

lexical Bool = "true" | "false";