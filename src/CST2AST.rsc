module CST2AST

import Syntax;
import AST;

import ParseTree;
import String;

/*
 * Implement a mapping from concrete syntax trees (CSTs) to abstract syntax trees (ASTs)
 *
 * - Use switch to do case distinction with concrete patterns (like in Hack your JS) 
 * - Map regular CST arguments (e.g., *, +, ?) to lists 
 *   (NB: you can iterate over * / + arguments using `<-` in comprehensions or for-loops).
 * - Map lexical nodes to Rascal primitive types (bool, int, str)
 * - See the ref example on how to obtain and propagate source locations.
 */

AForm cst2ast(start[Form] sf) {
  Form f = sf.top; // remove layout before and after form
  return cst2ast(f); // form(id(""), [ ], src=f.src); 
}

AForm cst2ast(f:(Form)`form <Id name> { <Question* qs> }`) {
  return form(cst2ast(name), [cst2ast(q) | Question q <- qs], src=f.src);
}

default AQuestion cst2ast(q:(Question)`<Str text> <Id var> : <Type typee>`) {
  return question(cst2ast(text), cst2ast(var), cst2ast(typee), src=q.src);
}

AQuestion cst2ast(q:(Question)`<Str text> <Id var> : <Type typee> = <Expr expr>`) {
  return computedQuestion(cst2ast(text), cst2ast(var), cst2ast(typee), cst2ast(expr), src=q.src);
}

AQuestion cst2ast(q:(Question)`if ( <Expr expr> ) { <Question* tqs> } else { <Question* eqs> }`) {
  return ifthenelse(cst2ast(expr), [cst2ast(tq) | Question tq <- tqs], [cst2ast(eq) | Question eq <- eqs], src=q.src);
}

AQuestion cst2ast(q:(Question)`if  ( <Expr expr> ) { <Question* qs> }`) {
  return ifthen(cst2ast(expr), [cst2ast(q) | Question q <- qs], src=q.src);
}

AExpr cst2ast(Expr e) {
  switch (e) {
    case (Expr)`<Id x>`: return ref(id("<x>", src=x.src), src=x.src);
    case (Expr)`<Str s>`: return stringy(cst2ast(s), src=s.src);
    case (Expr)`<Int i>`: return integer(cst2ast(i), src=i.src);
    case (Expr)`<Bool b>`: return boolean(cst2ast(b), src=b.src);
    case (Expr)`(<Expr e>)`: return cst2ast(e);
    case (Expr)`- <Expr e>`: return min(cst2ast(e), src=e.src);
    case (Expr)`<Expr e1> + <Expr e2>`: return add(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> - <Expr e2>`: return sub(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> * <Expr e2>`: return mul(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> / <Expr e2>`: return div(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> == <Expr e2>`: return eql(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> != <Expr e2>`: return neq(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> \< <Expr e2>`: return lt(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> \<= <Expr e2>`: return leq(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> \> <Expr e2>`: return gt(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> \>= <Expr e2>`: return geq(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> && <Expr e2>`: return and(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`<Expr e1> || <Expr e2>`: return or(cst2ast(e1), cst2ast(e2), src=e.src);
    case (Expr)`! <Expr e>`: return not(cst2ast(e), src=e.src);
    
    default: throw "Unhandled expression: <e>";
  }
}

AStr cst2ast(Str s) {
  return string("<s>", src=s.src);
}

AInt cst2ast(Int i) {
  return integer(toInt("<i>"), src=i.src);
}

ABool cst2ast(Bool b) {
  return boolean(("<b>" == "true" ? true : false ), src=b.src);
}

AId cst2ast(Id x) {
  return id("<x>", src=x.src);
}

AType cst2ast(Type t) {
  switch (t) {
    case (Type)`integer`: return intType(src=t.src);
    case (Type)`string`: return stringType(src=t.src);
    case (Type)`boolean`: return boolType(src=t.src);

    default: throw "Unhandled type: <t>";
  }
}
