module Check

import AST;
import Resolve;
import Message; // see standard library

data Type
  = tint()
  | tbool()
  | tstr()
  | tunknown()
  ;

// the type environment consisting of defined questions in the form 
alias TEnv = rel[loc def, str name, str label, Type \type];

// To avoid recursively traversing the form, use the `visit` construct
// or deep match (e.g., `for (/question(...) := f) {...}` ) 
TEnv collect(AForm f) {
  TEnv tenv = {<x.src, x.name, l.s, toType(t)> | /question(AStr l, AId x, AType t):= f}; 
  tenv += {<x.src, x.name, l.s, toType(t)> | /computedQuestion(AStr l, AId x, AType t, _):= f};
  return tenv;
}

set[Message] check(AForm f, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {}; 
  set[set[Message]] sets = {check(q, tenv, useDef) | /form(_, qs) := f, q <- qs};
  for(set[Message] setm <- sets) {
    msgs += setm;
  }

  return msgs; 
}

// - produce an error if there are declared questions with the same name but different types.
// - duplicate labels should trigger a warning 
// - the declared type computed questions should match the type of the expression.
set[Message] check(AQuestion q, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {}; 
  set[set[Message]] sets = {check(expr, tenv, useDef) | /computedQuestion(_, _, _, expr) := q};
  
  sets += {check(expr, tenv, useDef) | /ifthen(expr, _) := q};
  sets += {check(ifq, tenv, useDef) | /ifthen(_, qs) := q, ifq <- qs};

  sets += {check(expr, tenv, useDef) | /ifthenelse(expr, _, _) := q};
  sets += {check(ifq, tenv, useDef) | /ifthenelse(_, qs, _) := q, ifq <- qs};
  sets += {check(elseq, tenv, useDef) | /ifthenelse(_, _, qs) := q, elseq <- qs};

  for(set[Message] setm <- sets) {
    msgs += setm;
  }

  msgs += { error("Same variable with conflicting types", s)
          | <loc s, str x, _, Type t1> <- tenv, <_, x, _, Type t2> <- tenv, t1 != t2 };
  msgs += { warning("Duplicate question", text.src)
          | /question(text, var, _):= q, <loc lc, _, str l, _> <- tenv, text.s == l, var.src != lc };
  msgs += { error("Declared type does not match expression type", x.src)
          | /computedQuestion(_, x, t1, expr):= q, toType(t1) != typeOf(expr, tenv, useDef)};
  

  return msgs; 
}

// Check operand compatibility with operators.
// E.g. for an addition node add(lhs, rhs), 
//   the requirement is that typeOf(lhs) == typeOf(rhs) == tint()
set[Message] check(AExpr e, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  
  switch (e) {
    case ref(AId x):
      msgs += { error("Undeclared variable", x.src) | useDef[x.src] == {} };
    case add(AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != tint() };
      msgs += { error("Incompatible types", rhs.src) | typeOf(rhs, tenv, useDef) != tint() };
    }
    case sub(AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != tint() };
      msgs += { error("Incompatible types", rhs.src) | typeOf(rhs, tenv, useDef) != tint() };
    }
    case min(AExpr exp):{
      msgs += { error("Incompatible types", exp.src) | typeOf(exp, tenv, useDef) != tint() };
    }
    case mul(AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != tint() };
      msgs += { error("Incompatible types", rhs.src) | typeOf(rhs, tenv, useDef) != tint() };
    }
    case div(AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != tint() };
      msgs += { error("Incompatible types", rhs.src) | typeOf(rhs, tenv, useDef) != tint() };
    }
    case and (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != tbool() };
      msgs += { error("Incompatible types", rhs.src) | typeOf(rhs, tenv, useDef) != tbool() };
    }
    case or (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != tbool() };
      msgs += { error("Incompatible types", rhs.src) | typeOf(rhs, tenv, useDef) != tbool() };
    }
    case not (AExpr exp):{
      msgs += { error("Incompatible types", exp.src) | typeOf(exp, tenv, useDef) != tbool() };
    }
    case eql (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != typeOf(rhs, tenv, useDef) };
    }
    case neq (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | typeOf(lhs, tenv, useDef) != typeOf(rhs, tenv, useDef) };
    }
    case lt (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | lh := typeOf(lhs, tenv, useDef), rh := typeOf(rhs, tenv, useDef), lh != rh, lh != tint(), rh != tint() };
    }
    case gt (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | lh := typeOf(lhs, tenv, useDef), rh := typeOf(rhs, tenv, useDef), lh != rh, lh != tint(), rh != tint() };
    }
    case leq (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | lh := typeOf(lhs, tenv, useDef), rh := typeOf(rhs, tenv, useDef), lh != rh, lh != tint(), rh != tint() };
    }
    case geq (AExpr lhs, AExpr rhs):{
      msgs += { error("Incompatible types", lhs.src) | lh := typeOf(lhs, tenv, useDef), rh := typeOf(rhs, tenv, useDef), lh != rh, lh != tint(), rh != tint() };
    }
    case integer(AInt x): {
      msgs += {};
    }
    case stringy(AStr x): {
      msgs += {};
    }
    case boolean(ABool x): {
      msgs += {};
    }                                  
    // etc.
  }
  
  return msgs; 
}

Type typeOf(AExpr e, TEnv tenv, UseDef useDef) {
  switch (e) {
    case ref(id(_, src = loc u)):  
      if (<u, loc d> <- useDef, <d, x, _, Type t> <- tenv) {
        return t;
      }
    case stringy(_): return tstr();
    case boolean(_): return tbool();
    case integer(_): return tint();
    case min(exp): return typeOf(exp, tenv, useDef);
    case add(lhs, rhs): 
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return typeOf(lhs, tenv, useDef);
      }
    case sub(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return typeOf(lhs, tenv, useDef);
      } 
    case mul(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return typeOf(lhs, tenv, useDef);
      }
    case div(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return typeOf(lhs, tenv, useDef);
      }
    case eql(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case neq(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case lt(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case gt(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case leq(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case geq(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case and(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case or(lhs, rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
        return tbool();
      }
    case not(exp):
      if (typeOf(exp, tenv, useDef) == tbool()) {
        return tbool();
      }
  }
  return tunknown(); 
}

Type toType(AType t) {
  switch (t) {
    case intType(): return tint();
    case boolType(): return tbool();
    case stringType(): return tstr();
  }
  return tunknown();
}

/* 
 * Pattern-based dispatch style:
 * 
 * Type typeOf(ref(id(_, src = loc u)), TEnv tenv, UseDef useDef) = t
 *   when <u, loc d> <- useDef, <d, x, _, Type t> <- tenv
 *
 * ... etc.
 * 
 * default Type typeOf(AExpr _, TEnv _, UseDef _) = tunknown();
 *
 */
 
 

