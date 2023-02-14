module AST

/*
 * Define Abstract Syntax for QL
 *
 * - complete the following data types
 * - make sure there is an almost one-to-one correspondence with the grammar
 */

data AForm(loc src = |tmp:///|)
  = form(AId name, list[AQuestion] questions)
  ; 

data AQuestion(loc src = |tmp:///|)
  = question(AStr text, AId var, AType \type)
  | computedQuestion(AStr text, AId var, AType \type, AExpr expr)
  | ifthen(AExpr expr, list[AQuestion] questions)
  | ifthenelse(AExpr expr, list[AQuestion] thenQuestions, list[AQuestion] elseQuestions)
  ; 

data AExpr(loc src = |tmp:///|)
  = ref(AId id)
  | add(AExpr left, AExpr right)
  | sub(AExpr left, AExpr right)
  | mul(AExpr left, AExpr right)
  | div(AExpr left, AExpr right)
  | min(AExpr expr)
  | and(AExpr left, AExpr right)
  | or(AExpr left, AExpr right)
  | not(AExpr expr)
  | eql(AExpr left, AExpr right)
  | neq(AExpr left, AExpr right)
  | lt(AExpr left, AExpr right)
  | leq(AExpr left, AExpr right)
  | gt(AExpr left, AExpr right)
  | geq(AExpr left, AExpr right)
  | integer(AInt valueInt)
  | boolean(ABool valueBool)
  | stringy(AStr valueString)
  ;

data AStr(loc src = |tmp:///|)
  = string(str s)
  ;

data AInt(loc src = |tmp:///|)
  = integer(int i)
  ;

data ABool(loc src = |tmp:///|)
  = boolean(bool b)
  ;

data AId(loc src = |tmp:///|)
  = id(str name);

data AType(loc src = |tmp:///|)
  = intType()
  | boolType()
  | stringType();