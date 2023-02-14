module Eval

import AST;
import Resolve;
import util::Random;

/*
 * Implement big-step semantics for QL
 */
 
// NB: Eval may assume the form is type- and name-correct.


// Semantic domain for expressions (values)
data Value
  = vint(int n)
  | vbool(bool b)
  | vstr(str s)
  ;

// The value environment
alias VEnv = map[str name, Value \value];

// Modeling user input
data Input
  = input(str question, Value \value);
  
// produce an environment which for each question has a default value
// (e.g. 0 for int, "" for str etc.)
VEnv initialEnv(AForm f) {
  //iterate over questions and produce a map
  VEnv venv = (x.name : toValue(t) | /question(_, AId x, AType t):= f);
  venv += (x.name : toValue(t) | /computedQuestion(_, AId x, AType t, _):= f);
  return venv;
}

Input initInput(str question, int val) {
  Input inp = input(question, vint(val));
  return inp;
}

Input initInput(str question, str val) {
  Input inp = input(question, vstr(val));
  return inp;
}

Input initInput(str question, bool val) {
  Input inp = input(question, vbool(val));
  return inp;
}

// Because of out-of-order use and declaration of questions
// we use the solve primitive in Rascal to find the fixpoint of venv.
VEnv eval(AForm f, Input inp, VEnv venv) {
  return solve (venv) {
    venv = evalOnce(f, inp, venv);
  }
}

VEnv evalOnce(AForm f, Input inp, VEnv venv) {
  // evaluate conditions for branching,
  // evaluate inp and computed questions to return updated VEnv
  //iterate over questions and produce a map
  list[AQuestion] questions = [q | /form(_, list[AQuestion] qs):= f, AQuestion q <- qs];
  for (AQuestion q <- questions) {
    venv = eval(q, inp , venv);
  }
  return venv; 
}

VEnv eval(AQuestion q, Input inp, VEnv venv) {
  // evaluate conditions for branching,
  // evaluate inp and computed questions to return updated VEnv
  switch (q) {
    case question(AStr text, AId var, AType t): {
      if(extractQuestion(inp) == extractText(text)) {
        venv[var.name] = extractValue(inp);
      }
    }
    case computedQuestion(_, AId var, _, AExpr e): {
        venv[var.name] = eval(e, venv);
    }
    case ifthen(AExpr expr, list[AQuestion] questions):{
        if (eval(expr, venv) == vbool(true)){
          for (AQuestion q <- questions) {
            venv = eval(q, inp , venv);
          }
        }
    }
    case ifthenelse(AExpr expr, list[AQuestion] thenQuestions, list[AQuestion] elseQuestions):{
        if (eval(expr, venv) == vbool(true)){
          for (AQuestion q <- thenQuestions) {
            venv = eval(q, inp , venv);
          }
        }
        if (eval(expr, venv) == vbool(false)){
          for (AQuestion q <- elseQuestions) {
            venv = eval(q, inp , venv);
          }
        }
    }
  }
  return venv; 
}

Value eval(AExpr e, VEnv venv) {
  Value finalVal;
  switch (e) {
    case ref(id(str x)): return venv[x];
    case integer(integer(n)): return vint(n);
    case boolean(boolean(b)): return vbool(b);
    case stringy(string(s)): return vstr(s);
    case add (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      int res = lval + rval;
      finalVal = vint(res);
    }
    case sub (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      int res = lval - rval;
      finalVal = vint(res);
    }
    case mul (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      int res = lval * rval;
      finalVal = vint(res);
    }
    case div (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      int res = lval / rval;
      finalVal = vint(res);
    }
    case min (AExpr expr): {
      int val = toInt(eval(expr, venv));
      int res = - val;
      finalVal = vint(res);
    }
    case and (AExpr lhs, AExpr rhs): {
      bool lval = toBool(eval(lhs, venv));
      bool rval = toBool(eval(rhs, venv));
      bool res = lval && rval;
      finalVal = vbool(res);
    }
    case or (AExpr lhs, AExpr rhs): {
      bool lval = toBool(eval(lhs, venv));
      bool rval = toBool(eval(rhs, venv));
      bool res = lval || rval;
      finalVal = vbool(res);
    }
    case not (AExpr expr): {
      bool val = toBool(eval(expr, venv));
      bool res = ! val;
      finalVal = vbool(res);
    }
    case eql (AExpr lhs, AExpr rhs): {
      Value lv = eval(lhs, venv);
      switch (lv) {
        case vint(lval): {
          int rval = toInt(eval(rhs, venv));
          bool res = lval == rval;
          finalVal = vbool(res);
        }
        case vbool(lval): {
          bool rval = toBool(eval(rhs, venv));
          bool res = lval == rval;
          finalVal = vbool(res);
        }
        case vstr(lval): {
          str rval = toStr(eval(rhs, venv));
          bool res = lval == rval;
          finalVal = vbool(res);
        }
        default: throw "Unsupported type <lv>";
      }
    }
    case neq (AExpr lhs, AExpr rhs): {
      Value lv = eval(lhs, venv);
      switch (lv) {
        case vint(lval): {
          int rval = toInt(eval(rhs, venv));
          bool res = lval != rval;
          finalVal = vbool(res);
        }
        case vbool(lval): {
          bool rval = toBool(eval(rhs, venv));
          bool res = lval != rval;
          finalVal = vbool(res);
        }
        case vstr(lval): {
          str rval = toStr(eval(rhs, venv));
          bool res = lval != rval;
          finalVal = vbool(res);
        }
        default: throw "Unsupported type <lv>";
      }
    }
    case leq (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      bool res = lval <= rval;
      finalVal = vbool(res);
    }
    case geq (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      bool res = lval >= rval;
      finalVal = vbool(res);
    }
    case lt (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      bool res = lval < rval;
      finalVal = vbool(res);
    }
    case gt (AExpr lhs, AExpr rhs): {
      int lval = toInt(eval(lhs, venv));
      int rval = toInt(eval(rhs, venv));
      bool res = lval > rval;
      finalVal = vbool(res);
    }
    default: throw "Unsupported expression <e>";
  }
  return finalVal;
}

Value toValue(AType t) {
  switch (t) {
    case intType(): return vint(0);
    case boolType(): return vbool(false);
    case stringType(): return vstr("");
    default: throw "Unsupported type <t>";
  }
}

int toInt(Value v) {
  switch (v) {
    case vint(n): return n;
    default: throw "Unsupported value <v>";
  }
}

bool toBool(Value v) {
  switch (v) {
    case vbool(b): return b;
    default: throw "Unsupported value <v>";
  }
}

str toStr(Value v) {
  switch (v) {
    case vstr(s): return s;
    default: throw "Unsupported value <v>";
  }
}

str extractText(AStr text) {
  switch (text) {
    case string(txt): return txt;
    default: throw "Unsupported text <text>";
  }
}

str extractQuestion(Input input) {
  switch (input) {
    case input(txt, _): return txt;
    default: throw "Unsupported input <input>";
  }
}

Value extractValue(Input input) {
  switch (input) {
    case input(_, val): return val;
    default: throw "Unsupported input <input>";
  }
}