module Transform

import Syntax;
import Resolve;
import AST;
import ParseTree;

/* 
 * Transforming QL forms
 */
 
 
/* Normalization:
 *  wrt to the semantics of QL the following
 *     q0: "" int; 
 *     if (a) { 
 *        if (b) { 
 *          q1: "" int; 
 *        } 
 *        q2: "" int; 
 *      }
 *
 *  is equivalent to
 *     if (true) q0: "" int;
 *     if (true && a && b) q1: "" int;
 *     if (true && a) q2: "" int;
 *
 * Write a transformation that performs this flattening transformation.
 *
 */

AForm flatten(AForm f) {
  list[AQuestion] questions = [q | /form(_, list[AQuestion] qs):= f, AQuestion q <- qs];
  list[AQuestion] finalQuestions = [];
  for(AQuestion q <- questions) {
    finalQuestions += flatten(q, boolean(boolean(true)));
  }
  return form(f.name, finalQuestions);
}

list[AQuestion] flatten(AQuestion q, AExpr e) {
  switch (q) {
    case question(_, _, _): {
      return [ifthen(e, [q])];
    }
    case computedQuestion(_, _, _, _): {
      return [ifthen(e, [q])];
    }
    case ifthen(AExpr cond, list[AQuestion] qs): {
      list[AQuestion] finalQuestions = [];
      for(AQuestion q <- qs) {
        finalQuestions += flatten(q, and(e, cond));
      }
      return finalQuestions;
    }
    case ifthenelse(AExpr cond, list[AQuestion] qs1, list[AQuestion] qs2): {
      list[AQuestion] finalQuestions = [];
      for(AQuestion q <- qs1) {
        finalQuestions += flatten(q, and(e, cond));
      }
      for(AQuestion q <- qs2) {
        finalQuestions += flatten(q, and(e, not(cond)));
      }
      return finalQuestions;
    }
    default: throw ("Unknown question type");
  }
}

/* Rename refactoring:
 *
 * Write a refactoring transformation that consistently renames all occurrences of the same name.
 * Use the results of name resolution to find the equivalence class of a name.
 *
 */
 
start[Form] rename(start[Form] sf, loc useOrDef, str newName, UseDef useDef) {
  // return sf;
  Form f = sf.top;
  for (<loc y, loc x> <- useDef) {
    if(x == useOrDef) {
      break;
    } else if(y == useOrDef) {
      useOrDef = x;
      break;
    }
  }
  set[loc] toRename = {x | <loc x, loc y> <- useDef, y == useOrDef};
  toRename += useOrDef;

 
  return visit (sf) {
    case Id x => [Id]newName
      when x@\loc in toRename

    case q:(Question)`<Str _> <Id _> : <Type _>` => q[var = [Id]newName]
      when q@\loc in toRename

    case q:(Question)`<Str _> <Id _> : <Type _> = <Expr _>` => q[var = [Id]newName]
      when q@\loc in toRename

    case (Expr) `<Id x>` => [Expr]newName
      when x@\loc in toRename
  }
} 
 
 
 

