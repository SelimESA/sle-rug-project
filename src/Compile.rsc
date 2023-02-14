module Compile

import AST;
import Resolve;
import Eval;
import Transform;
import IO;
import lang::html::AST; // see standard library
import lang::html::IO;

/*
 * Implement a compiler for QL to HTML and Javascript
 *
 * - assume the form is type- and name-correct
 * - separate the compiler in two parts form2html and form2js producing 2 files
 * - use string templates to generate Javascript
 * - use the HTMLElement type and the `str writeHTMLString(HTMLElement x)` function to format to string
 * - use any client web framework (e.g. Vue, React, jQuery, whatever) you like for event handling
 * - map booleans to checkboxes, strings to textfields, ints to numeric text fields
 * - be sure to generate uneditable widgets for computed questions!
 * - if needed, use the name analysis to link uses to definitions
 */

void compile(AForm f) {
  writeFile(f.src[extension="js"].top, form2js(f));
  writeFile(f.src[extension="html"].top, writeHTMLString(form2html(f)));
}

HTMLElement form2html(AForm f) {
  AForm flattenedForm = flatten(f);
  return html([aid2headerTitle(f), aid2title(flattenedForm.name), body([form2body(flattenedForm)])]);
}

HTMLElement aid2headerTitle(AForm f) {
  return head([title([\data(f.name.name)]), script([], src = f.src[extension="js"].top.file)]);
}

HTMLElement aid2title(AId id) {
  return body([h1([\data(id.name + " Form")]), button([text(" Press To Start! ")], \id = "startButton")]);
}

HTMLElement form2body(AForm f) {
  list[HTMLElement] elements = [];
  for(AQuestion q <- f.questions) {
    elements = elements + question2html(q);
  }
  return form([e | e <- elements]);
}

list[HTMLElement] question2html(AQuestion q) {
  list[HTMLElement] elements = [];
  switch(q) {
    case question(AStr qText, AId var, AType t): {
      elements += label([text(qText.s)]);
      elements += br();
      elements += input(\type = type2HtmlType(t), \name = var.name, \id = var.name, disabled = "" );
      elements += br();
    }
    case computedQuestion(AStr qText, AId var, AType t, AExpr e): {
      elements += label([text(qText.s), br()]);
      elements += input(\type = type2HtmlType(t), \name = var.name, \id = var.name, disabled = "" );
      elements += br();
    }
    case ifthen(_, list[AQuestion] qs): {
      for(AQuestion q <- qs) {
        elements += question2html(q);
      }
    }
    // case ifthenelse(_, list[AQuestion] qs1, list[AQuestion] qs2): {
    //   elements += html([label("ifthenelse"), html([question2html(q) | q <- qs1]), html([question2html(q) | q <- qs2])]);
    // }
    default: elements += [];
  }
  return elements;
}

str type2HtmlType(AType t) {
  switch (t) {
    case intType(): return "number";
    case boolType(): return "checkbox";
    case stringType(): return "text";
    default: return "";
  }
}

str form2js(AForm f) {
  AForm flattenedForm = flatten(f);
  return "window.onload = function() {
         '  var button = document.getElementById(\"startButton\");
         '  button.addEventListener(\"click\", handleEvent);
         '  <questions2variables(flattenedForm.questions)>
         '  function handleEvent(event) {
         '    console.log(\"heree \" + event.target.id); // event.target.id = event.target.value;
         '    <questions2formulasjs(flattenedForm.questions)>
         '  }
         '};
         ";
}

str questions2variables(list[AQuestion] qs) {
  return "<for(AQuestion q <- qs) { ><question2Variable(q)>
         '<}>";
}

str question2Variable(AQuestion q) {
  switch(q) {
    case question(_, AId var, AType t): {
      return "let <var.name> = <atype2initValue(t)>;
             'var <var.name>Id = document.getElementById(\"<var.name>\");
             'var <var.name>Cond = true;
             '<var.name>Id.addEventListener(\"change\", handleEvent);
             ";
    }
    case computedQuestion(_, AId var, AType t, _): {
      return "let <var.name> = <atype2initValue(t)>;
             'var <var.name>Id = document.getElementById(\"<var.name>\");
             'var <var.name>Cond = true;
             '<var.name>Id.addEventListener(\"change\", handleEvent);
             ";
    }
    case ifthen(_, list[AQuestion] qs): {
      return "<questions2variables(qs)>";
    }
    case ifthenelse(_, list[AQuestion] qs1, list[AQuestion] qs2): {
      return "<questions2variables(qs1)>
             '<questions2variables(qs2)>
             ";
    }
    default: return "";
  }
}

str questions2formulasjs(list[AQuestion] qs) {
  return "<for(AQuestion q <- qs) { ><question2Formulajs(q)>
         '<}>";
}

str question2Formulajs(AQuestion q) {
  switch(q) {
    case question(_, AId var, AType t): {
      return "if (event.target.id === \"<var.name>\") {
             '  <type2Str(var, t)>
             '}
             "; 
    }
    case computedQuestion(_ , AId var, AType t, AExpr expr): {
      return "
             '<var.name> = <expr2formula(expr)>;
             '<var.name>Id.value = <var.name>;";
    }
    case ifthen(AExpr expr, list[AQuestion] qs): {
      return "<qs[0].var.name>Cond = <expr2formula(expr)>;
             'document.getElementById(\"<qs[0].var.name>\").disabled = !<qs[0].var.name>Cond;
             '<for(AQuestion q <- qs) { ><question2Formulajs(q)><}>";
    }
    case ifthenelse(_, list[AQuestion] qs1, list[AQuestion] qs2): {
      return "<for(AQuestion q <- qs1) { ><question2Formulajs(q)>
             '<}>
             '<for(AQuestion q <- qs2) { ><question2Formulajs(q)>
             '<}>";
    }
    default: return "";
  }
}

str type2Str(AId id, AType t) {
  switch (t) {
    case intType(): return "<id.name> = event.target.value;
                           '<id.name>Id.value = <id.name>;";
    case boolType(): return "<id.name> = event.target.checked;
                            '<id.name>Id.checked = <id.name>;";
    case stringType(): return "<id.name> = event.target.value;
                              '<id.name>Id.value = <id.name>;";
    default: return "";
  }
}

str expr2formula(AExpr expr) {
  switch (expr) {
    case ref(AId id): return id.name;
    case integer(AInt i): return "parseInt(<i.i>)";
    case boolean(ABool b): return "<b.b>";
    case stringy(s): return s.s;
    case add(e1, e2): return expr2formula(e1) + " + " + expr2formula(e2);
    case sub(e1, e2): return expr2formula(e1) + " - " + expr2formula(e2);
    case mul(e1, e2): return expr2formula(e1) + " * " + expr2formula(e2);
    case div(e1, e2): return expr2formula(e1) + " / " + expr2formula(e2);
    case min(e): "-(" + expr2formula(e) + ")";
    case and(e1, e2): return expr2formula(e1) + " && " + expr2formula(e2);
    case or(e1, e2): return expr2formula(e1) + " || " + expr2formula(e2);
    case not(e): return "!(" + expr2formula(e) + ")";
    case eql(e1, e2): return expr2formula(e1) + " == " + expr2formula(e2);
    case neq(e1, e2): return expr2formula(e1) + " != " + expr2formula(e2);
    case lt(e1, e2): return expr2formula(e1) + " \< " + expr2formula(e2);
    case gt(e1, e2): return expr2formula(e1) + " \> " + expr2formula(e2);
    case leq(e1, e2): return expr2formula(e1) + " \<= " + expr2formula(e2);
    case geq(e1, e2): return expr2formula(e1) + " \>= " + expr2formula(e2);
    default: return "";
  }
  return "";
}

str atype2initValue(AType t) {
  switch (t) {
    case intType(): return "0";
    case boolType(): return "false";
    case stringType(): return "\"\"";
    default: return "";
  }
}

str astr2str(AStr s) {
  return s.s;
}