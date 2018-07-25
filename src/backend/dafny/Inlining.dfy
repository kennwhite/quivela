include "Rules.dfy"


/*
Currently we only handle a very limited form of inlining methods, we only
allow replacing calls to global methods or methods of an immutable local field
of the surrounding New().
*/

datatype MethodCall = GlobalMethod(mtdName: Var) | FieldMethod(fieldName: Var, methodName: Var)

// TODO
function method SubstArgs(mtd: Expr, args: List<Expr>): Expr
  requires mtd.EMethod?
{
  mtd
}

function method InlineInList(es: List<Expr>, call: MethodCall, mtd: Expr): List<Expr>
  decreases es
  requires mtd.EMethod?
{
  match es
    case LNil => LNil
    case Cons(e, es') => Cons(InlineMethod(e, call, mtd), InlineInList(es', call, mtd))
}

function method InlineInLocs(locs: List<Init>, call: MethodCall, mtd: Expr): List<Init>
  decreases locs
  requires mtd.EMethod?
{
  match locs
    case LNil => LNil
    case Cons(loc, locs') => Cons(loc.(val := InlineMethod(loc.val, call, mtd)),
      InlineInLocs(locs', call, mtd))
}

function method InlineMethod(e: Expr, call: MethodCall, mtd: Expr): Expr
  requires mtd.EMethod?
{
  match e
    case EVar(x) => e
    case EConst(v) => e
    case ESeq(e1, e2) => ESeq(InlineMethod(e1, call, mtd), InlineMethod(e2, call, mtd))
    case ENop() => e
    case ETuple(vals) => ETuple(InlineInList(vals, call, mtd))
    case EITE(cnd, thn, els) => EITE(InlineMethod(cnd, call, mtd),
      InlineMethod(thn, call, mtd), InlineMethod(els, call, mtd))
    case EAssign(lhs, rhs) => EAssign(InlineMethod(lhs, call, mtd),
      InlineMethod(rhs, call, mtd))
    case ECVar(obj, name, idx) =>
      ECVar(InlineMethod(obj, call, mtd), name,
      InlineMethod(idx, call, mtd))
    case ENew(locs, body) =>
      ENew(InlineInLocs(locs, call, mtd),
      InlineMethod(body, call, mtd))
    case EMethod(name, params, body) =>
      if call == GlobalMethod(name)
      then e // local method shadows global method call we are looking for
      else EMethod(name, params, InlineMethod(body, call, mtd))
    case ECall(obj, name, args) =>
      var args' := InlineInList(args, call, mtd);
      // this is needlessly specific right now; FIXME: find a nice generalization
      if obj == EConst(Nil) && call == GlobalMethod(name)
      then SubstArgs(mtd, args')
      else if obj.EVar? && call == FieldMethod(obj.name, name)
        then SubstArgs(mtd, args')
        else ECall(InlineMethod(obj, call, mtd), name, args')
}

function method FindMethodByName(mtdName: Var, prog: Expr): Option<Expr>
  ensures var res := FindMethodByName(mtdName, prog);
  res.Some? ==> res.val.EMethod?
{
  if prog.EMethod? && prog.name == mtdName then Some(prog)
  else if !prog.ESeq? then None
  else (match FindMethodByName(mtdName, prog.e1)
    case Some(expr) => Some(expr)
    case None => FindMethodByName(mtdName, prog.e2))
}

function method FindInInits(fieldName: Var, mtdName: Var, locs: List<Init>): Option<Expr>
  ensures var res := FindInInits(fieldName, mtdName, locs);
  res.Some? ==> res.val.EMethod?
{
  match locs
    case LNil => None
    case Cons(init, inits') =>
      if init.name == fieldName && init.val.ENew?
      then FindMethodByName(mtdName, init.val.body)
      else FindInInits(fieldName, mtdName, inits')
}

function method FindCalledMethod(call: MethodCall, prog: Expr): Option<Expr>
  ensures var res := FindCalledMethod(call, prog);
  res.Some? ==> res.val.EMethod?
{
  match call
    case GlobalMethod(name) =>
      FindMethodByName(name, prog)
    case FieldMethod(fieldName, name) =>
      if prog.ENew? then FindInInits(fieldName, name, prog.locals)
      else if !prog.ESeq? then None
      else (match FindCalledMethod(call, prog.e1)
       case Some(expr) => Some(expr)
       case None => FindCalledMethod(call, prog.e2))
}

lemma InlineMethodEquivalent(prefix: Expr, lhs: Expr, Inv: ContextEquivalence,
  call: MethodCall)
  requires
  FindCalledMethod(call, ESeq(prefix, lhs)).Some?
  ensures
  var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
  var rhs := InlineMethod(lhs, call, FindCalledMethod(call, ESeq(prefix, lhs)).val);
  Equivalent(lhs, rhs, ctxp, Inv)
{ assume false; }
