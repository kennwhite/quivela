include "Rules.dfy"


/*
Currently we only handle a very limited form of inlining methods, we only
allow replacing calls to global methods or methods of an immutable local field
of the surrounding New().
*/

datatype MethodCall = GlobalMethod(mtdName: Var) | FieldMethod(fieldName: Var, methodName: Var)

function method Find<T>(pred: T -> bool, xs: List<T>): Option<T>
  decreases xs
  ensures var res := Find(pred, xs);
  if res.Some? then pred(res.val) else ListAll((x : T) => !pred(x), xs)
{
  match xs
    case LNil => None
    case Cons(x, xs') => if pred(x) then Some(x) else Find(pred, xs')
}

function method SubstVarInList(x: Var, substBy: Expr, es: List<Expr>): List<Expr>
  decreases es
{
  match es
    case LNil => LNil
    case Cons(e, es') => Cons(SubstVar(x, substBy, e), SubstVarInList(x, substBy, es'))
}

function method SubstInLocs(x: Var, substBy: Expr, locs: List<Init>): List<Init>
  decreases locs
{
  match locs
    case LNil => LNil
    case Cons(loc, locs') =>
      if loc.name == x then Cons(loc, locs')
      else Cons(loc.(val := SubstVar(x, substBy, loc.val)), SubstInLocs(x, substBy, locs'))
}

function method SubstVar(x: Var, substBy: Expr, e: Expr): Expr
  decreases e
{
  match e
    case EVar(y) => if x == y then substBy else e
    case EConst(v) => e
    case ETuple(vals) => ETuple(SubstVarInList(x, substBy, vals))
    case EMethod(name, args, body) => if Find((arg: Var) => arg == x, args).Some? then e else SubstVar(x, substBy, body)
    case ENop() => e
    case EITE(cnd, thn, els) => EITE(SubstVar(x, substBy, cnd), SubstVar(x, substBy, thn), SubstVar(x, substBy, thn))
    case ECall(obj, name, args) =>
      ECall(SubstVar(x, substBy, obj), name, SubstVarInList(x, substBy, args))
    case ENew(locs, body) =>
      var locs' := SubstInLocs(x, substBy, locs);
      var body' := if Find((loc: Init) => loc.name == x, locs).Some? then body else SubstVar(x, substBy, body);
      ENew(locs', body')
    case EAssign(lhs, rhs) => EAssign(SubstVar(x, substBy, lhs), SubstVar(x, substBy, rhs))
    case ECVar(obj, name, idx) => ECVar(SubstVar(x, substBy, obj), name, SubstVar(x, substBy, idx))
    case ESeq(e1, e2) => ESeq(SubstVar(x, substBy, e1), SubstVar(x, substBy, e2))
}

function method SubstList(substs: List<(Var, Expr)>, e: Expr): Expr
{
  match substs
    case LNil => e
    case Cons((x, subst), substs') => SubstList(substs', SubstVar(x, subst, e))
}

function method Min(n: nat, m: nat): nat
  ensures Min(n, m) <= n && Min(n, m) <= m && (Min(n, m) == n || Min(n, m) == m)
{
  if (n <= m) then n else m
}

function method Zip<T, S>(xs: List<T>, ys: List<S>): List<(T, S)>
  ensures Length(Zip(xs, ys)) == Min(Length(xs), Length(ys))
{
  match xs
    case LNil => LNil
    case Cons(x, xs') =>
      (match ys
         case LNil => LNil
         case Cons(y, ys') => Cons((x, y), Zip(xs', ys')))
}


// TODO
function method SubstArgs(mtd: Expr, args: List<Expr>): Expr
  requires mtd.EMethod? // && Length(mtd.args) == Length(args)
{
  SubstList(Zip(mtd.args, args), mtd.body)
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
      if init.name == fieldName && init.val.ENew? && init.immutable
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

function method MapList<S, T>(f: S -> T, xs: List<S>): List<T>
{
  match xs
    case LNil => LNil
    case Cons(x, xs') => Cons(f(x), MapList(f, xs'))
}

function method Fold<S, T>(op: (S, T) -> T, init: T, xs: List<S>): T
{
  match xs
    case LNil => init
    case Cons(x, xs') => op(x, Fold(op, init, xs'))
}

function method FreeVarsInList(es: List<Expr>, bound: set<Var>): set<Var>
{
  match es
    case LNil => {}
    case Cons(e, es') => FreeVars'(e, bound) + FreeVarsInList(es', bound)
}

function method FreeVarsInLocs(locs: List<Init>, bound: set<Var>): set<Var>
{
  match locs
    case LNil => {}
    case Cons(loc, locs') =>
      FreeVars'(loc.val, bound + {loc.name}) +
      FreeVarsInLocs(locs', bound + {loc.name})
}

function method FreeVars'(e: Expr, bound: set<Var>): set<Var>
{
  match e
    case EVar(x) => if x in bound then {} else {x}
    case ETuple(vals) => FreeVarsInList(vals, bound)
    case ENop => {}
    case EConst(v) => {}
    case EITE(cnd, thn, els) => FreeVars'(cnd, bound) + FreeVars'(thn, bound) + FreeVars'(els, bound)
    case ESeq(e1, e2) => FreeVars'(e1, bound) + FreeVars'(e2, bound)
    case EMethod(name, args, body) =>
      FreeVars'(body, bound + Fold((x: Var, xs: set<Var>) => {x} + xs, {}, args))
    case ECall(obj, name, args) => FreeVars'(obj, bound) + FreeVarsInList(args, bound)
    case ENew(locals, body) =>
      var localVars := FreeVarsInLocs(locals, bound);
      var boundLocs := Fold((loc: Init, fvs: set<Var>) => {loc.name} + fvs, {}, locals);
      localVars + FreeVars'(body, bound + boundLocs)
    case EAssign(lhs, rhs) => FreeVars'(lhs, bound) + FreeVars'(rhs, bound)
    case ECVar(obj, name, idx) => FreeVars'(obj, bound) + FreeVars'(idx, bound)
}

function method FreeVars(e: Expr): set<Var>
{
  FreeVars'(e, {})
}

function method GlobalVars(e: Expr): set<Var>
{
  if e.EAssign? && e.lhs.EVar? then {e.lhs.name}
  else if e.ESeq? then GlobalVars(e.e1) + GlobalVars(e.e2)
  else {}
}

lemma InlineMethodEquivalent(prefix: Expr, lhs: Expr, Inv: ContextEquivalence,
  call: MethodCall)
  requires
  var mtd := FindCalledMethod(call, ESeq(prefix, lhs));
    mtd.Some? &&
    FreeVars(mtd.val) * FreeVars(lhs) == {} &&
    FreeVars(mtd.val) <= GlobalVars(prefix)
    // This is more restrictive than it could be, since free variables
    // in the function could also be bound to the same object as in each
    // call site, but that'd be much trickier to check.
  ensures
  var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
  var rhs := InlineMethod(lhs, call, FindCalledMethod(call, ESeq(prefix, lhs)).val);
  Equivalent(lhs, rhs, ctxp, Inv)
{ assume false; }
