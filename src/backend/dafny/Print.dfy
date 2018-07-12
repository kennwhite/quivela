// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// 
// Licensed under the Apache License, Version 2.0 (the "License").
// You may not use this file except in compliance with the License.
// A copy of the License is located at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// or in the "license" file accompanying this file. This file is distributed 
// on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
// express or implied. See the License for the specific language governing 
// permissions and limitations under the License.

include "Lang.dfy"

/* 
This file is for printing out the result of calls to Eval(..) in a way
that's also a valid Dafny term. This allows evaluating such calls
ahead of time before the actual verification.

The builtin `print` of Dafny /almost/ prints out something that can be
passed back into Dafny, except that strings are printed without quotes.
We only need to wrap each string in an extra pair of quotes to fix this. 

Another issue is that `print` prints `true` and `false` as `True` and
`False` instead, which can be addressed by `const True := true;`, which
we don't address here. */

/* FIXME: In the long run, we should probably define a general-purpose "fmap"
operation over these structures, instead of the customized one
for printing we define here. */

function method quoteScope(scope: Scope): Scope
{
  quoteList(quotePair(quoteVar, quoteValue))(scope)
}

function method quoteVarSet(xs: set<Var>): set<Var>
{
  set x: Var | x in xs :: quoteVar(x)
}

function method quoteVar(x: Var): Var
{
  "\"" +  x + "\""
}

function method quoteValue(v: Value): Value
{
  v
}

function method quoteEnv(env: Env): Env
{
  quoteList(quotePair(quoteVar, quoteValue))(env)
} 

function method quoteListAux<T>(quoteElt: T -> T, xs : List<T>): List<T>
{
  if (xs.LNil?) then LNil() else Cons(quoteElt(xs.car), 
                                      quoteListAux(quoteElt, xs.cdr))
}

// We use curried functions for quoteList, quotePair, etc. to
// make it easier to build up quoting functions for larger structures.
function method quoteList<T>(quoteElt: T -> T): List<T> -> List<T>
{
  (xs: List<T>) => quoteListAux(quoteElt, xs)
}

function method quoteObject(obj: Object): Object
{
  obj.(locals := quoteEnv(obj.locals), 
       immutables := quoteVarSet(obj.immutables))
}

function method quotePair<S, T>(quoteS: S -> S, quoteT: T -> T): Pair<S, T> -> Pair<S, T>
{
  (pair: Pair<S, T>) => Pair(quoteS(pair.car), quoteT(pair.cdr))
}

function method quoteAddr(a: Addr): Addr { a }

function method id<T>(x: T): T
{ 
  x 
}

function method quoteObjs(objs: ObjList): ObjList
{
  quoteList(quotePair(id, quoteObject))(objs)
}

function method quoteExprList(es: List<Expr>): List<Expr>
{
  // can't reuse quoteList here due to mutual recursion
  match es
  case LNil => LNil()
  case Cons(x, xs') => Cons(quoteExpr(x), quoteExprList(xs'))
}

function method quoteInit(init: Init): Init
{
  match init
  case Init(name, val, immut) =>
    Init(quoteVar(name), quoteExpr(val), immut)
}

function method quoteInits(inits: List<Init>): List<Init>
{
  match inits
  case LNil => LNil()
  case Cons(init, inits') => Cons(quoteInit(init), quoteInits(inits'))
}

function method quoteExpr(e: Expr): Expr
{
  match e
  case EVar(x) => EVar(quoteVar(x))
  case EConst(v) => EConst(quoteValue(v))
  case ETuple(es) => ETuple(quoteExprList(es))
  case ESeq(e1, e2) => ESeq(quoteExpr(e1), quoteExpr(e2))
  case ECVar(obj, name, idx) => 
    ECVar(quoteExpr(obj), quoteVar(name), quoteExpr(idx))
  case EITE(cond, thn, els) =>
    EITE(quoteExpr(cond), quoteExpr(thn), quoteExpr(els))
  case ENew(locals, body) =>
    ENew(quoteInits(locals), quoteExpr(body))
  case EMethod(name, args, body) =>
    EMethod(quoteVar(name), quoteList(quoteVar)(args), quoteExpr(body))
  case EAssign(lhs, rhs) => EAssign(quoteExpr(lhs), quoteExpr(rhs))
  case ECall(cobj, cname, cargs) =>
    ECall(quoteExpr(cobj), quoteVar(cname), quoteExprList(cargs))
  case ENop() => ENop()
}

function method quoteMethod(methd: Method): Method
{
  methd.(name := quoteVar(methd.name), 
         args := quoteList(quoteVar)(methd.args),
         body := quoteExpr(methd.body))
}

function method quoteMethods(methods: MethodMap): MethodMap
{
  quoteList(quotePair(id, quoteList(quotePair(quoteVar, quoteMethod))))
           (methods)
}

function method quoteContext(ctx: Context): Context
{
  ctx.(scope := quoteScope(ctx.scope), objs := quoteObjs(ctx.objs), methods := quoteMethods(ctx.methods))
}

method printContext(ctx: Context)
{
  print quoteContext(ctx);
}
