include "Lang.dfy"
include "Print.dfy"

function method digitToString(n: nat): string
  requires 0 <= n <= 9
{
  var digits := ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];
  digits[n]
}


function method natToString(n: nat): string
{
  if (n <= 9) then digitToString(n)
  else natToString(n/10) + digitToString(n % 10)
}


class Havocer
{
  var nextId: nat;
  var newVars: seq<(nat, string)>;

  const havocPrefix: string;

  constructor(havocPrefix: string)
  {
    nextId := 0;
    // TODO: make sure to avoid clashes with existing variables by setting this to something unused
    // by concrete programs.
    this.havocPrefix := havocPrefix;
  }

  method freshId(rhs: string) returns (id: nat)
    modifies this
  {
    id := nextId;
    newVars := newVars + [(id, rhs)];
    nextId := nextId + 1;
  }

  function method varName(n: nat): string
  {
    havocPrefix + natToString(n)
  }

  // AssocGet(AssocGet(objs, addr).val.locals, "x")
  method havocLocals(locals: List<Pair<Var, Value>>, immuts: List<Var>, addr: Addr)
    returns (newLocals: List<Pair<Var, Value>>)
    modifies this
    decreases locals
  {
    match locals {
      case LNil => { newLocals := LNil(); }
      case Cons(Pair(name, val), locals') => {
        var rest := havocLocals(locals', immuts, addr);
        if InList(immuts, name) {
          newLocals := Cons(Pair(name, val), rest);

        } else {
          var next := freshId("AssocGet(AssocGet({objs}, " + natToString(addr) + ").val.locals, \\\"" + name + "\\\").val");
          newLocals := Cons(Pair(name, Internal(varName(next))), rest);
        }
      }
    }
  }

  method havocObj(obj: Object, addr: Addr) returns (newObj: Object)
    modifies this
  {
    var newLocals := havocLocals(obj.locals, obj.immutables, addr);
    newObj := obj.(locals := newLocals);
  }

  method havocObjs(objs: ObjList) returns (newObjs: ObjList)
    modifies this
  {
    match objs {
      case LNil => { newObjs := LNil(); }
      case Cons(Pair(addr, obj), objs') => {
        var newObj := havocObj(obj, addr);
        var rest := havocObjs(objs');
        newObjs := Cons(Pair(addr, newObj), rest);
      }
    }
  }

  method VarsToString(vars: seq<(nat, string)>) returns (varNames: seq<string>)
  {
    if vars == [] {
      varNames := [];
    } else {
      var i: int := |vars| - 1;
      varNames := [];
      while i >= 0
      invariant -1 <= i < |vars|
      decreases i
      {
        var (varId, varVal) := vars[i];
        varNames := ["(\"" + varName(varId) + "\", \"" + varVal + "\")"] + varNames;
        i := i - 1;
      }
    }
  }

  method printHavocData(stuff: (Value, Context))
    modifies this
  {
    var objs := havocObjs(stuff.1.objs);
    // TODO: use a proper output format here in case this optimization turns out to be useful
    var newVarNames := VarsToString(newVars);
    print quoteObjs(objs), " @@@ ", newVarNames;
  }
}
