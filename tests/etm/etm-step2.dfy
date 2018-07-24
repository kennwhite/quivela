include "../../src/backend/dafny/Lang.dfy"
include "../../src/backend/dafny/Indistinguishable.dfy"
include "../../src/backend/dafny/Refl.dfy"
include "../../src/backend/dafny/Rules.dfy"
const True := true; const False := false;

function invariant0(ctx1: Context, ctx2: Context, addr1: Addr, addr2: Addr): bool
{
  var ctx1' := ctx1.(scope := Cons(Pair("_lhs", Ref(addr1)), ctx1.scope));
  var ctx2' := ctx2.(scope := Cons(Pair("_rhs", Ref(addr2)), ctx2.scope));
  var (lhs', _) := Eval(ECVar(EVar("_lhs"), "e", EConst(Nil())), ctx1', FUEL);
  var (rhs', _) := Eval(ECVar(EVar("_rhs"), "e", EConst(Nil())), ctx2', FUEL);
  lhs' == rhs'
}

function invariant1(ctx1: Context, ctx2: Context, addr1: Addr, addr2: Addr): bool
{
  var ctx1' := ctx1.(scope := Cons(Pair("_lhs", Ref(addr1)), ctx1.scope));
  var ctx2' := ctx2.(scope := Cons(Pair("_rhs", Ref(addr2)), ctx2.scope));
  var (lhs', _) := Eval(ECVar(EVar("_lhs"), "mac", EConst(Nil())), ctx1', FUEL);
  var (rhs', _) := Eval(ECVar(EVar("_rhs"), "mac", EConst(Nil())), ctx2', FUEL);
  lhs' == rhs'
}

function invariant2(ctx1: Context, ctx2: Context, addr1: Addr, addr2: Addr): bool
{
  var ctx1' := ctx1.(scope := Cons(Pair("_lhs", Ref(addr1)), ctx1.scope));
  var ctx2' := ctx2.(scope := Cons(Pair("_rhs", Ref(addr2)), ctx2.scope));
  var (lhs', _) := Eval(ECVar(ECVar(EVar("_lhs"), "mac", EConst(Nil())), "tg", EConst(Nil())), ctx1', FUEL);
  var (rhs', _) := Eval(ECVar(ECVar(EVar("_rhs"), "mac", EConst(Nil())), "tg", EConst(Nil())), ctx2', FUEL);
  lhs' == rhs'
}

function invariant3(ctx1: Context, ctx2: Context, addr1: Addr, addr2: Addr): bool
{
  var ctx1' := ctx1.(scope := Cons(Pair("_lhs", Ref(addr1)), ctx1.scope));
  var ctx2' := ctx2.(scope := Cons(Pair("_rhs", Ref(addr2)), ctx2.scope));
  var (lhs', _) := Eval(ECVar(ECVar(EVar("_lhs"), "mac", EConst(Nil())), "mac", EConst(Nil())), ctx1', FUEL);
  var (rhs', _) := Eval(ECVar(ECVar(EVar("_rhs"), "mac", EConst(Nil())), "mac", EConst(Nil())), ctx2', FUEL);
  lhs' == rhs'
}

function invariant4(ctx1: Context, ctx2: Context, addr1: Addr, addr2: Addr): bool
{
  invariant0(ctx1, ctx2, addr1, addr2) && invariant1(ctx1, ctx2, addr1, addr2) && invariant2(ctx1, ctx2, addr1, addr2) && invariant3(ctx1, ctx2, addr1, addr2)
}

// Top-level equivalence proof
lemma equivalent0()
  ensures
    var prefix := ESeq(ESeq(ESeq(ESeq(ESeq(ESeq(ESeq(ESeq(EMethod("MacI", Cons("mac", LNil), ENew(Cons(Init("mac", EConst(Nil()), true), Cons(Init("tg", EConst(Int(0)), false), LNil)), ESeq(EMethod("tag", Cons("m", LNil), EAssign(ECVar(EConst(Nil()), "tg", EVar("m")), ECall(EVar("mac"), "tag", Cons(EVar("m"), LNil)))), EMethod("verify", Cons("m", Cons("t", LNil)), ECall(EConst(Nil()), "&", Cons(EVar("t"), Cons(ECall(EConst(Nil()), "==", Cons(ECVar(EConst(Nil()), "tg", EVar("m")), Cons(EVar("t"), LNil))), LNil))))))), EMethod("Enc", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("d", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), Cons(ECall(EConst(Nil()), "!", Cons(ECVar(EConst(Nil()), "d", EVar("c")), LNil)), LNil))), Cons(EAssign(ECVar(EConst(Nil()), "d", EVar("c")), EVar("m")), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("c", LNil), ECall(EVar("e"), "dec", Cons(EVar("c"), LNil))))))), EMethod("CpaC", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("h", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), Cons(EAssign(ECVar(EConst(Nil()), "h", EVar("c")), EConst(Int(1))), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("c", LNil), ECall(EConst(Nil()), "&", Cons(ECVar(EConst(Nil()), "h", EVar("c")), Cons(ECall(EVar("e"), "dec", Cons(EVar("c"), LNil)), LNil)))))))), EMethod("CpaI", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("d", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(ECall(EConst(Nil()), "zero", Cons(EVar("m"), LNil)), LNil))), Cons(EAssign(ECVar(EConst(Nil()), "d", EVar("c")), EVar("m")), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("c", LNil), ECVar(EConst(Nil()), "d", EVar("c"))))))), EMethod("AeadI", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("d", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(EVar("a"), Cons(ECall(EConst(Nil()), "zero", Cons(EVar("m"), LNil)), LNil)))), Cons(EAssign(ECVar(EConst(Nil()), "d", ETuple(Cons(EVar("a"), Cons(EVar("c"), LNil)))), EVar("m")), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ECVar(EConst(Nil()), "d", ETuple(Cons(EVar("a"), Cons(EVar("c"), LNil))))))))), EMethod("EtM", Cons("e", Cons("mac", LNil)), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("mac", EConst(Nil()), true), LNil)), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EAssign(EVar("em"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), LNil))), Cons(EAssign(EVar("t"), ECall(EVar("mac"), "tag", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), LNil))), LNil))), Cons(ETuple(Cons(EVar("em"), Cons(EVar("t"), LNil))), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ESeq(EAssign(EVar("em"), ECVar(EVar("c"), "get", EConst(Int(0)))), ESeq(EAssign(EVar("t"), ECVar(EVar("c"), "get", EConst(Int(1)))), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("c"), Cons(ECall(EVar("mac"), "verify", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), Cons(EVar("t"), LNil))), LNil))), Cons(ECall(EVar("e"), "dec", Cons(EVar("em"), LNil)), LNil)))))))))), EMethod("zero", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EConst(Int(0)), LNil))))), EAssign(EVar("_e"), ECall(EConst(Nil()), "adversary", LNil))), EAssign(EVar("_mac"), ECall(EConst(Nil()), "adversary", LNil)));
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ENew(Cons(Init("e", EVar("_e"), true), Cons(Init("mac", ECall(EConst(Nil()), "MacI", Cons(EVar("_mac"), LNil)), true), LNil)), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EAssign(EVar("em"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), LNil))), Cons(EAssign(EVar("t"), ECall(EVar("mac"), "tag", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), LNil))), LNil))), Cons(ETuple(Cons(EVar("em"), Cons(EVar("t"), LNil))), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ESeq(EAssign(EVar("em"), ECVar(EVar("c"), "get", EConst(Int(0)))), ESeq(EAssign(EVar("t"), ECVar(EVar("c"), "get", EConst(Int(1)))), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("c"), Cons(ECall(EVar("mac"), "verify", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), Cons(EVar("t"), LNil))), LNil))), Cons(ECall(EVar("e"), "dec", Cons(EVar("em"), LNil)), LNil))))))));
    var rhs := ENew(Cons(Init("e", EVar("_e"), true), Cons(Init("mac", ECall(EConst(Nil()), "MacI", Cons(EVar("_mac"), LNil)), true), Cons(Init("cpa", ENew(Cons(Init("e", EVar("_e"), true), LNil), ESeq(EMethod("enc", Cons("m", LNil), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), EMethod("dec", Cons("c", LNil), ECall(EVar("e"), "dec", Cons(EVar("c"), LNil))))), true), LNil))), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EAssign(EVar("em"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), LNil))), Cons(EAssign(EVar("t"), ECall(EVar("mac"), "tag", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), LNil))), LNil))), Cons(ETuple(Cons(EVar("em"), Cons(EVar("t"), LNil))), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ESeq(EAssign(EVar("em"), ECVar(EVar("c"), "get", EConst(Int(0)))), ESeq(EAssign(EVar("t"), ECVar(EVar("c"), "get", EConst(Int(1)))), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("c"), Cons(ECall(EVar("mac"), "verify", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), Cons(EVar("t"), LNil))), LNil))), Cons(ECall(EVar("e"), "dec", Cons(EVar("em"), LNil)), LNil))))))));
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    Equivalent_AllMethods(ctx1, ctx2, addr1, addr2, invariant4)
{
    var prefix := ESeq(ESeq(ESeq(ESeq(ESeq(ESeq(ESeq(ESeq(EMethod("MacI", Cons("mac", LNil), ENew(Cons(Init("mac", EConst(Nil()), true), Cons(Init("tg", EConst(Int(0)), false), LNil)), ESeq(EMethod("tag", Cons("m", LNil), EAssign(ECVar(EConst(Nil()), "tg", EVar("m")), ECall(EVar("mac"), "tag", Cons(EVar("m"), LNil)))), EMethod("verify", Cons("m", Cons("t", LNil)), ECall(EConst(Nil()), "&", Cons(EVar("t"), Cons(ECall(EConst(Nil()), "==", Cons(ECVar(EConst(Nil()), "tg", EVar("m")), Cons(EVar("t"), LNil))), LNil))))))), EMethod("Enc", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("d", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), Cons(ECall(EConst(Nil()), "!", Cons(ECVar(EConst(Nil()), "d", EVar("c")), LNil)), LNil))), Cons(EAssign(ECVar(EConst(Nil()), "d", EVar("c")), EVar("m")), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("c", LNil), ECall(EVar("e"), "dec", Cons(EVar("c"), LNil))))))), EMethod("CpaC", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("h", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), Cons(EAssign(ECVar(EConst(Nil()), "h", EVar("c")), EConst(Int(1))), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("c", LNil), ECall(EConst(Nil()), "&", Cons(ECVar(EConst(Nil()), "h", EVar("c")), Cons(ECall(EVar("e"), "dec", Cons(EVar("c"), LNil)), LNil)))))))), EMethod("CpaI", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("d", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(ECall(EConst(Nil()), "zero", Cons(EVar("m"), LNil)), LNil))), Cons(EAssign(ECVar(EConst(Nil()), "d", EVar("c")), EVar("m")), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("c", LNil), ECVar(EConst(Nil()), "d", EVar("c"))))))), EMethod("AeadI", Cons("e", LNil), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("d", EConst(Int(0)), false), LNil)), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EAssign(EVar("c"), ECall(EVar("e"), "enc", Cons(EVar("a"), Cons(ECall(EConst(Nil()), "zero", Cons(EVar("m"), LNil)), LNil)))), Cons(EAssign(ECVar(EConst(Nil()), "d", ETuple(Cons(EVar("a"), Cons(EVar("c"), LNil)))), EVar("m")), LNil))), Cons(EVar("c"), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ECVar(EConst(Nil()), "d", ETuple(Cons(EVar("a"), Cons(EVar("c"), LNil))))))))), EMethod("EtM", Cons("e", Cons("mac", LNil)), ENew(Cons(Init("e", EConst(Nil()), true), Cons(Init("mac", EConst(Nil()), true), LNil)), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EAssign(EVar("em"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), LNil))), Cons(EAssign(EVar("t"), ECall(EVar("mac"), "tag", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), LNil))), LNil))), Cons(ETuple(Cons(EVar("em"), Cons(EVar("t"), LNil))), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ESeq(EAssign(EVar("em"), ECVar(EVar("c"), "get", EConst(Int(0)))), ESeq(EAssign(EVar("t"), ECVar(EVar("c"), "get", EConst(Int(1)))), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("c"), Cons(ECall(EVar("mac"), "verify", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), Cons(EVar("t"), LNil))), LNil))), Cons(ECall(EVar("e"), "dec", Cons(EVar("em"), LNil)), LNil)))))))))), EMethod("zero", Cons("m", LNil), ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EConst(Int(0)), LNil))))), EAssign(EVar("_e"), ECall(EConst(Nil()), "adversary", LNil))), EAssign(EVar("_mac"), ECall(EConst(Nil()), "adversary", LNil)));
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ENew(Cons(Init("e", EVar("_e"), true), Cons(Init("mac", ECall(EConst(Nil()), "MacI", Cons(EVar("_mac"), LNil)), true), LNil)), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EAssign(EVar("em"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), LNil))), Cons(EAssign(EVar("t"), ECall(EVar("mac"), "tag", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), LNil))), LNil))), Cons(ETuple(Cons(EVar("em"), Cons(EVar("t"), LNil))), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ESeq(EAssign(EVar("em"), ECVar(EVar("c"), "get", EConst(Int(0)))), ESeq(EAssign(EVar("t"), ECVar(EVar("c"), "get", EConst(Int(1)))), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("c"), Cons(ECall(EVar("mac"), "verify", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), Cons(EVar("t"), LNil))), LNil))), Cons(ECall(EVar("e"), "dec", Cons(EVar("em"), LNil)), LNil))))))));
    var rhs := ENew(Cons(Init("e", EVar("_e"), true), Cons(Init("mac", ECall(EConst(Nil()), "MacI", Cons(EVar("_mac"), LNil)), true), Cons(Init("cpa", ENew(Cons(Init("e", EVar("_e"), true), LNil), ESeq(EMethod("enc", Cons("m", LNil), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), EMethod("dec", Cons("c", LNil), ECall(EVar("e"), "dec", Cons(EVar("c"), LNil))))), true), LNil))), ESeq(EMethod("enc", Cons("a", Cons("m", LNil)), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("m"), Cons(EAssign(EVar("em"), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), LNil))), Cons(EAssign(EVar("t"), ECall(EVar("mac"), "tag", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), LNil))), LNil))), Cons(ETuple(Cons(EVar("em"), Cons(EVar("t"), LNil))), LNil)))), EMethod("dec", Cons("a", Cons("c", LNil)), ESeq(EAssign(EVar("em"), ECVar(EVar("c"), "get", EConst(Int(0)))), ESeq(EAssign(EVar("t"), ECVar(EVar("c"), "get", EConst(Int(1)))), ECall(EConst(Nil()), "&", Cons(ECall(EConst(Nil()), "&", Cons(EVar("c"), Cons(ECall(EVar("mac"), "verify", Cons(ETuple(Cons(EVar("a"), Cons(EVar("em"), LNil))), Cons(EVar("t"), LNil))), LNil))), Cons(ECall(EVar("e"), "dec", Cons(EVar("em"), LNil)), LNil))))))));
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);

    var newField := Init("cpa", ENew(Cons(Init("e", EVar("_e"), true), LNil), ESeq(EMethod("enc", Cons("m", LNil), ECall(EVar("e"), "enc", Cons(EVar("m"), LNil))), EMethod("dec", Cons("c", LNil), ECall(EVar("e"), "dec", Cons(EVar("c"), LNil))))), true);

    assert NoExternalEffects(newField.val) by {
      forall x: Var ensures NoExternalEffects(EVar(x)) { EVar_NoExternalEffects(x); }
      assert OnlyMethodDefinitions(newField.val.body);
      ENew_NoExternalEffects(newField.val.locals, newField.val.body);
    }
    assert AssocGet(ctx1.methods, addr1.addr) == AssocGet(ctx2.methods, addr2.addr);
    assert newField.name == "cpa";
    assert UnusedIn(newField.name, lhs.body) by {
      // evaluates to true; tackle this later by simplification step in Dafny
      // see etm-step2-eval.dfy
      assume false;
    }
    EquivalentAddNewField(prefix, lhs.locals, lhs.body, newField, invariant4, 2);

}

method Main()
{
  equivalent0();
}
