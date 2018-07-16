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

//// This file is a template used for generating equivalence proofs in the Dafny
//// backend.
//// Lines beginning with "////" are removed from the generated code.
//// Lines beginning with "///<" are also removed, and act as delimiters for
//// code generation.
//// Strings that begin with __ and end with __ are replaced during code generation.

///< START method_proof
// Equivalence proof for method `${method}`
lemma ${proof}(objs1: ObjList, objs2: ObjList${args})
  requires
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
  ensures
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    var args: List<Value> := ${cons_args};
    Length(args) == ${arg_count} &&
    ${invariant}(ctx1, ctx2, addr1.addr, addr2.addr) &&
    HavocPostcondition("${method}", args, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
{
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    var args: List<Value> := ${cons_args};
    assert Length(args) == ${arg_count} by { HasLength(args, ${arg_count}); }


    var ctx1' := ctx1.(objs := objs1);
    var ctx2' := ctx2.(objs := objs2);
    var scope1 := BindArguments(GetMethod(ctx1', addr1.addr, "${method}").args, args);
    var scope2 := BindArguments(GetMethod(ctx2', addr2.addr, "${method}").args, args);
${argument_equalities}
    var (retL, ctxL) := CallMethod("${method}", scope1, addr1.addr, ctx1');
    var (retR, ctxR) := CallMethod("${method}", scope2, addr2.addr, ctx2');

${body}
}
///< END method_proof

///< START equivalence_proof
// Top-level equivalence proof
lemma ${proof}()
  ensures
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    Equivalent_AllMethods(ctx1, ctx2, addr1, addr2, ${invariant})
{
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);

    forall objs1: ObjList, objs2: ObjList, m: Var, values: List<Value>
          | HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2) &&
            ValidMethod(ctx1, addr1.addr, m) && ValidMethod(ctx2, addr2.addr, m) &&
            Length(GetMethod(ctx1, addr1.addr, m).args) == Length(GetMethod(ctx2, addr2.addr, m).args) == Length(values)
      ensures HavocPostcondition(m, values, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2) {
${body}
    }

}
///< END equivalence_proof

///< START lemma_use_args
 if (m == "${method}") {
        // Invoke equivalence proof for method `${method}`
        ${proof}(${havoc_args}${args});
      } else
///< END lemma_use_args

///< START lemma_use_noargs
 if (m == "${method}") {
        // Invoke equivalence proof for method `${method}`
        ${proof}(${havoc_args});
      } else
///< END lemma_use_noargs

///< START print_expr
method Main()
{
  var prefix := ${prefix};
  var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
  var lhs := ${exp};
  var (res, ctx) := Eval(lhs, ctxp, FUEL);
  print (res, quoteContext(ctx)), "\n";
}
///< END print_expr

///< START method_proof_compiled
// Equivalence proof for method `${method}`
lemma ${proof}(${havoc_vars}${args})
  requires
    var (addr1, ctx1) := ${result1};
    var (addr2, ctx2) := ${result2};
    var objs1 := ${havoc_objs1};
    var objs2 := ${havoc_objs2};
    HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
  ensures
    var (addr1, ctx1) := ${result1};
    var (addr2, ctx2) := ${result2};
    var objs1 := ${havoc_objs1};
    var objs2 := ${havoc_objs2};
    var args: List<Value> := ${cons_args};
    Length(args) == ${arg_count} &&
    ${invariant}(ctx1, ctx2, addr1.addr, addr2.addr) &&
    HavocPostcondition("${method}", args, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
{
    var (addr1, ctx1) := ${result1};
    var (addr2, ctx2) := ${result2};
    var args: List<Value> := ${cons_args};
    assert Length(args) == ${arg_count} by { HasLength(args, ${arg_count}); }

    var objs1 := ${havoc_objs1};
    var objs2 := ${havoc_objs2};
    var ctx1' := ctx1.(objs := objs1);
    var ctx2' := ctx2.(objs := objs2);
    var scope1 := BindArguments(GetMethod(ctx1', addr1.addr, "${method}").args, args);
    var scope2 := BindArguments(GetMethod(ctx2', addr2.addr, "${method}").args, args);
${argument_equalities}
    var (retL, ctxL) := CallMethod("${method}", scope1, addr1.addr, ctx1');
    var (retR, ctxR) := CallMethod("${method}", scope2, addr2.addr, ctx2');
    // Invoke auxiliary lemmas to help Dafny unfold definitions as much as needed:
${rec_lemmas}

${body}
}
///< END method_proof_compiled

///< START equivalence_proof_compiled
// Top-level equivalence proof
lemma ${proof}()
  ensures
    var (addr1, ctx1) := ${result1};
    var (addr2, ctx2) := ${result2};
    Equivalent_AllMethods(ctx1, ctx2, addr1, addr2, ${invariant})
{

    var (addr1, ctx1) := ${result1};
    var (addr2, ctx2) := ${result2};
    forall m: Var, values: List<Value>, objs1: ObjList, objs2: ObjList
    | HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2) &&
            ValidMethod(ctx1, addr1.addr, m) && ValidMethod(ctx2, addr2.addr, m) &&
            Length(GetMethod(ctx1, addr1.addr, m).args) == Length(GetMethod(ctx2, addr2.addr, m).args) == Length(values)
            ensures HavocPostcondition(m, values, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2) {

              // Assume correctness of more detailed representation of havoced object lists:
${havoc_eqs}
${body}
    }

}
///< END equivalence_proof_compiled

///< START compilation_correctness
lemma ${name}()
  ensures
  var prefix := ${prefix};
  var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
  var unevaled := ${unevaled};
  Eval(unevaled, ctxp, FUEL) == ${compiled}
{ }
///< END compilation_correctness
