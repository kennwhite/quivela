# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# 
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# or in the "license" file accompanying this file. This file is distributed 
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
# express or implied. See the License for the specific language governing 
# permissions and limitations under the License.

import ast
import logging
import os
import re
import string
import subprocess
import tempfile
from functools import reduce
from typing import Any, Dict, List, Tuple

from ..emitter import *
from ..proof import *
from ..analysis import GatherObjectInfo
from ..runtime import Runtime
from ..config import Config
from . import template


DAFNY_INCLUDES = ["Lang.dfy", "Indistinguishable.dfy", "Refl.dfy"]
DAFNY_BACKEND_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../backend/dafny"))

def run_dafny(prog) -> Optional[str]:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".dfy",
                                     delete=False) as f:
        fname = f.name
        for i in DAFNY_INCLUDES + ["Call.dfy", "Print.dfy", "Havoc.dfy", "Util.dfy"]:
            f.write("include \"{}\"\n".format(os.path.join(DAFNY_BACKEND_ROOT, i)))
        f.write(prog)
    rt = Runtime()
    binary = rt._find_executable("dafny")
    proc = subprocess.Popen([binary, "/compile:3", fname],
                            stdout=subprocess.PIPE,
                            universal_newlines=True)
    out, err = proc.communicate()
    lines = out.splitlines()
    logging.info("Dafny process printed:\n{}".format(out))
    if proc.returncode == 0 and len(lines) > 0:
        return lines[-1]
    else:
        return None

def run_expr(prefix, exp) -> Optional[str]:
    tmpl = template.equivalence.get("print_expr")
    prog = tmpl.substitute(prefix=prefix.to_dafny(), exp=exp.to_dafny())
    return run_dafny(prog)

def compute_havoc_data(prefix, expr) -> (str, List[str]):
        prog = '''
method Main()
{{
  var havocer := new Havocer("{prefix}");
  havocer.printHavocData({expr});
}}'''.format(prefix=prefix, expr=expr)
        result = run_dafny(prog).split(" @@@ ") # ugly hack; should write json printer in Dafny instead
        assert len(result) == 2
        p = re.compile(r'Value\.Internal\(([a-zA-Z0-9_]+)\)')
        fixed_obj = p.sub(r'\1', result[0])
        havoc_vars = ast.literal_eval(result[1])
        return (fixed_obj, havoc_vars)

def replace_tuples(target: str, replacements: List[Tuple[str, str]]) -> str:
    """For each tuple (from, to) in replacements, replace all occurrences of from by to in target"""
    return reduce(lambda s, repl: s.replace(repl[0], repl[1]), replacements, target)

class DafnyEmitter(Emitter):
    def __init__(self, includes: List[str]=[]) -> None:
        self.includes = [os.path.join(DAFNY_BACKEND_ROOT, i) for i in DAFNY_INCLUDES]
        self.bodies = []  # type: List[str]
        self.to_run = []  # type: List[str]
        self.id = IDGen()
        self.current_type = None  # type: Optional[str]
        self.current_name = None  # type: Optional[str]
        self.current_ret  = None  # type: Optional[str]
        self.current_args = None  # type: Optional[List[Tuple[str, str]]]
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
    
    def start_method(self, name: str, args: List[Tuple[str, str]]=[], verbatim=False) -> str:
        assert self.current_type is None
        self.current_type = "method"
        self.current_name = self.id.fresh(name) if not verbatim else name
        self.current_ret  = None
        self.current_args = args
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
        return self.current_name

    def start_function(self, name: str, args: List[Tuple[str, str]], ret: str) -> str:
        assert self.current_type is None
        self.current_type = "function"
        self.current_name = self.id.fresh(name)
        self.current_args = args
        self.current_ret  = ret
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
        return self.current_name
    
    def start_lemma(self, name: str, args: List[Tuple[str, str]]=[], verbatim=False) -> str:
        assert self.current_type is None
        self.current_type = "lemma"
        self.current_name = self.id.fresh(name) if not verbatim else name
        self.current_ret  = None
        self.current_args = args
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
        return self.current_name
    
    def end(self, run=False) -> str:
        assert self.current_type is not None
        body = "\n".join("  {}".format(l) for l in self.current_body.getLines())
        annot = "\n".join("  {}".format(l) for l in self.current_annotation.getLines())
        if annot != "":
            annot += "\n"
        arglist = ", ".join("{}: {}".format(n, t) for n, t in self.current_args)
        ret = ": {}".format(self.current_ret) if self.current_ret is not None else ""
        text = "{typ} {name}({args}){ret}\n{annot}{{\n{body}\n}}".format(
            typ=self.current_type, name=self.current_name, args=arglist,
            ret=ret, annot=annot, body=body
        )
        self.bodies.append(text)
        if run:
            if self.current_args == []:
                self.to_run.append(self.current_name)
            else:
                raise Exception("can't run something at top-level with args")
        self.current_type = None
        return self.current_name


    def emit(self, *lines) -> None:
        assert self.current_type is not None
        for l in lines:
            self.current_body.emit(l)
    def emit_annotation(self, *lines) -> None:
        assert self.current_type is not None
        for l in lines:
            self.current_annotation.emit(l)
    def emit_directly(self, text: str, name: Optional[str]=None) -> None:
        self.bodies.append(text)
        if name is not None:
            self.to_run.append(name)


    def to_program(self) -> str:
        self.start_method("Main", verbatim=True)
        for name in self.to_run:
            self.emit("{}();".format(name))
        self.end()

        prelude = "\n".join('include "{}"'.format(i.replace("\\", "\\\\")) for i in self.includes)
        # Dafny's builtin print function uses different cases for true and false; use this
        # as a workaround for now:
        prelude += "\nconst True := true; const False := false;"
        program = "\n\n".join([prelude] + self.bodies)
        return program


    def emit_AssertionProof(self, prf: AssertionProof) -> None:
        prog = self.id.fresh("prog")
        ctx  = self.id.fresh("ctx")
        ret  = self.id.fresh("ret")
        cond = self.id.fresh("cond")
        self.start_method("assertion")
        self.emit(
            "var {} := {};".format(prog, prf.program.to_dafny()),
            "var (_, {}) := Eval({}, EmptyContext(), FUEL);".format(ctx, prog),
            "var {} := {};".format(cond, prf.condition.to_dafny()),
            "var {} := Eval({}, {}, FUEL).0;".format(ret, cond, ctx),
            "assert {} == Int(1);".format(ret))
        self.end(True)
    
    def emit_EquivalenceProof(self, prf: EquivalenceProof) -> None:
        # first, gather the methods from the AST
        v = GatherObjectInfo()
        v.visit(prf.context)
        v.visit(prf.lhs)
        v.visit(prf.rhs)
        lhs_methods = v.get_methods(prf.lhs)
        rhs_methods = v.get_methods(prf.rhs)

        proof_name = self.id.fresh("equivalent")

        # the common stuff
        prefix = prf.context.to_dafny()
        lhs = prf.lhs.to_dafny()
        rhs = prf.rhs.to_dafny()
        invs = self.emit_invariants(prf.invs)

        # build a single invariant that conjoins all invariants together
        if len(invs) > 1:
            self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
            calls = " && ".join("{}(ctx1, ctx2, addr1, addr2)".format(i) for i in invs)
            self.emit(calls)
            inv = self.end()
        elif len(invs) == 1:
            inv = invs[0]
        else:
            inv = self.emit_TrueInvariant(TrueInvariant())

        # If we can evaluate both sides to a constant context and result, we
        # use these terms directly instead of a call to Eval in the output.
        if not Config.get_args().no_precompile:
            lhs_compiled = run_expr(prf.context, prf.lhs)
            rhs_compiled = run_expr(prf.context, prf.rhs)
            use_compiled = lhs_compiled is not None and rhs_compiled is not None
            if Config.get_args().consistency_checks and use_compiled:
                # Emit lemmas stating that the compilation was performed correctly
                correctness_tmpl = template.equivalence.get('compilation_correctness')
                correctness_lemma1 = correctness_tmpl.substitute(
                    name=self.id.fresh('compilation_correctness_lhs'),
                    prefix=prefix, unevaled=lhs, compiled=lhs_compiled)
                self.emit_directly(correctness_lemma1)
                correctness_lemma2 = correctness_tmpl.substitute(
                    name=self.id.fresh('compilation_correctness_rhs'),
                    prefix=prefix, unevaled=rhs, compiled=rhs_compiled)
                self.emit_directly(correctness_lemma2)
        else:
            use_compiled = False

        # generate a new lemma for each method
        lemmas = []  # type: List[str]
        if lhs_methods is not None and rhs_methods is not None:
            common_methods = {}  # type: Dict[str, MethodNode]
            for n, m in lhs_methods.items():
                if n in rhs_methods and len(rhs_methods[n].args) == len(m.args):
                    common_methods[n] = m
            for name in sorted(common_methods):

                lemma_name = "{}_{}".format(proof_name, name)
                lemma_args = [(self.id.fresh("v"), "Value") for _ in common_methods[name].args]
                arg_list = ", ".join("{}: Value".format(v) for v, _ in lemma_args)
                bvs = arg_list
                arg_bindings = list_to_dafny_list([v for v, _ in lemma_args])
                # generate the lemma
                tmpl = template.equivalence.get("method_proof")
                tmpl_compiled = template.equivalence.get("method_proof_compiled")

                # Assert some equalities about method arguments in the new scopes:
                argument_eqs = []
                assert len(common_methods[name].args) == len(lemma_args)
                for i in range(0, len(lemma_args)):
                    arg = common_methods[name].args[i]
                    lemma_arg = lemma_args[i]
                    arg_assertion = '''
    assert {{:fuel (AssocGet<Var, Value>), {fuel}}} AssocGet(scope1, \"{arg_name}\") == Some({lemma_arg}) == AssocGet(scope2, \"{arg_name}\");
'''[1:-1]
                    argument_eqs.append(arg_assertion.format(arg_name=arg.name, lemma_arg=lemma_arg[0], fuel=i+1))


                rec_lemmas = ["AssocGet_Cons<Addr, Object>();",
                              "AssocGet_Cons<Var, Value>();",
                              "AssocGet_Cons<Var, Method>();",
                              "AssocGet_Cons<Addr, MethodList>();"]
                rec_lemmas = "\n".join(["    " + rl for rl in rec_lemmas])

                # TODO: factor out commonalities between the templates
                if use_compiled:
                    # If we have a precompiled context, we can also use a more precise
                    # representation of the havoc'ed object list.
                    # To avoid writing a parser for Dafny ASTs in python, this is implemented
                    # as part of the Dafny backend:
                    havoc_objs1, havoc_vars1 = compute_havoc_data("havocVar1_", lhs_compiled)
                    havoc_objs2, havoc_vars2 = compute_havoc_data("havocVar2_", rhs_compiled)
                    havoc_vars = list(map(lambda p: p[0], havoc_vars1 + havoc_vars2))
                    havoc_formal_params = ", ".join(["{}: Value".format(v) for v in havoc_vars])
                    logging.info("Havoc'd stuff (LHS):\n{}\n{}".format(havoc_objs1, havoc_vars1))
                    logging.info("Havoc'd stuff (RHS):\n{}\n{}".format(havoc_objs2, havoc_vars2))
                    if havoc_formal_params != "" and arg_list != "":
                        arg_list = ", " + arg_list
                    text = tmpl_compiled.substitute(
                        proof=lemma_name, method=name, result1=lhs_compiled, result2=rhs_compiled,
                        cons_args=arg_bindings, args=arg_list, arg_count=len(lemma_args),
                        havoc_vars=havoc_formal_params, havoc_objs1=havoc_objs1, havoc_objs2=havoc_objs2,
                        argument_equalities="\n".join(argument_eqs),
                        rec_lemmas=rec_lemmas,
                        invariant=inv, body=prf.verbatim)
                else:
                    if arg_list != "":
                        arg_list = ", " + arg_list
                    text = tmpl.substitute(
                        proof=lemma_name, method=name, prefix=prefix, lhs=lhs, rhs=rhs, cons_args=arg_bindings,
                        args=arg_list, arg_count=len(lemma_args), argument_equalities="\n".join(argument_eqs),
                        rec_lemmas=rec_lemmas, invariant=inv, body=prf.verbatim)
                self.emit_directly(text)

                # generate the lemma invocation
                use_tmpl = template.equivalence.get("lemma_use_noargs" if lemma_args == [] else "lemma_use_args")
                args = ", ".join(["Nth(values, {})".format(i) for i in range(0, len(lemma_args))])
                if use_compiled:
                    havoc_arg_values1 = list(map(lambda p: p[1].format(objs="objs1"), havoc_vars1))
                    havoc_arg_values2 = list(map(lambda p: p[1].format(objs="objs2"), havoc_vars2))
                    havoc_arg_values = ", ".join(havoc_arg_values1 + havoc_arg_values2)
                    if havoc_arg_values != "" and args != "":
                        args = ", " + args
                else:
                    havoc_arg_values = "objs1, objs2"
                    if args != "":
                        args = ", " + args
                use_text = use_tmpl.substitute(proof=lemma_name, method=name, args=args,
                                               havoc_args=havoc_arg_values)
                lemmas.append(use_text)
            lemmas.append(" {\n      }") # terminate dangling else at the end
        
        # generate the final proof
        body = "     " + "".join(lemmas)
        if use_compiled:
            logging.info("Using precompiled terms for {} and {}".format(prf.lhs, prf.rhs))
            tmpl = template.equivalence.get("equivalence_proof_compiled")
            if havoc_formal_params != "":
                havoc_formal_params = ", " + havoc_formal_params
            # Assert that the havoc'd object list must have the shape we
            # computed before:
            havoc_eq_templ = "        // TODO: proof for this:" +\
                "\n        assert {objs} == {objs_rhs} by {{assume false;}}"
            # FIXME: This step is a bit too fragile and relies on the names of the havoc_vars not
            # appearing anywhere else in the context (as part of the program); should come up
            # with a more robust way of handling this.
            havoc_rhs1_replaced = list(map(lambda p: (p[0], p[1].format(objs="objs1")), havoc_vars1))
            havoc_rhs2_replaced = list(map(lambda p: (p[0], p[1].format(objs="objs2")), havoc_vars2))
            havoc_rhs1 = replace_tuples(havoc_objs1, havoc_rhs1_replaced)
            havoc_rhs2 = replace_tuples(havoc_objs2, havoc_rhs2_replaced)
            # We need to assert that each of the variables actually exists in the havoced context:
            havoc_somes = []
            for havoc_rhs in havoc_rhs1_replaced + havoc_rhs2_replaced:
                # FIXME: this is a horrible mess of regular expressions;
                # writing a proper parser for Dafny expressions in Python would
                # fix this (or port some of this stuff to a .NET language and
                # reuse Dafny's internal data structures)
                assert havoc_rhs[1].endswith(").val")
                # First assert that address is valid:
                assert havoc_rhs[1].startswith("AssocGet(AssocGet(")
                r = re.compile(r'AssocGet\(objs(?P<obj_num>[12]), (?P<addr>[0-9]+)\)')
                addr_expr = havoc_rhs[1][len("AssocGet("):]
                match = r.search(addr_expr)
                assert match is not None
                addr_expr = match.group(0)
                addr_proof = "HavocAddrSomeIff(ctx{obj_num}.objs, objs{obj_num}, {addr});".format(
                    obj_num=match.group('obj_num'), addr=match.group('addr'))
                havoc_somes.append("        assert {}.Some? by {{ {} }}".format(addr_expr, addr_proof))
                havoc_somes.append("        assert {}.Some?;".format(havoc_rhs[1][:-4]))
            havoc_rhs1 = havoc_eq_templ.format(objs="objs1", objs_rhs=havoc_rhs1)
            havoc_rhs2 = havoc_eq_templ.format(objs="objs2", objs_rhs=havoc_rhs2)
            havoc_eqs = "\n".join(havoc_somes + [havoc_rhs1, havoc_rhs2])
#             havoc_eq1 = havoc_eq_templ.format(objs="objs1", objs_rhs
            text = tmpl.substitute(
                proof=proof_name, result1=lhs_compiled, result2=rhs_compiled,
                invariant=inv, body=body, havoc_eqs=havoc_eqs)
        else:
            tmpl = template.equivalence.get("equivalence_proof")
            text = tmpl.substitute(
                proof=proof_name, prefix=prefix, lhs=lhs, rhs=rhs, invariant=inv, body=body
            )
        self.emit_directly(text, proof_name)


    def emit_AdmitProof(self, prf: AdmitProof) -> None:
        self.start_method("admitted")
        lhs_prog = SeqNode(prf.context, prf.lhs)
        rhs_prog = SeqNode(prf.context, prf.rhs)
        lhs = self.id.fresh("lhs")
        rhs = self.id.fresh("rhs")
        self.emit(
            "var {} := {};".format(lhs, lhs_prog.to_dafny()),
            "var {} := {};".format(rhs, rhs_prog.to_dafny()),
            "// this goal is admitted",
            "assert true;")
        self.end(True)

    def emit_RewriteProof(self, prf: RewriteProof) -> None:
        self.start_method("validrewrite")
        ctx = self.id.fresh("ctx")
        lhs = self.id.fresh("lhs")
        rhs = self.id.fresh("rhs")
        assumptions = self.id.fresh("assumptions")
        all_assumptions = prf.assumptions + [(r,l) for l,r in prf.assumptions]
        assumptions_list = "[" + ", ".join(["({}, {})".format(l.to_dafny(), r.to_dafny()) for l, r in all_assumptions]) + "]"
        self.emit(
            "var {} := {};".format(ctx, prf.context.to_dafny()),
            "var {} := {};".format(lhs, prf.lhs.to_dafny()),
            "var {} := {};".format(rhs, prf.rhs.to_dafny()),
            "var {} := {};".format(assumptions, assumptions_list),
            "assert ValidRewrite({}, {}, {}, {}, {}, {});".format(ctx, lhs, rhs, prf.e1.to_dafny(), prf.e2.to_dafny(), assumptions))
        self.end(True)

    def emit_RunProof(self, prf: RunProof) -> None:
        initial_context = "EmptyContext()"
        if prf.initctx is not None:
            k, v = prf.initctx
            initial_context = "EmptyContext().(objs := AssocSet(EmptyContext().objs, 0, Object(Cons(Pair(\"{}\", Int({})), LNil), LNil)))".format(k, v)
        
        self.start_method("run")

        initctx = self.id.fresh("initctx")
        self.emit("var {} := {};".format(initctx, initial_context))

        ctx = initctx
        ret = None
        for t in prf.terms:
            expr = self.id.fresh("expr")
            ret = self.id.fresh("ret")
            newctx = self.id.fresh("ctx")
            self.emit(
                "var {} := {};".format(expr, t.to_dafny()),
                "var ({}, {}) := Eval({}, {}, FUEL);".format(ret, newctx, expr, ctx),
                'Reflect_Expr({}); print " ==> "; Reflect_Value({}); print "\\n";'.format(expr, ret))
            ctx = newctx

        # If there's an expected value and the program matched it, we output
        # "SUCCESS" so the testing script can detect it.
        if prf.expect is not None and prf.expect != "None":
            try:
                x = int(prf.expect)
                self.emit("if ({} == Int({}))".format(ret, x))
            except ValueError:
                self.emit("if ({}.{}?)".format(ret, prf.expect))
            self.emit(" { print \"SUCCESS\"; } else { print \"FAILURE\"; }")

        self.end(True)


    def emit_DefaultInvariant(self, inv: DefaultInvariant) -> str:
        return 'DefaultInvariant'

    def emit_TrueInvariant(self, inv: TrueInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        self.emit("true")
        return self.end()

    def emit_FalseInvariant(self, inv: FalseInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        self.emit("false")
        return self.end()

    def emit_EqualInvariant(self, inv: EqualInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        self.emit(
            """var ctx1' := ctx1.(scope := Cons(Pair("_lhs", Ref(addr1)), ctx1.scope));""",
            """var ctx2' := ctx2.(scope := Cons(Pair("_rhs", Ref(addr2)), ctx2.scope));""",
            """var (lhs', _) := Eval({}, ctx1', FUEL);""".format(inv.lhs.to_dafny()),
            """var (rhs', _) := Eval({}, ctx2', FUEL);""".format(inv.rhs.to_dafny()),
            """lhs' == rhs'""")
        return self.end()

    def emit_ValidInvariant(self, inv: ValidInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        self.emit(
            """var ctx := {}.(ths := {});""".format(ctx, addr),
            """var ret := Eval({}, ctx, FUEL).0;""".format(inv.expr.to_dafny()),
            """!ret.Error?""")
        return self.end()

    def emit_RefInvariant(self, inv: RefInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        self.emit(
            """var ctx := {}.(ths := {});""".format(ctx, addr),
            """var ret := Eval({}, ctx, FUEL).0;""".format(inv.expr.to_dafny()),
            """ret.Ref?""")
        return self.end()

    def emit_IntInvariant(self, inv: IntInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        self.emit(
            """var ctx := {}.(ths := {});""".format(ctx, addr),
            """var ret := Eval({}, ctx, FUEL).0;""".format(inv.expr.to_dafny()),
            """ret.Int?""")
        return self.end()

