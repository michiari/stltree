# MIT License
#
# Copyright (c) 2024 Ezio Bartocci, Michele Chiari, Beatrice Melani
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

from stl_consistency.parser import STLParser
from stl_consistency.abstract_syntax_table import STLAbstractSyntaxTable
from stl_consistency.util import all_partitions

from itertools import chain
from z3 import *

class SMTSTLConsistencyChecker:

    relational_op_functions = {
        '<': lambda x, y: x < y,
        '<=': lambda x, y: x <= y,
        '>': lambda x, y: x > y,
        '>=': lambda x, y: x >= y,
        '==': lambda x, y: x == y,
        '!=': lambda x, y: x != y
    }

    arithmetic_op_functions = {
        '+': lambda x, y: x + y,
        '-': lambda x, y: x - y
    }

    def __init__(self):
        pass

    def _encode_time(self, t, time_horizon):
        # Convert the number in a string
        t_str = str(t)
        # Add 0 to complete the string
        return t_str.zfill(len(str(time_horizon)))

    def _encode_variables(self, table, time_horizon, verbose):
        if verbose:
            print("")
            print("# Encode the Real/Binary variables ")
            print("")
        for key in table.getVariableList():
            for t in range(time_horizon):
                prop = f"{key}_t{self._encode_time(t, time_horizon)}"
                if table.getVariableType(key) == 'real':
                    if verbose:
                        print(f"{prop} = Real('{prop}')")
                    self.smt_variables[prop] = Real(prop)
                elif table.getVariableType(key) == 'binary':
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    self.smt_variables[prop] = Bool(prop)

    def _encode_real_expr(self, expr, encoded_time):
        if isinstance(expr, str):
            if STLParser.is_float(expr):
                return float(expr)
            return self.smt_variables[f"{expr}_t{encoded_time}"]
        assert isinstance(expr, tuple)
        if len(expr) == 2:
            assert expr[0] == 'abs'
            return Abs(self._encode_real_expr(expr[1], encoded_time))
        assert len(expr) == 3
        if expr[0] == '/':
            return Q(int(expr[1]), int(expr[2]))
        op = SMTSTLConsistencyChecker.arithmetic_op_functions[expr[0]]
        return op(self._encode_real_expr(expr[1], encoded_time), self._encode_real_expr(expr[2], encoded_time))

    def _filter_witness(self, model):
        filter_model1 = []
        filter_model2 = {}
        sorted_model = {}
        for var in model:
            var_name = str(var)
            if len(var_name) >= 4:
                if var_name[0:4] != "_phi":
                    filter_model1.append(var_name)
                    filter_model2[var_name] = model[var]

        filter_model1.sort()
        for var in filter_model1:
            sorted_model[var] = filter_model2[var]

        return sorted_model

    def solve(self, table, mode, return_trace, verbose):
        # This hashtable will contain the variables for the SMT Solver
        self.smt_variables = {}

        time_horizon = table.getTimeHorizon()
        root_formula = table.getRootFormula()

        if verbose:
            print("# SMT Encoding in Python")
            print()
            print(f"Time horizon = {time_horizon}")
            print("============================")
            print("")

        self._encode_variables(table, time_horizon, verbose)

        if verbose:
            print("")
            print("# Instantiate the SMT Solver")
            print("s = Solver()")

        s = Solver()
        root_prop = f"{root_formula}_t{self._encode_time(0, time_horizon)}"
        if verbose:
            print(f"{root_prop} = Bool('{root_prop}')")
        self.smt_variables[root_prop] = Bool(root_prop)
        s.add(self.smt_variables[root_prop])

        for key, formula in table.getFormulaKeyValuePairs():
            # If the sub-formula to consider is the root formula then we compute only for time t0
            if key == root_formula:
                time_limit = 1
            else:
                time_limit = time_horizon

            for t in range(time_limit):
                encoded_time = self._encode_time(t, time_horizon)
                prop = f"{key}_t{encoded_time}"

                if len(formula) == 1:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    self.smt_variables[prop] = Bool(prop)

                    if formula[0] in {'true', 'false'}:
                        if verbose:
                            print(f"s.add({prop} == {formula[0][2:]})")
                        s.add(self.smt_variables[prop] == (formula[0] == 'true'))
                    else:
                        if verbose:
                            print(f"s.add({prop} == {formula[0]}_t{encoded_time})") 
                        s.add(self.smt_variables[prop] == self.smt_variables[f"{formula[0]}_t{encoded_time}"])

                elif len(formula) == 3 and formula[0] in {'<', '<=', '>', '>=', '==','!='}:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    self.smt_variables[prop] = Bool(prop)
                    op = SMTSTLConsistencyChecker.relational_op_functions[formula[0]]
                    lhs = self._encode_real_expr(formula[1], encoded_time)
                    rhs = self._encode_real_expr(formula[2], encoded_time)
                    s.add(self.smt_variables[prop] == op(lhs, rhs))

                    if verbose:
                        print(f"s.add({self.smt_variables[prop]} == ({formula[1]} {formula[0]} {formula[2]}))")

                elif len(formula) == 4 and formula[0] in {'G','F'}:  # in the case of nested operation it is necessary to do all the t
                    int_a = int(formula[1])
                    int_b = int(formula[2])
                    if t + int_b < time_horizon:

                        prop1 = formula[3]
                        flag = 1
                        for i in range(int_a, int_b + 1):
                            if not f"{prop1}_t{self._encode_time(t + i, time_horizon)}" in self.smt_variables:
                                flag = 0
                                break
                        if flag:
                            if verbose:
                                print(f"{prop} = Bool('{prop}')")
                            self.smt_variables[prop] = Bool(prop)

                            prop1_list = [self.smt_variables[f"{prop1}_t{self._encode_time(t + i, time_horizon)}"] for i in
                                          range(int_a, int_b + 1)]
                            if formula[0] == 'G':
                                s.add(self.smt_variables[prop] == And(prop1_list))
                                if verbose:
                                    print(f"s.add({prop} == And({prop1_list}))")
                            elif formula[0] == 'F':
                                s.add(self.smt_variables[prop] == Or(prop1_list))
                                if verbose:
                                    print(f"s.add({prop} == Or({prop1_list}))")
                elif len(formula) == 3 and formula[0] in {'&&', '||', '->', '<->'}:
                    prop1 = f"{formula[1]}_t{encoded_time}"
                    prop2 = f"{formula[2]}_t{encoded_time}"
                    if prop1 in self.smt_variables and prop2 in self.smt_variables:
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")
                        self.smt_variables[prop] = Bool(prop)
                        if formula[0] == '&&':
                            s.add(self.smt_variables[prop] == And(self.smt_variables[prop1], self.smt_variables[prop2]))
                            if verbose:
                                print(f"s.add({prop} == And({prop1},{prop2}))")
                        elif formula[0] == '||':
                            s.add(self.smt_variables[prop] == Or(self.smt_variables[prop1], self.smt_variables[prop2]))
                            if verbose:
                                print(f"s.add({prop} == Or({prop1},{prop2}))")
                        elif formula[0] == '->':
                            s.add(self.smt_variables[prop] == Implies(self.smt_variables[prop1], self.smt_variables[prop2]))
                            if verbose:
                                print(f"s.add({prop} == Implies({prop1},{prop2}))")
                        elif formula[0] == '<->':
                            s.add(self.smt_variables[prop] == (self.smt_variables[prop1] == self.smt_variables[prop2]))
                            if verbose:
                                print(f"s.add({prop} == ({prop1} == {prop2}))")
                elif len(formula) == 2 and formula[0] in {'!'}:
                    prop1 = f"{formula[1]}_t{encoded_time}"
                    if prop1 in self.smt_variables:
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")
                        self.smt_variables[prop] = Bool(prop)
                        if formula[0] == '!':
                            s.add(self.smt_variables[prop] == Not(self.smt_variables[prop1]))
                            if verbose:
                                print(f"s.add({prop} == Not({prop1}))")
                elif len(formula) == 5 and formula[0] in {'U'}:
                    int_a = int(formula[1])
                    int_b = int(formula[2])
                    # phi1 U_[a,b] phi2 = G [0,a] phi1 && F [a,b] phi2 && F [a,a] (phi1 U phi2)
                    # A   = G [0,a] phi1
                    # B   = F [a,b] phi2
                    # C   = phi1 U phi2
                    # C_t = phi2_t or (phi1_t and C_t+1) with C_N = phi2_N
                    # C_a = F [a,a] (phi1 U phi2)
                    # Example
                    # a = 2 and N = 7
                    # C_t7 = phi2_t7
                    # C_t6 = phi2_t6 or (phi1_t6 and C_t7)
                    # C_t5 = phi2_t5 or (phi1_t5 and C_t6)

                    prop1 = formula[3]
                    prop2 = formula[4]

                    if (t + int_b < time_horizon and
                        all(f"{prop1}_t{self._encode_time(t + i, time_horizon)}" in self.smt_variables for i in range(0, int_b)) and
                        all(f"{prop2}_t{self._encode_time(t + i, time_horizon)}" in self.smt_variables for i in range(int_a, int_b + 1))):

                        # We create
                        if verbose:
                            print("")
                            print(f"{prop}_A = Bool('{prop}_A')")
                        self.smt_variables[f"{prop}_A"] = Bool(f"{prop}_A")
                        prop_a_list = [self.smt_variables[f"{prop1}_t{self._encode_time(t + i, time_horizon)}"] for i in
                                       range(0, int_a + 1)]
                        s.add(self.smt_variables[f"{prop}_A"] == And(prop_a_list))
                        if verbose:
                            print(f"s.add({prop}_A == And({prop_a_list}))")

                        self.smt_variables[f"{prop}_B"] = Bool(f"{prop}_B")
                        if verbose:
                            print("")
                            print(f"{prop}_B = Bool('{prop}_B')")
                        prop_b_list = [self.smt_variables[f"{prop2}_t{self._encode_time(t + i, time_horizon)}"] for i in
                                       range(int_a, int_b + 1)]
                        s.add(self.smt_variables[f"{prop}_B"] == Or(prop_b_list))
                        if verbose:
                            print(f"s.add({prop}_B == Or({prop_b_list}))")
                            print("")
                        if f"{key}_t{self._encode_time(t + int_a, time_horizon)}_C" not in self.smt_variables:
                            if verbose:
                                print(f"The variables {key}_t{self._encode_time(t + int_a, time_horizon)}_C are not in self.smt_variables")

                            if f"{key}_t{self._encode_time(t + int_b, time_horizon)}_C" not in self.smt_variables:
                                if verbose:
                                    print(f"{key}_t{self._encode_time(t + int_b, time_horizon)}_C = Bool('{key}_t{self._encode_time(t + int_b, time_horizon)}_C')")
                                self.smt_variables[f"{key}_t{self._encode_time(t + int_b, time_horizon)}_C"] = Bool(
                                    f"{key}_t{self._encode_time(t + int_b, time_horizon)}_C")
                                s.add(self.smt_variables[f"{key}_t{self._encode_time(t + int_b, time_horizon)}_C"] ==
                                      self.smt_variables[f"{prop2}_t{self._encode_time(t + int_b, time_horizon)}"])
                                if verbose:
                                    print(f"s.add({key}_t{self._encode_time(t + int_b, time_horizon)}_C == {prop2}_t{self._encode_time(t + int_b, time_horizon)})")

                            for i in range(t + int_b - 1, t + int_a - 1, -1):

                                k = time_horizon - i - 2 + int_a
                                # print(f"i = {i}, k = {k}")
                                if not f"{key}_t{self._encode_time(i, time_horizon)}_C" in self.smt_variables:
                                    if verbose:
                                        print(f"{key}_t{self._encode_time(i, time_horizon)}_C = Bool('{key}_t{self._encode_time(i, time_horizon)}_C')")
                                    self.smt_variables[f"{key}_t{self._encode_time(i, time_horizon)}_C"] = Bool(f"{key}_t{self._encode_time(k, time_horizon)}_C")
                                    if verbose:
                                        print(f"s.add({key}_t{self._encode_time(i, time_horizon)}_C == Or({prop2}_t{self._encode_time(i, time_horizon)},And({prop1}_t{self._encode_time(i + 1, time_horizon)},{key}_t{self._encode_time(i + 1, time_horizon)}_C))")
                                    s.add(self.smt_variables[f"{key}_t{self._encode_time(i, time_horizon)}_C"] == Or(
                                        self.smt_variables[f"{prop2}_t{self._encode_time(i, time_horizon)}"],
                                        And(self.smt_variables[f"{prop1}_t{self._encode_time(i, time_horizon)}"],
                                            self.smt_variables[f"{key}_t{self._encode_time(i + 1, time_horizon)}_C"])))

                        self.smt_variables[f"{prop}"] = Bool(f"{prop}")
                        if verbose:
                            print(f"\n{prop} = Bool('{prop}')")

                        s.add(
                            self.smt_variables[f"{prop}"] == And(self.smt_variables[f"{prop}_A"], self.smt_variables[f"{prop}_B"],
                                                            self.smt_variables[
                                                                f"{key}_t{self._encode_time(int_a, time_horizon)}_C"]))
                        if verbose:
                            print(f"s.add({prop} == And({prop}_A,{prop}_B,{key}_t{self._encode_time(int_a, time_horizon)}_C))")

        if mode == 'strong_sat':
            imply_formulas = list(filter(lambda pf: len(pf[1]) == 3 and pf[1][0] == '->', table.getFormulaKeyValuePairs()))
            if verbose:
                print("================================")
                print("Encoding 'strong_sat' mode")
                print("List of implications:", imply_formulas)

            for t in range(time_horizon):
                if verbose:
                    print("s.add(Or(")
                encoded_time = self._encode_time(t, time_horizon)
                imply_formulas_t = map(lambda prop_f: prop_f + (f"{prop_f[0]}_t{encoded_time}",), imply_formulas)
                encoded_imply_formulas_t = filter(lambda pft: pft[2] in self.smt_variables, imply_formulas_t)
                clauses = []
                for p1, p2 in all_partitions(encoded_imply_formulas_t):
                    true_implications = map(lambda pft: self.smt_variables[pft[2]], p1)
                    false_implications = map(lambda pft: Not(self.smt_variables[pft[2]]), p2)
                    true_antecedents = map(lambda pft: self.smt_variables[f"{pft[1][1]}_t{encoded_time}"], p1)
                    clauses.append(And(list(chain(true_implications, false_implications, true_antecedents))))

                    if verbose:
                        print("\tAnd(", end='\n\t\t')
                        print(*map(lambda pft: pft[2], p1), sep=", ", end=',\n\t\t')
                        print(*map(lambda pft: f"Not({pft[2]})", p2), sep=", ", end=',\n\t\t')
                        print(*map(lambda pft: f"{pft[1][1]}_t{encoded_time}", p1), sep=", ")
                        print("\t)")

                s.add(Or(clauses))

                if verbose:
                    print(")) # end s.add, Or")
                    

        if verbose:
            print("")
            print("================================")
            print(f"Num of variables in SMT solver = {len(self.smt_variables)}")
            print("")
            print("Solver statistics")
            print(s.statistics())
            print(s)

        check_res = s.check()

        if check_res == unsat:
            if verbose:
                print("The STL requirements are inconsistent.")
                print(f"The unsat core is {s.unsat_core()}")
            return False
        elif check_res == sat:
            if verbose:
                print("The STL requirements are consistent.")
            if return_trace:
                return self._filter_witness(s.model()), True
            return True
        else:
            print("Unable to check consistency!")
            return None


def smt_check_consistency(parsed_formula, mode, return_trace, verbose=False):
    table = STLAbstractSyntaxTable(parsed_formula)

    if verbose:
        print("Parsed STL Expression:", parsed_formula)
        table.print()

    checker = SMTSTLConsistencyChecker()
    return checker.solve(table, mode, return_trace, verbose)
