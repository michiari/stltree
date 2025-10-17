# MIT License
#
# Copyright (c) 2025 Michele Chiari
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
import z3


class QSMTFormulaEncoder:
    def __init__(self, mltl):
        self.bool_var_map = {}
        self.real_var_map = {}
        self.h = z3.Int('h')
        self.mltl = mltl

    def encode(self, formula, t):
        match formula[0]:
            case '&&':
                return z3.And(*(self.encode(arg, t) for arg in formula[1:]))
            case '||':
                return z3.Or(*(self.encode(arg, t) for arg in formula[1:]))
            case '!':
                return z3.Not(self.encode(formula[1], t))
            case '->':
                return z3.Implies(self.encode(formula[1], t), self.encode(formula[2], t))
            case 'G':
                a, b, subf = int(formula[1]), int(formula[2]), formula[3]
                i = z3.FreshInt('G_i')
                return z3.ForAll(i, z3.Implies(z3.And(t + a <= i, i <= t + b), self.encode(subf, i)))
            case 'F':
                a, b, subf = int(formula[1]), int(formula[2]), formula[3]
                i = z3.FreshInt('F_i')
                return z3.Exists(i, z3.And(t + a <= i, i <= t + b, self.encode(subf, i)))
            case 'U':
                a, b, f1, f2 = int(formula[1]), int(formula[2]), formula[3], formula[4]
                i, j = z3.FreshInt('U_i'), z3.FreshInt('U_j')
                forall_range = z3.And(t + a <= j, j < i) if self.mltl else z3.And(t <= j, j <= i)
                return z3.Exists(i, z3.And(
                    t + a <= i, i <= t + b,
                    self.encode(f2, i),
                    z3.ForAll(j, z3.Implies(forall_range, self.encode(f1, j)))
                ))
            case 'R':
                a, b, f1, f2 = int(formula[1]), int(formula[2]), formula[3], formula[4]
                i, j = z3.FreshInt('R_i'), z3.FreshInt('R_j')
                exists_range = z3.And(t + a <= j, j < i) if self.mltl else z3.And(t <= j, j <= i)
                return z3.ForAll(i, z3.Implies(
                    z3.And(t + a <= i, i <= t + b),
                    self.encode(f2, i),
                    z3.Exists(j, z3.And(exists_range, self.encode(f1, j)))
                ))
            case '<' | '<=' | '>' | '>=' | '==' | '!=':
                lhs = self._encode_arith_expr(formula[1], t)
                rhs = self._encode_arith_expr(formula[2], t)
                return z3.And(self.h >= t, QSMTFormulaEncoder.relational_op_functions[formula[0]](lhs, rhs))
            case _:
                if len(formula) == 1 and isinstance(formula[0], str):
                    var_name = formula[0]
                    if var_name == 'true':
                        return z3.BoolVal(True)
                    if var_name == 'false':
                        return z3.BoolVal(False)
                    if var_name not in self.bool_var_map:
                        self.bool_var_map[var_name] = z3.Function(var_name, z3.IntSort(), z3.BoolSort())
                    return z3.And(self.h >= t, self.bool_var_map[var_name](t))
                raise ValueError('Malformed formula ' + str(formula))

    relational_op_functions = {
        '<': lambda x, y: x < y,
        '<=': lambda x, y: x <= y,
        '>': lambda x, y: x > y,
        '>=': lambda x, y: x >= y,
        '==': lambda x, y: x == y,
        '!=': lambda x, y: x != y
    }

    def _encode_arith_expr(self, expr, t):
        if isinstance(expr, str):
            if STLParser.is_float(expr):
                return float(expr)
            if expr not in self.real_var_map:
                self.real_var_map[expr] = z3.Function(expr, z3.IntSort(), z3.RealSort())
            return self.real_var_map[expr](t)

        assert isinstance(expr, list)
        if len(expr) == 2:
            assert expr[0] == 'abs'
            return z3.Abs(self._encode_arith_expr(expr[1], t))

        assert len(expr) == 3
        lhs = self._encode_arith_expr(expr[1], t)
        rhs = self._encode_arith_expr(expr[2], t)
        match expr[0]:
            case '+':
                return lhs + rhs
            case '-':
                return lhs - rhs
        raise ValueError(f"Unknown operator: {expr[0]}")

    def _lists_to_tuples(self, formula):
        if isinstance(formula, list):
            return tuple(self._lists_to_tuples(el) for el in formula)
        return formula

class QuantifiedSMTChecker:
    def __init__(self, mltl):
        self.solver = z3.Solver()
        self.encoder = QSMTFormulaEncoder(mltl)

    def check_formula(self, formula, verbose = False):
        z3_formula = self.encoder.encode(formula, 0)
        self.solver.add(z3_formula)

        if verbose:
            print("Z3 formula:")
            print(z3_formula)
            print("Solving...")

        result = self.solver.check()

        if verbose:
            print("Solver statistics")
            print(self.solver.statistics())
            print("Result:", result)

        match result:
            case z3.unsat:
                if verbose:
                    print("The STL requirements are inconsistent.")
                return False
            case z3.sat:
                if verbose:
                    print("The STL requirements are consistent.")
                return True
            case _:
                print("Unable to check consistency!")
                print(self.solver.reason_unknown())
                print(self.solver.to_smt2())
                return None

def qsmt_check_consistency(formula, mltl, verbose = False):
    checker = QuantifiedSMTChecker(mltl)
    return checker.check_formula(formula, verbose)
