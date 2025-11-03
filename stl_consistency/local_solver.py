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

import z3
from stl_consistency.parser import STLParser

class LocalSolver:

    def __init__(self):
        self.solver = z3.Solver()
        self.z3_variables = {}
        self.z3_ast_cache = {} # contains entries of the form (negated, key) -> z3_ast
        self.boolean_solver = BooleanSolver()
        self.current_assertions = set() # contains entries of the form (negated, key) keeping track of current assertions in solver
        self.assertion_stack = [] # contains entries of the form [(negated, key)]
        # Cache for result of self.solver.check(). To be invalidated after every self.solver.assert_exprs
        self.check_result = True

    def get_empty_solver(self):
        new_solver = LocalSolver()
        new_solver.z3_variables = self.z3_variables
        new_solver.z3_ast_cache = self.z3_ast_cache
        return new_solver

    def add_boolean_constraint(self, negated, prop):
        # TODO use identifier
        entry = (negated, prop)
        if entry not in self.current_assertions:
            self.current_assertions.add(entry)
            self.assertion_stack[-1].append(entry)
            self.boolean_solver.add_constraint(negated, prop)

            if self.check_result:
                self.check_result = self.boolean_solver.check()

    def add_real_constraint(self, negated, node):
        assert node.identifier is not None
        entry = (negated, node.identifier)
        if entry not in self.current_assertions:
            self.current_assertions.add(entry)
            self.assertion_stack[-1].append(entry)
            if entry not in self.z3_ast_cache:
                    z3_ast = self.real_term_to_z3(node)
                    self.z3_ast_cache[entry] = z3.Not(z3_ast) if negated else z3_ast
            self.solver.assert_exprs(self.z3_ast_cache[entry])
            
            if (not negated, node.identifier) in self.current_assertions:
                self.check_result = False

            if self.check_result:
                self.check_result = None

    def check(self):
        if self.check_result is None:
            #print(self.solver)
            self.check_result = self.boolean_solver.check() and self.solver.check() == z3.sat
        return self.check_result

    def push(self):
        self.assertion_stack.append([])
        self.solver.push()

    def pop(self):
        if self.assertion_stack:
            old_assertions = self.assertion_stack.pop()
            for ass in old_assertions:
                self.current_assertions.remove(ass)
                negated, term = ass
                if isinstance(term, str):
                    self.boolean_solver.remove_constraint(negated, term)
            self.solver.pop()
            if len(old_assertions) > 0:
                self.check_result = None

    def reset(self):
        self.assertion_stack = []
        self.current_assertions = set()
        self.check_result = None
        self.solver.reset()

    def real_term_to_z3(self, node):
        comp, lhs, rhs = node.operands
        lhs = self.real_expr_to_z3(lhs)
        rhs = self.real_expr_to_z3(rhs)
        match comp:
            case '<':
                return lhs < rhs
            case '<=':
                return lhs <= rhs
            case '>':
                return lhs > rhs
            case '>=':
                return lhs >= rhs
            case '==':
                return lhs == rhs
            case '!=':
                return lhs != rhs
            case _:
                raise ValueError(f"Unknown operator: {comp}")

    def real_expr_to_z3(self, expr):
        if isinstance(expr, str):
            if STLParser.is_float(expr):
                return float(expr)
            if expr not in self.z3_variables:
                self.z3_variables[expr] = z3.Real(expr)
            return self.z3_variables[expr]

        assert isinstance(expr, list)
        if len(expr) == 2:
            assert expr[0] == 'abs'
            return z3.Abs(self.real_expr_to_z3(expr[1]))

        assert len(expr) == 3
        if expr[0] == '/':
            return z3.Q(int(expr[1]), int(expr[2]))

        lhs = self.real_expr_to_z3(expr[1])
        rhs = self.real_expr_to_z3(expr[2])
        match expr[0]:
            case '+':
                return lhs + rhs
            case '-':
                return lhs - rhs
        raise ValueError(f"Unknown operator: {expr[0]}")


class BooleanSolver:

    def __init__(self):
        self.pos_props = set()
        self.neg_props = set()
        self.check_result = True

    def add_constraint(self, negated, prop):
        if negated:
            self.neg_props.add(prop)
            if prop in self.pos_props:
                self.check_result = False
        else:
            self.pos_props.add(prop)
            if prop in self.neg_props:
                self.check_result = False

    def remove_constraint(self, negated, prop):
        if negated:
            self.neg_props.remove(prop)
        else:
            self.pos_props.remove(prop)

        if not self.check_result:
            # It we remove a constraint, the set of terms might become satisfiable
            self.check_result = None
    
    def check(self):
        if self.check_result is None:
            self.check_result = self.pos_props.isdisjoint(self.neg_props)

        return self.check_result
