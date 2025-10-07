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

import unittest

from stl_consistency.node import Node
from stl_consistency.tableau import make_tableau, shift_bounds
from stl_consistency.parser import STLParser

class TestTableau(unittest.TestCase):

    def make_test(self, formula, max_depth, expected, mltl=False):
        parser = STLParser()
        parsed_formula = parser.parse_formula_as_node(formula)
        #print(parser.parse_formula_as_stl_list(formula))
        res = make_tableau(parsed_formula, max_depth, 'sat', False, False, False, False, mltl)
        self.assertEqual(res, expected)

    def test_and(self):
        self.make_test("a && b", 5, True)

    def test_many_ops(self):
        self.make_test("a && b && c && (a || b || c) && d", 5, True)

    def test_true(self):
        self.make_test("a && !TrUe", 5, False)

    def test_false(self):
        self.make_test("a && FaLsE", 5, False)

    def test_globally0(self):
        self.make_test("G[2,5] (R_x > 5 || R_x < 0)", 10, True)
        
    def test_globally_add(self):
        self.make_test("G[2,5] (R_x + R_y > 5 && R_x - R_y < 0)", 10, True)

    def test_globally_add_many(self):
        self.make_test("G[2,5] (R_x + R_y - R_z + R_x > 5 && R_x - R_y < 0)", 10, True)
    
    def test_release(self):
        self.make_test("(R_x == 10) R[1,6] (R_x < 10)", 10, True)

    def test_abs(self):
        self.make_test("G[0,5] (|x| > 20 | |x| < 10) && F[0,5] (x == -15)", 20, False)

    def test_mltl(self):
        formula = "F[58,92] ((a1) U[87,100] ((a1 && a0 && ! a1) U[9,100] (a0)))"
        self.make_test(formula, 200, False, mltl=False)
        self.make_test(formula, 200, True, mltl=True)

    def test_release(self):
        self.make_test("false R[0,10] a", 100, True)

    def test_GFGG(self):
        self.make_test("G[0,6] F[2,4] a && G[0,6] (a -> G[1,3] !a)", 200, False)

    def test_jump1_0(self):
        self.make_test("!a && G[10,20] !a && F[0,20] a", 200, True)

    def test_jump1_G(self):
        self.make_test("G[0,10] !a && F[5,20] a && G[15,25] !a", 200, True)

    def test_jump1_F(self):
        self.make_test("F[0,10] !a && G[0,9] a && F[10,20] a && G[15,20] !a", 200, True)

    def test_jump1_U(self):
        self.make_test("b U[0,10] !a && G[0,9] a && F[10,20] a && G[15,20] !a", 200, True)

    def test_G_is_derived(self):
        self.make_test("G[0,6]  (! (a0 U[2,10] (F[0,6] (! a0))))", 500, True, mltl=True)

    def test_U_parent(self):
        self.make_test("(G[0,89] F[88,100] a2 U[0,78] !a1) && a1", 500, True, mltl=True)

    def test_shift_bounds_GF(self):
        formula = [
            ',',
            ['G', '3', '50', ['F', '5', '20', ['B_a']]],
            ['G', '10', '60', ['->', ['B_a'], ['G', '20', '40', ['!', ['B_a']]]]],
            ['G', '3', '50', ['F', '5', '20', ['F', '20', '30', ['G', '20', '40', ['!', ['B_a']]]]]],
            ['F', 0, 5, ['&&', ['G', 10, 20, ['B_a']], ['G', 20, 30, ['B_a']]]],
            ['U', 0, 5, ['G', 10, 20, ['B_a']], ['G', 20, 30, ['B_a']]],
            ['U', 0, 5, ['G', 10, 20, ['B_a']], ['||', ['G', 20, 30, ['B_a']], ['B_a']]],
        ]
        expected = [
            ',',
            ['G', 8, 55, ['F', 0, 15, ['B_a']]],
            ['G', 10, 60, ['->', ['B_a'], ['G', 20, 40, ['!', ['B_a']]]]],
            ['G', 48, 95, ['F', 0, 15, ['F', 0, 10, ['G', 0, 20, ['!', ['B_a']]]]]],
            ['F', 10, 15, ['&&', ['G', 0, 10, ['B_a']], ['G', 10, 20, ['B_a']]]],
            ['U', 10, 15, ['G', 0, 10, ['B_a']], ['G', 10, 20, ['B_a']]],
            ['U', 0, 5, ['G', 10, 20, ['B_a']], ['||', ['G', 20, 30, ['B_a']], ['B_a']]],
        ]
        node = Node(*formula)
        shift_bounds(node)
        self.assertEqual(node.to_list(), expected)

    def test_merge_imply_G(self):
        self.make_test("G[0, 10] (a -> G[10, 15] b) && G[0, 10] a && G[16, 16] !b", 200, False)

if __name__ == '__main__':
    unittest.main()
