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

from stl_consistency.qsmtchecker import qsmt_check_consistency
from stl_consistency.parser import STLParser

class TestQSMTChecker(unittest.TestCase):

    def make_test(self, formula, result, mltl = False):
        parser = STLParser()
        parsed_formula = parser.parse_formula_as_stl_list(formula)
        print(parsed_formula)
        self.assertEqual(qsmt_check_consistency(parsed_formula, mltl, True), result)

    def test_and(self):
        self.make_test("a && b", True)

    def test_bool(self):
        self.make_test("a && b || c && d && e", True)

    def test_many_ops(self):
        self.make_test("a && b && c && (a || b || c) && d", True)

    def test_true(self):
        self.make_test("a && !TrUe", False)

    def test_false(self):
        self.make_test("a && FaLsE", False)

    def test_globally0(self):
        self.make_test("G[2,5] (x > 5 || x < 0)", True)

    def test_globally_add(self):
        self.make_test("G[2,5] (x + y > 5 && x - y < 0)", True)

    def test_globally_add_many(self):
        self.make_test("G[2,5] (x + y - z + x > 5 && x - y < 0)", True)
    
    def test_release(self):
        self.make_test("(x == 10) R[1,6] (x < 10)", True)

    def test_abs(self):
        self.make_test("G[0,5] (|x| > 20 | |x| < 10) && F[0,5] (x == -15)", False)

    def test_mltl(self):
        formula = "F[58,92] ((a1) U[87,100] ((a1 && a0 && ! a1) U[9,100] (a0)))"
        self.make_test(formula, False, mltl=False)
        self.make_test(formula, True, mltl=True)

    def test_release_false(self):
        self.make_test("false R[0,10] a", True)

    def test_GFGG(self):
        self.make_test("G[0,6] F[2,4] a && G[0,6] (a -> G[1,3] !a)", False)
        
    def test_jump1_0(self):
        self.make_test("!a && G[10,20] !a && F[0,20] a", True)

    def test_jump1_G(self):
        self.make_test("G[0,10] !a && F[5,20] a && G[15,25] !a", True)

    def test_jump1_F(self):
        self.make_test("F[0,10] !a && G[0,9] a && F[10,20] a && G[15,20] !a", True)

    def test_jump1_U(self):
        self.make_test("b U[0,10] !a && G[0,9] a && F[10,20] a && G[15,20] !a", True)

    def test_G_is_derived(self):
        self.make_test("G[0,6]  (! (a0 U[2,10] (F[0,6] (! a0))))", True, mltl=True)

    def test_U_parent(self):
        self.make_test("(G[0,89] F[88,100] a2 U[0,78] !a1) && a1", True, mltl=True)

    def test_G_initial_upper(self):
        self.make_test("G[0,53] ((G[0,38] (! a0 && (F[0,54] (a0)))))", False, mltl=True)

    def test_merge_imply_G(self):
        self.make_test("G[0, 10] (a -> G[10, 15] b) && G[0, 10] a && G[16, 16] !b", False)

    def test_real(self):
        self.make_test("G[0,5] (x - 3.5 <= y + 2.0E2)", True)

    def test_rational(self):
        self.make_test("G[0,5] (x + -3/4 <= y - 5/8) && F[1,2] (x - y > 1/8)", False)


if __name__ == '__main__':
    unittest.main()
