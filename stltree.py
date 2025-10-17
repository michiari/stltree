#!/usr/bin/env python3

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

import argparse
import sys
import time
import networkx

from stl_consistency.parser import STLParser
from stl_consistency.smtchecker import smt_check_consistency
from stl_consistency.qsmtchecker import qsmt_check_consistency
from stl_consistency.tableau import make_tableau

def read_formula(filename):
    with open(filename, 'rt') as f:
        return f.read()

DEFAULT_DEPTH = 10000000

def main():
    argp = argparse.ArgumentParser()
    argp.add_argument('-s', '--smt', action='store_true', help='Use SMT-based bounded satisfiability checker instead of tree-based tableau (default)')
    argp.add_argument('-f', '--fol', action='store_true', help='Use FOL satisfiability checker instead of tree-based tableau (default)')
    argp.add_argument('-d', '--max-depth', type=int, default=DEFAULT_DEPTH, help='Build tableau up to the given depth (ignored if --smt is given)')
    argp.add_argument('-p', '--plot', type=str, help='Plot the tree-shaped tableau to the given dot file (ignored if --smt is given)')
    argp.add_argument('--print-trace', action='store_true', help='Print an example trace that satisfies the formula)')
    argp.add_argument('-t', '--strong-sat', action='store_true', help='Use strong definition of satisfiability that avoids formulas being satisfied vacuously (default is normal satisfiability)')
    argp.add_argument('--smtlib-result', action='store_true', help='Emit result as SMTLIB output (sat, unsat, unknown)')
    argp.add_argument('--parallel', action='store_true', help='Use parallel version of the tableau')
    argp.add_argument('--mltl', action='store_true', help='Use MLTL semantics for U and R operators.') # TODO support this in SMT engine
    argp.add_argument('--no-jump', action='store_true', help='Disable jump rule in tableau.')
    argp.add_argument('--no-formula-optimizations', action='store_true', help='Disable formula optimizations in tableau.')
    argp.add_argument('--no-children-order-optimizations', action='store_true', help='Disable children order optimizations in tableau.')
    argp.add_argument('--no-early-local-consistency-check', action='store_true', help='Perform local consistency checks on poised tableau nodes only.')
    argp.add_argument('--no-memoization', action='store_true', help='Disable memoization of tableau nodes.')
    argp.add_argument('--no-simple-nodes', action='store_true', help='Disable simple nodes optimization in tableau.')
    argp.add_argument('--no-g-f', action='store_true', help='Do not use special rules for G and F in the tableau.')
    argp.add_argument('-v', '--verbose', action='store_true')
    argp.add_argument('formula', type=str, help='File containing formula to be checked.')
    args = argp.parse_args()

    sys.setrecursionlimit(100000000)

    formula = read_formula(args.formula)
    parser = STLParser()

    mode = 'strong_sat' if args.strong_sat else 'sat'

    if args.smt:
        start_t = time.perf_counter()
        parsed_formula = parser.parse_formula_as_stl_list(formula)
        parsing_t = time.perf_counter()
        res = smt_check_consistency(parsed_formula, mode, args.print_trace, args.verbose)

        if args.print_trace:
            trace, res = res
            if res:
                print('Trace:')
                print(trace)
    elif args.fol:
        start_t = time.perf_counter()
        parsed_formula = parser.parse_formula_as_stl_list(formula)
        parsing_t = time.perf_counter()
        res = qsmt_check_consistency(parsed_formula, args.mltl, args.verbose)
    else:
        start_t = time.perf_counter()

        parsed_formula = parser.parse_formula_as_node(formula)
        parsing_t = time.perf_counter()

        tableau_opts = {
            'jump': not args.no_jump,
            'formula_opts': not args.no_formula_optimizations,
            'children_order_opts': not args.no_children_order_optimizations,
            'early_local_consistency_check': not args.no_early_local_consistency_check,
            'memoization': not args.no_memoization,
            'simple_nodes_first': not args.no_simple_nodes,
            'g_f': not args.no_g_f
        }

        res = make_tableau(
            parsed_formula,
            args.max_depth,
            mode,
            build_tree=args.plot is not None,
            return_trace=args.print_trace,
            parallel=args.parallel,
            verbose=args.verbose,
            mltl=args.mltl,
            tableau_opts=tableau_opts
        )

        if args.plot or args.print_trace:
            tree, trace, res = res
            if args.plot:
                networkx.drawing.nx_pydot.write_dot(tree, args.plot)
            if args.print_trace and res:
                    print('Trace:')
                    print(trace)

    if args.smtlib_result:
        if res:
            print('sat')
        elif res is None:
            print('unknown')
        else:
            print('unsat')
    else:
        print(f'Elapsed time: {time.perf_counter() - parsing_t} (parsing: {parsing_t - start_t})')
        if res:
            print('The constraints are consistent.')
        elif res is None:
            print('Consistency could not be proved within the given depth limit. Please increase it with the -d option.')
        else:
            print(f'The constraints are not consistent.')


if __name__ == "__main__":
    main()
