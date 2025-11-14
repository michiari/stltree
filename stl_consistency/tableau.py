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

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import bisect
import concurrent.futures as fs
from stl_consistency.node import Node
from stl_consistency.local_solver import LocalSolver


def modify_U_R(node):
    """Modify formula by replacing p U[a,b] q and p R[a,b] q ."""
    """ pU[a,b]q becomes pU[a,b]q && G[0,a]p whereas (p R[a,b] q) → (F[0,a] p) || (p R[a,b] q)"""
    # If node.operator is ('P'), node is returned with no modification
    if node.operator == 'P':
        return node

    for i in range(len(node.operands)):
        node.operands[i] = modify_U_R(node.operands[i])

    # If node.operator is Until, it becomes: (p U[a,b] q) → (p U[a,b] (p ∧ q) ∧ (G[0,a] p)
    if node.operator == 'U':
        p = node[0]
        q = node[1]
        a = node.lower

        new_q = Node('&&', p, q)
        node.replace_operand(1, new_q)

        if node.lower > 0:
            G_part = Node('G', '0', a, p)
            new_node = Node('&&', node, G_part)
            return new_node

    # if node.operator is Release, it becomes: (p R[a,b] q) → (F[0,a] p) ∨ (p R[a,b] q)
    elif node.operator == 'R' and node.lower > 0:
        p = node[0]
        a = node.lower

        F_part = Node('F', '0', a, p)
        new_node = Node('||', F_part, node)
        return new_node

    # return node with updated operands
    return node


def push_negation(node):
    if node.operator == '!':
        operand = node[0]
        match operand.operator:
            case 'P':
                return node
            case '!':
                return push_negation(operand[0])

        new_node = operand.shallow_copy()
        match operand.operator:
            case ',' | '&&':
                new_node.operator = '||'
                new_node.operands = [push_negation(Node('!', op)) for op in operand]
            case '||':
                new_node.operator = ','
                new_node.operands = [push_negation(Node('!', op)) for op in operand]
            case '->':
                new_node.operator = ','
                new_node.operands = [operand[0], push_negation(Node('!', operand[1]))]
            case 'O':
                new_node.operator = operand.operator
                new_node.operands = [push_negation(Node('!', operand[0]))]
            case 'G':
                new_node.operator = 'F'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0]))]
            case 'F':
                new_node.operator = 'G'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0]))]
            case 'U':
                new_node.operator = 'R'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0])), push_negation(Node('!', operand[1]))]
            case 'R':
                new_node.operator = 'U'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0])), push_negation(Node('!', operand[1]))]
            case _:
                raise ValueError('Bad formula')
        return new_node
    elif node.operator == 'P':
        return node
    else:  # Any non-negated operator
        new_node = node.shallow_copy()
        new_node.operands = [push_negation(op) for op in node.operands]
        return new_node

def shift_bounds(node):
    def shift_backward(f, shift_amount):
        match f.operator:
            case '&&' | '||' | ',' | '->' | '!':
                for operand in f:
                    shift_backward(operand, shift_amount)
            case 'G' | 'F' | 'U' | 'R':
                f.lower -= shift_amount
                f.upper -= shift_amount
                f.initial_upper -= shift_amount
            case _:
                raise RuntimeError('Trying to shift bounds of proposition')

    match node.operator:
        case '&&' | '||' | ',' | '->' | '!':
            for operand in node:
                shift_bounds(operand)
        case 'G' | 'F':
            shift_bounds(node[0])
            shift_amount = node[0].get_min_lower(False)
            # If get_min_lower is -1, we can't shift because there are props at the first level
            if shift_amount > 0:
                shift_backward(node[0], shift_amount)
                node.lower += shift_amount
                node.upper += shift_amount
                node.initial_upper += shift_amount
        case 'U' | 'R':
            shift_bounds(node[0])
            shift_bounds(node[1])
            shift_amount0 = node[0].get_min_lower(False)
            shift_amount1 = node[1].get_min_lower(False)
            shift_amount = min(shift_amount0, shift_amount1)
            # If get_min_lower is -1, we can't shift because there are props at the first level
            if shift_amount > 0:
                shift_backward(node[0], shift_amount)
                shift_backward(node[1], shift_amount)
                node.lower += shift_amount
                node.upper += shift_amount
                node.initial_upper += shift_amount

def remove_GF(node):
    match node.operator:
        case 'G':
            return Node('R', node.lower, node.upper, Node('false'), node[0])
        case 'F':
            return Node('U', node.lower, node.upper, Node('true'), node[0])
        case 'P':
            return node
        case _:
            new_node = node.shallow_copy()
            new_node.operands = [remove_GF(op) for op in node.operands]
            return new_node

def assign_and_or_element(node):
    """
    It assigns the attribute and_element at every operand of an && inside a G
    and or_element at every operand of a || inside a G
    """
    if not node.operands:
        return

    if node.operator == 'G' and node.operands[0].operator == '&&':
        # Assign and_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.and_element = index
    elif node.operator == 'G' and node.operands[0].operator == '||':
        # Assign or_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.or_element = index

    # Recursion for all operands
    for operand in node.operands:
        if isinstance(operand, Node):
            assign_and_or_element(operand)


def count_implications(node, counter=[0]):
    """
    Counts all implications ('->') in the node and in its operands,
    assigning to each a unique identifier.

    """
    if not isinstance(node, Node):
        return
    if node.operator == '->':
        node.identifier = counter[0]  # Assign ID
        counter[0] += 1
    else:
        for operand in node.operands:
            count_implications(operand, counter)

    return counter[0]


def assign_identifier(node):
    '''
    :param node:
    :return: assign id to nested operator, such that it is possible to recognize from which nested operator
    an operand has been extracted
    '''
    id_counter = 0
    # We assign the same identifier to equal P formulas
    # We use a list instead of a set because lists (node.operands) are unhashable
    already_assigned = []

    def do_assign(node):
        nonlocal id_counter
        match node.operator:
            case 'P':
                prev_id = next(filter(lambda expr_id: expr_id[0] == node.operands, already_assigned), None)
                if prev_id:
                    node.identifier = prev_id[1]
                else:
                    node.identifier = id_counter
                    already_assigned.append((node.operands, id_counter))
                    id_counter += 1
            case 'G' | 'F' | 'U' | 'R':
                node.identifier = id_counter
                id_counter += 1
                for operand in node.operands:
                    do_assign(operand)
            case '&&' | '||' | ',' | '->' | '!':
                for operand in node.operands:
                    do_assign(operand)

    do_assign(node)


def decompose(tableau_data, local_solver, node, current_time):
    """
    :param node: node to be decomposed with operator ','
    :param current_time: current time instant to understand which operands can be decomposed
    :return: return next node(s) of the tree
    """
    # early accept/reject check, if rejected you do not need to decompose further on the branch
    if tableau_data.tableau_opts['early_local_consistency_check'] and not local_consistency_check(local_solver, node):
        return ['Rejected']
    res, has_decomposed = decompose_and(node)
    if has_decomposed:
        return res
    
    res, has_decomposed = decompose_all_G_nodes(tableau_data.tableau_opts, node, current_time)
    if has_decomposed:
        return res

    res = None
    for j in range(len(node.operands)):
        match node.operands[j].operator:
            case '||':
                res = decompose_or(tableau_data.tableau_opts, node, j)
                break
            case '->':
                if tableau_data.mode == 'complete' or tableau_data.mode == 'sat':
                    res = decompose_imply_classic(tableau_data, node, j)
                else:
                    #res = decompose_imply_new(node, j)
                    res = decompose_imply_classic(tableau_data, node, j, 'strong_sat')
                break

    if res is None:
        for j in range(len(node.operands)):
            match node.operands[j].operator:
                case 'F':
                    if node.operands[j].lower == current_time:
                        res = decompose_F(node, j)
                        break
                case 'U':
                    if node.operands[j].lower == current_time:
                        res = decompose_U(node, j)
                        break
                case 'R':
                    if node.operands[j].lower == current_time:
                        res = decompose_R(node, j, tableau_data.mltl)
                        break

    if res is not None:
        for child in res:
            child.current_time = node.current_time
        return res

    # if you get here it means that you had nothing to decompose and therefore you can jump ahead
    if not tableau_data.tableau_opts['early_local_consistency_check'] and not local_consistency_check(local_solver, node):
        return ['Rejected']

    if not tableau_data.tableau_opts['jump']:
        node.jump1 = True

    return decompose_jump(tableau_data, node)


def decompose_all_G_nodes(tableau_opts, outer_node, current_time):
    """
    Decomposes all active G nodes in the formula.
    """
    # Function do modify argument of G
    def modify_argument(arg, G_node, short, simple):
        if arg.operator in {'P', '!'}:
            return arg
        elif simple and arg.operator == 'F' and G_node.lower + 2 <= G_node.upper:
            # We expand with the equivalence G[a,b]F[c,d] q = (F[a+c+1,a+d] q || (G[a+c,a+c] q && G[a+d+1,a+d+1] q)) && G[a+2,b]F[c,d] q
            a = G_node.lower
            c, d = arg.lower, arg.upper
            q = arg.operands[0]
            G_node.lower += 1 # this implements G[a+2,b]F[c,d] q because decompose_jump adds 1 again
            ret = Node('||', Node('F', a+c+1, a+d, q), Node(',', Node('G', a+c, a+c, q), Node('G', a+d+1, a+d+1, q)))
            ret.set_initial_time()
            return ret
        elif arg.operator in {'U', 'R', 'F'} or (arg.operator == 'G' and (not short or G_node.lower == G_node.initial_time)):
            # Modify bounds adding that of the external G
            extract = arg.shallow_copy()
            extract.lower = arg.lower + G_node.lower
            extract.upper = extract.initial_upper = arg.upper + G_node.lower
            extract.parent = G_node.identifier if G_node.lower < G_node.upper else None
            extract.set_initial_time()
            return extract
        elif short and arg.operator == 'G' and G_node.lower > G_node.initial_time:
            G_counter = 0
            for i, operand in enumerate(outer_node.operands):
                if operand.operator == 'G' and operand.is_derived() and operand.parent == G_node.identifier and operand.and_element == arg.and_element:
                    outer_node.operands[i] = operand.shallow_copy()
                    outer_node.operands[i].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.initial_upper:
                        outer_node.operands[i].parent = None
                elif operand.operator == 'O' and operand.operands[0].operator == 'G' and operand.operands[0].is_derived() and operand.operands[0].parent == G_node.identifier and operand.operands[0].and_element == arg.and_element:
                    operand.operands[0] = operand.operands[0].shallow_copy()
                    operand.operands[0].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.initial_upper:
                        operand.operands[0].parent = None
            if G_counter == 0:
                extract = arg.shallow_copy()
                extract.lower = arg.lower + G_node.lower
                extract.upper = extract.initial_upper = arg.upper + G_node.lower
                extract.parent = G_node.identifier if G_node.lower < G_node.initial_upper else None
                extract.set_initial_time()
                return extract
            else:
                return None
        elif arg.operator in {'&&', ','}:
            # Recursive application
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, short, False) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            if arg.operands:
                return arg
            else:
                return None
        elif arg.operator in {'||', '->'}:
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, False, False) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            return arg
        else:
            raise ValueError(f"Unknown operator: {arg.operator}")

    outer_node = outer_node.shallow_copy()
    G_nodes = []
    for i, operand in enumerate(outer_node.operands):
        if operand.operator == 'G' and operand.lower == current_time:
            # We need a shallow_copy for GF because it changes operand.lower
            new_operand = operand.shallow_copy() if operand[0].operator == 'F' else operand
            G_nodes.append(new_operand)
            if operand.lower < operand.upper:
                # Substitute with ['O', ['G', 'a', 'b', ['p']]]
                outer_node.operands[i] = Node('O', new_operand)
            else:
                if (operand[0].check_boolean_closure(lambda n: n.operator == 'P') and
                    any(other.lower_bound() == operand.lower for j, other in enumerate(outer_node.operands) if (j != i and other is not None))):
                    outer_node.jump1 = True
                # I remove element if  a == b
                outer_node.operands[i] = None
    outer_node.operands = [x for x in outer_node.operands if x is not None]

    formula_opts = tableau_opts['formula_opts']
    for G_node in G_nodes:
        assert G_node.initial_time != '-1'
        # Decompose original node
        new_operands = modify_argument(G_node.operands[0], G_node, formula_opts, formula_opts)
        if new_operands:
            outer_node.operands.append(new_operands)
        if G_node.lower >= G_node.initial_upper:
            # Set parent to None (we do it here so that it doesn't interfere with modify_argument)
            for other in outer_node.operands:
                temp_op = other.operands[0] if other.operator == 'O' else other
                if temp_op.operator in {'G', 'U', 'R', 'F'} and temp_op.is_derived() and temp_op.parent == G_node.identifier:
                    temp_op.parent = None
    return [outer_node], len(G_nodes) > 0


def decompose_F(node, index):
    assert index >= 0 and node is not None

    F_formula = node[index]
    lower_bound = F_formula.lower
    current_time = F_formula.current_time

    def modify_argument(arg):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modify temporal bounds
            extract = arg.shallow_copy()
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.current_time = current_time
            extract.set_initial_time()
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Recursive application
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Unknown operator: {arg.operator}")

    # Node where we postpone satisfaction of F
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, Node('O', F_formula))

    # Node where the operand holds
    new_node2 = node.shallow_copy()
    new_node2.replace_operand(index, modify_argument(F_formula.operands[0]))
    if (F_formula.lower == F_formula.upper and
        F_formula[0].check_boolean_closure(lambda n: n.operator == 'P') and
        any(other.lower_bound() == F_formula.lower for j, other in enumerate(node.operands) if j != index)):
        new_node2.jump1 = True

    return new_node2, new_node1


def decompose_U(formula, index):
    '''
    :return: pUq becomes q OR p and OU
    '''
    assert index >= 0 and formula is not None
    U_formula = formula[index]
    assert U_formula.initial_time != '-1'
    first_operand = formula[index].operands[0]
    second_operand = formula[index].operands[1]

    def modify_argument(arg, derived):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modify bounds
            extract = arg.shallow_copy()
            extract.lower = arg.lower + U_formula.lower
            extract.upper = arg.upper + U_formula.lower
            extract.current_time = U_formula.current_time
            if derived:
                extract.parent = U_formula.identifier
            extract.set_initial_time()
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Recursive application
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op, derived) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Unknown operator: {arg.operator}")

    # Node in which U is not satisfied (p, OU)
    new_node1 = formula.shallow_copy()
    new_operand = modify_argument(first_operand.shallow_copy(), True)
    new_node1.replace_operand(index, Node('O', U_formula))
    new_node1.operands.extend([new_operand])

    # Node where U is satisfied (q)
    new_node2 = formula.shallow_copy()
    new_node2.replace_operand(index, modify_argument(second_operand.shallow_copy(), False))
    if (U_formula.lower == U_formula.upper and
        U_formula[1].check_boolean_closure(lambda n: n.operator == 'P') and
        any(other.lower_bound() == U_formula.lower for j, other in enumerate(formula.operands) if j != index)):
        new_node2.jump1 = True

    # When I have OU[b,b] I set is_derived to false in the operands derived from that U
    del_parent = new_node2.operands + (new_node1.operands if U_formula.lower == U_formula.upper else [])
    for operand in del_parent:
        temp_op = operand.operands[0] if operand.operator == 'O' else operand
        if temp_op.parent == U_formula.identifier:
            temp_op.parent = None

    return [new_node2, new_node1]



def decompose_R(formula, index, mltl):
    '''
    :return:    p R[a,b] q becomes (q and O(pRq)) OR p
    '''
    assert index >= 0 and formula is not None
    R_formula = formula[index]
    assert R_formula.initial_time != '-1'
    first_operand = formula[index].operands[0]
    second_operand = formula[index].operands[1]

    def modify_argument(arg, derived):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modify temporal bounds
            extract = arg.shallow_copy()
            extract.lower = arg.lower + R_formula.lower
            extract.upper = arg.upper + R_formula.lower
            extract.current_time = R_formula.current_time
            if derived:
                extract.parent = R_formula.identifier
            extract.set_initial_time()
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Recursive application
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op, derived) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Unknown operator: {arg.operator}")

    # Node in which U is not satisfied (q, OU)
    new_node1 = formula.shallow_copy()
    if R_formula.lower < R_formula.upper:
        new_operand = modify_argument(second_operand.shallow_copy(), True)
        new_node1.replace_operand(index, Node('O', R_formula))
        new_node1.operands.extend([new_operand])
    else:
        new_operand = modify_argument(second_operand.shallow_copy(), False)
        new_node1.replace_operand(index, new_operand)
        if (second_operand.check_boolean_closure(lambda n: n.operator == 'P') and
            any(op.lower_bound() == R_formula.lower for j, op in enumerate(new_node1.operands) if j != index)):
            new_node1.jump1 = True

    # Node where R is satisfied (p)
    new_node2 = formula.shallow_copy()
    if mltl:
        new_node2.replace_operand(index, modify_argument(first_operand.shallow_copy(), False), modify_argument(second_operand.shallow_copy(), False))
    else:
        new_node2.replace_operand(index, modify_argument(first_operand.shallow_copy(), False))

    # when OR[b,b] I remove is_derived from operands that came from the decomposition of that R
    del_parent = new_node2.operands + (new_node1.operands if R_formula.lower == R_formula.upper else [])
    for operand in del_parent:  
        temp_op = operand.operands[0] if operand.operator == 'O' else operand
        if temp_op.parent == R_formula.identifier:
            temp_op.parent = None

    return [new_node2, new_node1]

def decompose_and(node):
    new_node = node.shallow_copy()
    # We decomose all AND operators, but only at the first level
    has_decomposed = False
    for i, operand in enumerate(node.operands):
        if operand.operator in {'&&', ','}:
            new_node.replace_operand(i, *operand.operands)
            has_decomposed = True

    return [new_node], has_decomposed


def decompose_or(tableau_opts, node, index):
    assert index >= 0 and node is not None
    # I compute a score to decide the order in which the operands of OR are returned
    def complexity_score(or_node, node):
        def check_match(sub1, sub2):
            return sub1.operator == sub2.operator and ((sub1.operator == 'P' and sub1.operands == sub2.operands) or (
                        sub1.operator == '!' and sub1[0].operands == sub2[0].operands))
        """Compute score penalizing nested operators."""
        # 1. Operatori con solo 'P' → Migliori
        if or_node.operator in {'P', '!'}:
            for operand in node.operands:
                if check_match(or_node, operand):
                    return -1
            return 0
        if or_node.operator in {'&&', ','} and all(op.operator == 'P' for op in or_node.operands):
            return 1
        if or_node.operator == '->' and all(op.operator == 'P' for op in or_node.operands):
            return 2
        if or_node.operator == '||' and all(op.operator == 'P' for op in or_node.operands):
            return 3

        # 2. Temporal operators without complex nesting
        if or_node.operator in {'G', 'F', 'U', 'R'}:
            # I penalize based on time horizon of operator
            score = 10 + (or_node.upper - or_node.lower)

            # Extra penalization if temporal operator is nested with another temporal operator
            if or_node.operator == 'G' and or_node.operands[0].operator in {'G', 'F', 'U', 'R'}:
                score += 20  # nested G → bad case
            elif or_node.operator == 'U' and or_node.operands[0].operator in {'G', 'F', 'U', 'R'}:
                score += 15  # nested U with temporal operator in first operand → bad case
            elif or_node.operator == 'R' and or_node.operands[1].operator in {'G', 'F', 'U', 'R'}:
                score += 15  # nested R with temporal operator in second operand → bad case

            return score

        # 3. Logical operators
        if or_node.operator == '->':
            return 30 + len(or_node.operands)
        elif or_node.operator == '&&':
            return 40 + len(or_node.operands)
        elif or_node.operator == '||':
            return 50 + len(or_node.operands)
        elif or_node.operator == ',':
            return 60 + len(or_node.operands)
        
        raise ValueError(f"Unknown operator: {or_node.operator}")

    res = []
    if tableau_opts['children_order_opts']:
        or_operands = sorted(node[index].operands, key=lambda op: complexity_score(op, node))
    else:
        or_operands = node[index].operands
    for or_operand in or_operands:
        new_node = node.shallow_copy()
        if or_operand.is_derived() and or_operand.or_element > -1:
            z = 0
            for element in new_node.operands:
                if element.operator == 'G' and element.parent == or_operand.parent and element.or_element == or_operand.or_element:
                    z += 1
                    element.upper = or_operand.upper
                elif element.operator == 'O' and element.operands[0].operator == 'G' and element.operands[0].is_derived() and element.operands[0].parent == or_operand.parent and element.operands[0].or_element == or_operand.or_element:
                    z += 1
                    element.operands[0].upper = or_operand.upper
            if z == 0:
                new_node.replace_operand(index, or_operand)
            else:
                # We modified some exisiting G, so we don't need to add more formulas
                del new_node.operands[index]
        else:
            new_node.replace_operand(index, or_operand)
        res.append(new_node)
    return res


def decompose_imply_classic(tableau_data, node, index, mode='sat'):
    '''
    :return: decomposes p->q as not(p) OR (p and q)
    '''
    assert index >= 0 and node is not None

    imply_formula = node[index]
    lhs = imply_formula.operands[0]
    rhs = imply_formula.operands[1]
    
    if lhs.id_implication == -1:
        lhs.id_implication = 0
    if rhs.id_implication == -1:
        rhs.id_implication = 1

    def merge_derived_g_nodes(imply_op, new_node):
        # Looks for derived 'G' nodes in the new node
        if tableau_data.tableau_opts['formula_opts']:
            for i, operand in enumerate(new_node.operands):
                if operand.operator == 'G' and operand.parent == imply_op.parent and operand.is_derived() and operand.id_implication == imply_op.id_implication:
                    # We are modifying the existing G node, so we need to make a copy
                    new_node.operands[i] = operand.shallow_copy()
                    new_node.operands[i].upper = imply_op.upper
                    return None
        return imply_op

    # lhs of the implication
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, push_negation(Node('!', lhs)))
    new_node1[index].set_initial_time()

    # rhs of the implication
    new_node2 = node.shallow_copy()
    new_lhs, new_rhs = lhs, rhs
    if not tableau_data.tableau_opts['formula_opts']:
        new_lhs = None
    elif lhs.operator == 'G' and lhs.is_derived():
        new_lhs = merge_derived_g_nodes(lhs, new_node2)
    if rhs.operator == 'G' and rhs.is_derived():
        new_rhs = merge_derived_g_nodes(rhs, new_node2)
    new_node2.replace_operand(index, *(x for x in [new_lhs, new_rhs] if x is not None))

    if imply_formula.identifier is not None and mode == 'strong_sat':
        skip = imply_formula.identifier in new_node2.satisfied_implications
        new_node2.satisfied_implications.add(imply_formula.identifier)
    else:
        # TODO this is needed because sometimes imply_formula.identifier is None (req_cps): find out why and fix it
        skip = True

    if tableau_data.tableau_opts['children_order_opts']:
        # heuristics:if in the formula I already have the expression of the antecedent that should be true
        # I return first the branch in which the antecedent is evaluated to true, to avoid a rejected branch
        def check_match(sub1, sub2):
            return sub1.operator == sub2.operator and ((sub1.operator == 'P' and sub1.operands == sub2.operands) or (sub1.operator == '!' and sub1[0].operands == sub2[0].operands))
        if lhs.operator in {'P', '!'}:
            for operand in node.operands:
                if check_match(lhs, operand):
                    return new_node2, new_node1
        elif lhs.operator in {'&&', ',', '||'}:
            for element in lhs.operands:
                for operand in node.operands:
                    if check_match(element, operand):
                        return new_node2, new_node1

        if mode == 'sat' or new_node2.satisfied_implications == tableau_data.number_of_implications or (mode == 'strong_sat' and skip):
            return new_node1, new_node2
        else:
            return new_node2, new_node1
    else:
        return new_node1, new_node2


def decompose_imply_new(node, index):
    '''
    same ad previous function, but it avoids vacuously true cases (those in which antecedent is never evaluated to true)
    '''

    imply_formula = node[index]
    lhs = imply_formula.operands[0]  # antecedent
    rhs = imply_formula.operands[1]  # consequent

    assert index >= 0 and node is not None
    new_node2 = node.shallow_copy()
    new_node2.replace_operand(index, lhs, rhs)
    if node.operands[index].identifier is not None:
        new_node2.satisfied_implications.add(node.operands[index].identifier)
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, push_negation(Node('!', lhs)))
    new_node1 = push_negation(new_node1)
    return new_node1, new_node2

def simplify_F(node):
    '''
    Simplify formula according to the rule
    F[a,b] p && F[c,d] p <-> F[c,d] p whenever c >= a && d <= b
    '''
    assert node.operator == ','
    remove_indices = []
    F_formulas = {}
    for i, formula in enumerate(node.operands):
        if formula.operator == 'F':
            operand = formula[0]
            if operand in F_formulas:
                for j, F_formula in F_formulas[operand]:
                    if F_formula.lower >= formula.lower and F_formula.upper <= formula.upper:
                        remove_indices.append(i)
                    elif formula.lower >= F_formula.lower and formula.upper <= F_formula.upper:
                        remove_indices.append(j)
                        # We could also remove (j, F_formula) from the set, but we would have to do it out of the loop
            else:
                F_formulas[operand] = {(i, formula)}
    for i in sorted(remove_indices, reverse=True):
        del node.operands[i]
    return node


def has_temporal_operator(node):
    '''
    :param node: Node containing a formula
    :return: True if the formula contains any temporal operator
    '''
    match node.operator:
        case 'G' | 'F' | 'U' | 'R':
            return True
        case '&&' | '||' | ',' | '!' | '->':
            return any(has_temporal_operator(operand) for operand in node)
    return False

def is_complex_temporal_operator(node):
    match node.operator:
        case 'G' | 'U':
            return has_temporal_operator(node[0])
        case 'R':
            return has_temporal_operator(node[1])
    return False

def flagging(node):
    '''
    :param node:
    :return: True if the node contains any `problematic` operators
    '''
    match node.operator:
        case ',' | '&&' | '||' | '!' | '->':
            return any(flagging(operand) for operand in node)
        case 'O':
            match node[0].operator:
                case 'G' | 'U':
                    return has_temporal_operator(node[0][0])
                case 'R':
                    return has_temporal_operator(node[0][1])
            return False
    return False

def extract_time_instants(node, flag):
    """
    :return: it return the extrema of all time interval of temporal operators in the formula
    as a vector in ascending order
    (does not include bounds of derived operators)
    """
    time_instants = []
    if flag:
        for elem in node:
            if elem.operator in {'G', 'F', 'U', 'R'} and not elem.is_derived():
                time_instants.append(elem.lower)
                time_instants.append(elem.upper)
            elif elem.operator == 'O' and not elem.operands[0].is_derived():
                time_instants.append(elem.operands[0].lower)
                time_instants.append(elem.operands[0].upper)
    else:
        for elem in node:
            if elem.operator in {'G', 'F', 'U', 'R'}:
                time_instants.append(elem.lower)
                time_instants.append(elem.upper)
            elif elem.operator == 'O':
                time_instants.append(elem.operands[0].lower)
                time_instants.append(elem.operands[0].upper)

    return sorted(time_instants)

def decompose_jump(tableau_data, node):
    '''
    Checks if the case is non-problematic (in which you can always jump to the next min in the formula
    or if it is problematic (you cannot always jump, when you do not meet jump conditions you have to set jump = 1)
    '''
    assert node.operator == ','
    trace_stack = tableau_data.trace_stack
    if trace_stack is not None:
        trace_stack.append([])

    flag = flagging(node)
    time_instants = extract_time_instants(node, flag)
    if not flag:  # no problematic operator is currently active
        if not time_instants:
            # there are no temporal operators, we just return None
            return None
        if node.jump1:
            new_time = node.current_time + 1
        else:
            # I find the next min in the vector of time instants
            indice = bisect.bisect_right(time_instants, node.current_time)
            new_time = time_instants[indice]
        
        new_operands = []
        for and_operand in node.operands:
            if and_operand.operator not in {'P', '!', 'O'}:
                new_operands.append(and_operand)
            elif and_operand.operator == 'O' and and_operand.operands[0].lower < and_operand.operands[0].upper:
                sub_formula = and_operand.operands[0].shallow_copy()
                sub_formula.lower = new_time
                new_operands.append(sub_formula)
            elif trace_stack is not None and and_operand.operator in {'P', '!'}:
                trace_stack[-1].append(str(and_operand))

        if trace_stack is not None:
            repetitions = new_time - node.current_time - 1
            trace_stack.extend([trace_stack[-1]] * repetitions)

        if new_operands:
            new_node = node.shallow_copy()
            new_node.jump1 = False
            new_node.operands = new_operands
            new_node.current_time = new_time
            if tableau_data.tableau_opts['formula_opts'] and len(new_node.operands) > 1:
                simplify_F(new_node)
            return [new_node]
        else:
            return None
    else:  # problematic case
        # We first compute the time jump
        if node.jump1:
            jump = 1
            node.jump1 = False
        else:
            must_jump_1 = False
            for and_operand in node.operands:
                # I check problematic nested operator to compute the jump
                # I verify if for the operator I reached the threshold to jump, if yes I compute the jump
                # otherwise jump = 1
                # Once I have computed the jump for all problematic operators I select the min and jump
                if and_operand.operator == 'O' and not and_operand.operands[0].is_derived() and and_operand.operands[0].operator in {'G', 'U', 'R'}:
                    max_upper = -1
                    o_operand = and_operand.operands[0]
                    if o_operand.operator in {'G', 'U'}:
                        max_upper = o_operand.operands[0].get_max_upper()
                    elif o_operand.operator == 'R':
                        max_upper = o_operand.operands[1].get_max_upper()

                    must_jump_1 = must_jump_1 or max_upper == -1 or o_operand.lower < o_operand.initial_time + max_upper

            if must_jump_1:
                jump = 1
            else:
                indice = bisect.bisect_right(time_instants, node.current_time)
                jump = time_instants[indice] - node.current_time
        # Now we build the new node after the jump
        new_node_operands = []
        for and_operand in node.operands:
            if and_operand.operator in {'F', 'G', 'U', 'R'} and (jump == 1 or not and_operand.is_derived()):
                new_node_operands.append(and_operand)
            elif and_operand.operator == 'O' and and_operand.operands[0].lower < and_operand.operands[0].upper:
                if jump == 1:
                    sub_formula = and_operand.operands[0].shallow_copy()
                    sub_formula.lower = sub_formula.lower + jump
                    new_node_operands.append(sub_formula)
                else:
                    if and_operand.operands[0].is_derived():  # here I need to add jump to both lower and upper extremum of the interval
                        sub_formula = and_operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        sub_formula.upper = sub_formula.upper + jump
                        new_node_operands.append(sub_formula)
                    else:
                        sub_formula = and_operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        new_node_operands.append(sub_formula)
            elif trace_stack is not None and and_operand.operator in {'P', '!'}:
                trace_stack[-1].append(str(and_operand))

        if trace_stack is not None:
            # I add to the trace the atomic elements as many times ad the jump
            trace_stack.extend([trace_stack[-1]] * (jump - 1))
        
        new_node = node.shallow_copy()
        new_node.operands = new_node_operands
        new_node.current_time = node.current_time + jump
        if tableau_data.tableau_opts['formula_opts'] and len(new_node.operands) > 1:
            simplify_F(new_node)

        # We build a simplified node without complex nested operators that implies new_node
        simple_node_operands = list(filter(lambda n: not is_complex_temporal_operator(n), new_node.operands))
        
        if not tableau_data.tableau_opts['simple_nodes_first'] or len(simple_node_operands) == len(new_node.operands) or not simple_node_operands:
            return [new_node]
        else:
            simple_node = new_node.shallow_copy()
            simple_node.operands = simple_node_operands
            simple_node.siblings_imply = True
            return [simple_node, new_node]


def local_consistency_check(local_solver, node):
    '''
    :return: True if node is consistent, False otherwise
    '''
    for operand in node.operands:
        match operand.operator:
            case 'O':
                if operand.operator == 'O' and operand[0].operator in {'F', 'U'} and operand[0].lower == operand[0].upper:
                    return False
            case 'P':
                if operand[0] in {'<', '<=', '>', '>=', '==', '!='}:
                    local_solver.add_real_constraint(False, operand)
                else: # Boolean variable
                    prop = operand[0]
                    if prop == 'false':
                        return False # we have false in the upper level of a node
                    elif prop == 'true':
                        continue # if we have true in the upper level of a node we can just ignore it
                    local_solver.add_boolean_constraint(False, prop)
            case '!':
                if operand[0][0] in {'<', '<=', '>', '>=', '==', '!='}:
                    local_solver.add_real_constraint(True, operand[0])
                else: # Boolean variable
                    prop = operand[0][0]
                    if prop == 'true':
                        return False # we have !true in the upper level of a node
                    elif prop == 'false':
                        continue # if we have !false in the upper level of a node we can just ignore it
                    local_solver.add_boolean_constraint(True, prop)

    return local_solver.check()


def add_tree_child(tableau_data, G, parent_label, child):
    tableau_data.counter += 1
    if isinstance(child, str):
        child_label = child + ' ' + str(tableau_data.counter)
    else:
        child.counter = tableau_data.counter
        child_label = child.to_label()
    G.add_node(child_label)
    G.add_edge(parent_label, child_label)

def add_rejected(tableau_data, node):
    if tableau_data.tableau_opts['memoization'] and not check_rejected(tableau_data, node):
        #print(node)
        bisect.insort_left(tableau_data.rejected_store, node, key=Node.get_imply_sort_key)

def check_rejected(tableau_data, node):
    if not tableau_data.tableau_opts['memoization']:
        return False
    node.sort_operands()
    max_lower = max((op.lower for op in node.operands if op.operator in {'G', 'F', 'U', 'R'}))
    i = bisect.bisect_left(tableau_data.rejected_store, node.get_imply_sort_key(max_lower), key=Node.get_imply_sort_key)
    for rejected in tableau_data.rejected_store[i:]:
        if node.implies_quick(rejected):
            if tableau_data.verbose:
                print('Rejecting', node, ' because it implies rejected node ', rejected)
            return True
        if node.operands[-1].get_imply_search_key() < rejected.operands[0].get_imply_search_key():
            return False
    return False

def add_children(tableau_data, local_solver, node, depth, last_spawned, max_depth, current_time):
    if local_solver is None:
        local_solver = LocalSolver()
    mode = tableau_data.mode

    if depth >= max_depth:
        print('Max depth reached!')
        return None

    if tableau_data.tree:
        node_label = node.to_label()

    current_time = node.current_time
    local_solver.push()
    children = decompose(tableau_data, local_solver, node, current_time)
    if children is None:
        local_solver.pop()
        if tableau_data.verbose:
            print('No more children in this branch')
        if tableau_data.trace_stack is not None:
            # I add last element otherwise it would not be added since it does not go through decompose_jump
            for element in node.operands:
                if element.operator in {'P', '!'}:
                    tableau_data.trace_stack[-1].append(str(element))
        if mode in {'sat', 'complete'}:
            return True
        elif mode == 'strong_sat':
            return len(node.satisfied_implications) == tableau_data.number_of_implications
    if tableau_data.verbose:
        for child in children:
            print(child)

    child_queue = []
    for child in children:
        if child != 'Rejected':
            if child.siblings_imply:
                if mode == 'sat':
                    if check_rejected(tableau_data, child):
                        # All other children imply this one, so they'll be rejected
                        child_queue = []
                        if tableau_data.tree:
                            add_tree_child(tableau_data, tableau_data.tree, node_label, 'Rejected (memo)')
                        break
                    else:
                        # Children implied by others must be analyzed first
                        child_queue.insert(0, child)
            else:
                if mode != 'sat' or child.current_time == current_time or not check_rejected(tableau_data, child):
                    child_queue.append(child)
                elif tableau_data.tree and mode == 'sat':
                    add_tree_child(tableau_data, tableau_data.tree, node_label, child)
                    node_label = child.to_label()
                    child = 'Rejected (memo)'
        if tableau_data.tree:
            add_tree_child(tableau_data, tableau_data.tree, node_label, child)
    
    if all(c.siblings_imply for c in child_queue):
        child_queue = []

    if mode == 'complete':
        complete_result = False

    if tableau_data.parallel and mode == 'sat' and depth - last_spawned > 30 and len(child_queue) > 1: # add 'strong_sat'
        # print("spawning", node)
        # print("children: ", str([child for child in child_queue]))

        pool = fs.ProcessPoolExecutor(max_workers=2)
        try:
            futures = [pool.submit(
                add_children,
                tableau_data,
                None, # z3 stuff can't be pickled
                child, depth + 1, depth, max_depth, current_time
            ) for child in child_queue]
            for fut in fs.as_completed(futures):
                if fut.result():
                    local_solver.pop()
                    return True
        finally:
            # We wait for running subtask to finish, otherwise they remain hanging.
            # TODO maybe use Event to stop them asap
            pool.shutdown(wait=True, cancel_futures=True)
    else:
        max_depth_reached = False
        for child in child_queue:
            # If the child comes from a temporal jump, we need a new, empty solver
            child_solver = local_solver if child.current_time == current_time else local_solver.get_empty_solver()
            child_res = add_children(tableau_data, child_solver, child, depth + 1, last_spawned, max_depth, current_time)
            if child_res:
                if not child.siblings_imply:
                    if mode == 'complete':
                        complete_result = True
                    else: # mode in {'sat', 'strong_sat'}
                        local_solver.pop()
                        return True
            elif child_res is None:
                max_depth_reached = True
            elif mode == 'sat' and child.current_time > current_time:
                add_rejected(tableau_data, child)
                if child.siblings_imply:
                    # All other siblings will be rejected
                    break

    local_solver.pop()

    if mode in {'sat', 'strong_sat'}:
        if max_depth_reached:
            return None
        return False
    else: # mode == 'complete'
        if not complete_result and max_depth_reached:
            return None
        return complete_result

def build_decomposition_tree(tableau_data, root, max_depth):
    """
    : return:
        if mode in {'sat', 'complete'}:
            True if the tableau has an accepting branch rooted at node,
            False if the tableau has only rejected branches rooted at node,
            None if we reached max_dept without finding an accepting branch
        if mode == 'strong_sat':
            True if the tableau has an accepting branch rooted at node and all implications are satisfied,
            False if the tableau has only rejected branches rooted at node,
            None if we reached max_dept without finding an accepting branch
    """
    root.current_time = 0
    root.jump1 = root.check_boolean_closure(lambda n: n.operator == 'P')

    if tableau_data.build_tree:
        root.counter = tableau_data.counter
        tableau_data.tree.add_node(root.to_label())

    if tableau_data.verbose:
        print(root)

    res = add_children(tableau_data, LocalSolver(), root, 0, 0, max_depth, root.current_time)

    if tableau_data.verbose:
        if res:
            print("The requirement set is consistent")
            if tableau_data.trace_stack is not None:
                print(f"A trace satisfying the requirements is: " + str([item for sublist in tableau_data.trace_stack for item in sublist]))
        else:
            print("The requirement set is not consistent")
    if tableau_data.build_tree or tableau_data.trace_stack is not None:
        return tableau_data.tree, tableau_data.trace_stack, res
    else:
        return res

class TableauData:

    def __init__(self, number_of_implications, mode, build_tree, return_trace, parallel, verbose, tableau_opts, mltl):
        self.number_of_implications = number_of_implications
        self.build_tree = build_tree
        self.mode = mode
        self.parallel = parallel
        self.verbose = verbose
        if build_tree:
            self.counter = 0
            self.tree = nx.DiGraph()
        else:
            self.tree = None
        self.trace_stack = [] if return_trace else None
        if mode == 'sat':
            self.rejected_store = []
        self.tableau_opts = tableau_opts
        self.mltl = mltl


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


default_tableau_opts = {
    'jump': True,
    'formula_opts': True,
    'children_order_opts': True,
    'early_local_consistency_check': True,
    'memoization': True,
    'simple_nodes_first': True,
    'g_f': True
}

def make_tableau(formula, max_depth, mode, build_tree, return_trace, parallel, verbose, mltl=False, tableau_opts=default_tableau_opts):
    if formula.operator != ',':
        formula = Node(',', formula)

    if not mltl:
        formula = modify_U_R(formula)
        formula = decompose_and(formula)[0][0] # modify_U_R may add &&'s
    
    formula = push_negation(formula)
    if tableau_opts['formula_opts']:
        shift_bounds(formula)
    if not tableau_opts['g_f']:
        formula = remove_GF(formula)
    assign_and_or_element(formula)
    number_of_implications = count_implications(formula)
    formula.set_initial_time()
    assign_identifier(formula)

    tableau_data = TableauData(number_of_implications, mode, build_tree, return_trace, parallel, verbose, tableau_opts, mltl)
    return build_decomposition_tree(tableau_data, formula, max_depth)



