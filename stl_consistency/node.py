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

class Node:
    def __init__(self, *args):
        if len(args) == 0:
            return # We create an empty object to be filled later
        operator = args[0]
        args = args[1:]

        # If you add more fields, remember to update shallow_copy
        self.current_time = None
        self.initial_time = '-1' # the initial time of the outer operator of a nested operator
        self.identifier = None   # a number that uniquely identifies (some) formulas
        self.parent = None # if this formula comes from the decomposition of a nested temporal operand, contains the parent's identifier, None otherwise
        self.operator = operator
        self.id_implication = -1 # to identify from which element of an implication an operands has been extracted
        self.and_element = -1 # identifies univoc operands of && inside a G
        self.or_element = -1 # identifies univoc operands of || inside a G
        self.jump1 = False # needed because in some instances you can only jump 1 step to make sure you do not miss anything important
        self.siblings_imply = False
        if operator in {'&&', '||', ',', '!', 'O', '->', '<->'}:
            self.lower = self.upper = -1
            self.operands = list(args)
            if operator in {'&&', ','}:
                self.satisfied_implications = set()
        elif operator in {'G', 'F', 'U', 'R'}:
            self.lower = int(args[0])
            self.upper = int(args[1])
            self.operands = list(args[2:])
        elif operator in {'<', '<=', '>', '>=', '==', '!='}:
            self.lower = self.upper = -1
            self.operator = 'P'
            self.operands = [operator] + list(args)
        elif isinstance(operator, str) and len(args) == 0:
            self.lower = self.upper = -1
            self.operator = 'P'
            self.operands = [operator]
        else:
            print(operator, args)
            raise ValueError('Bad formula' + operator + str(args))

        self.initial_upper = self.upper # to remember the original upper bound when shifting bounds

        # Convert operands to Nodes, if any
        if self.operator != 'P' and len(self.operands) > 0 and not isinstance(self.operands[0], Node):
            self.operands = [Node(*op) for op in self.operands]

    def set_current_time(self, time):
        self.current_time = time
    
    def get_current_time(self):
        return self.current_time

    def lower_bound(self):
        if self.operator == 'O':
            return self.operands[0].lower
        return self.lower

    def upper_bound(self):
        if self.operator == 'O':
            return self.operands[0].upper
        return self.upper

    def is_derived(self):
        return self.parent is not None

    def replace_operand(self, index, new_operand, *more_new_operands):
        '''
        Replaces the operand at the given index with the new operand(s),
        appending operands other than the first to the end.
        '''
        self.operands[index] = new_operand
        self.operands.extend(more_new_operands)

    def shallow_copy(self):
        new = Node()
        new.current_time = self.current_time
        new.initial_time = self.initial_time
        new.identifier = self.identifier
        new.parent = self.parent
        new.operator = self.operator
        new.id_implication = self.id_implication
        new.and_element = self.and_element
        new.or_element = self.or_element
        new.jump1 = self.jump1
        new.siblings_imply = False
        new.lower = self.lower
        new.upper = self.upper
        new.initial_upper = self.initial_upper
        new.operands = self.operands.copy()
        if hasattr(self, 'satisfied_implications'):
            new.satisfied_implications = self.satisfied_implications.copy()
        return new

    def set_initial_time(self):
        '''
        Set the time at which the operator starts being active
        '''
        match self.operator:
            case 'G' | 'U':
                self.initial_time = self.lower
            case 'R':
                self.initial_time = self.lower
            case '&&' | '||' | ',' | '->':
                for operand in self.operands:
                    operand.set_initial_time()

    def to_list(self):
        '''
        Convert node to list representation
        '''
        if self.operator in {'&&', '||', ',', '!', 'O', '->', '<->'}:
            return [self.operator] + [op.to_list() for op in self.operands]
        elif self.operator in {'G', 'F', 'U', 'R'}:
            return [self.operator, self.lower, self.upper] + [op.to_list() for op in self.operands]
        elif self.operator == 'P':
            return self.operands
        else:
            raise ValueError('Unknown operator')

    def to_label(self):
        '''
        Use node.to_label(counter) to create a label for a graph node.
        The current time must be set before using this method with node.set_current_time()
        '''
        return " ".join([str(self), str(self.current_time), str(self.counter)])

    def get_min_lower(self, ignore_prop=True):
        '''
        :return: the minimum lower bound from temporal operators in the first-level
                 boolean closure of self, and -1 if self is purely propositional
        '''
        match self.operator:
            case '&&' | '||' | ',' | '->' | '!':
                return min(filter(lambda x: not ignore_prop or x >= 0, (op.get_min_lower(ignore_prop) for op in self.operands)))
            case _:
                # Works because in all non-temporal operators self.lower == -1
                return self.lower

    def get_max_upper(self):
        '''
        :return: the maximum upper bound from temporal operators in the first-level
                 boolean closure of self, and -1 if self is purely propositional
        '''
        match self.operator:
            case '&&' | '||' | ',' | '->' | '!':
                return max(op.get_max_upper() for op in self.operands)
            case _:
                # Works because in all non-temporal operators self.upper == -1
                return self.upper

    def __getitem__(self, i):
        '''
        Can be used to write e.g. node[0] to get the first operand
        '''
        return self.operands[i]

    def flatten(self):
        if self.operator in {'&&', '||', ','}:
            for i in range(len(self.operands)):
                self.operands[i].flatten()
                if self.operands[i].operator == self.operator:
                    self.operands[i:i+1] = self.operands[i].operands
        if self.operator != 'P':
            for op in self.operands:
                op.flatten()

    def __str__(self):
        match self.operator:
            case 'G' | 'F':
                return f"{self.operator}[{self.lower},{self.upper}] {self.operands[0]}"
            case 'O' | '!':
                return f"{self.operator} {self.operands[0]}"
            case 'U' | 'R':
                return f"({self.operands[0]}) {self.operator}[{self.lower},{self.upper}] ({self.operands[1]})"
            case '&&' | '||' | '->':
                return f"({f' {self.operator} '.join(str(op) for op in self.operands)})"
            case ',':
                return f"({', '.join(str(op) for op in self.operands)})"
            case 'P':
                if len(self.operands) == 1:
                    return self.operands[0]
                else:
                    return Node.arith_expr_to_string(self.operands)
            case _:
                raise ValueError(f'Operator {self.operator} not handled.')

    def arith_expr_to_string(expr):
        if isinstance(expr, list):
            if len(expr) == 3 and expr[0] in {'<', '<=', '>', '>=', '==', '!=', '+', '-', '/'}:
                return ' '.join([Node.arith_expr_to_string(expr[1]), expr[0], Node.arith_expr_to_string(expr[2])])
            elif len(expr) == 2 and expr[0] == 'abs':
                return f'|{Node.arith_expr_to_string(expr[1])}|'
            elif len(expr) == 1 and isinstance(expr[0], str):
                return expr[0]
            else:
                raise ValueError('Bad arithmetic expression')
        elif isinstance(expr, str):
            return expr
        else:
            raise ValueError('Bad arithmetic expression')

    def __hash__(self):
        '''
        Node: only hashes formula content!
        '''
        return hash((
            self.operator, self.lower, self.upper,
            Node.lists_to_tuples(self.operands) if self.operator == 'P' else tuple(self.operands)
        ))

    def __eq__(self, other):
        '''
        Note: only checks formula equality!
        '''
        return isinstance(other, Node) and (self.operator, self.lower, self.upper, self.operands) == (other.operator, other.lower, other.upper, other.operands)

    def __lt__(self, other):
        # TODO do something less ugly
        if self.operator == 'P' and len(self.operands) > 1:
            self_operands = [str(self.identifier)]
        else:
            self_operands = self.operands
        if other.operator == 'P' and len(other.operands) > 1:
            other_operands = [str(other.identifier)]
        else:
            other_operands = other.operands
        return (self.operator, self.lower, self.upper, self_operands) < (other.operator, other.lower, other.upper, other_operands)
    
    def __le__(self, other):
        # TODO do something less ugly
        if self.operator == 'P' and len(self.operands) > 1:
            self_operands = [str(self.identifier)]
        else:
            self_operands = self.operands
        if other.operator == 'P' and len(other.operands) > 1:
            other_operands = [str(other.identifier)]
        else:
            other_operands = other.operands
        return (self.operator, self.lower, self.upper, self_operands) <= (other.operator, other.lower, other.upper, other_operands)

    def __gt__(self, other):
        # TODO do something less ugly
        if self.operator == 'P' and len(self.operands) > 1:
            self_operands = [str(self.identifier)]
        else:
            self_operands = self.operands
        if other.operator == 'P' and len(other.operands) > 1:
            other_operands = [str(other.identifier)]
        else:
            other_operands = other.operands
        return (self.operator, self.lower, self.upper, self_operands) > (other.operator, other.lower, other.upper, other_operands)
    
    def __ge__(self, other):
        # TODO do something less ugly
        if self.operator == 'P' and len(self.operands) > 1:
            self_operands = [str(self.identifier)]
        else:
            self_operands = self.operands
        if other.operator == 'P' and len(other.operands) > 1:
            other_operands = [str(other.identifier)]
        else:
            other_operands = other.operands
        return (self.operator, self.lower, self.upper, self_operands) >= (other.operator, other.lower, other.upper, other_operands)

    def get_imply_sort_key(self, time=None):
        if time is None:
            time = self.current_time
        return (
            self.operator,
            self.operands,
            self.lower - time,
            self.upper - time
        )

    def get_imply_search_key(self):
        return (
            self.operator,
            self.operands
        )

    def sort_operands(self):
        self.operands.sort(key=lambda op: op.get_imply_sort_key(self.current_time))

    def implies_quick_inner(self, other, time_self, time_other):
        if self.operator != other.operator:
            return False
        match self.operator:
            case 'F':
                return other.lower - time_other <= self.lower - time_self and other.upper - time_other >= self.upper - time_self and self.operands[0] == other.operands[0]
            case 'G':
                return self.lower - time_self <= other.lower - time_other and self.upper - time_self >= other.upper - time_other and self.operands[0] == other.operands[0]
            case 'P':
                return self.operands[0] == other.operands[0]
            case '!':
                return self.operands[0].implies_quick_inner(other.operands[0], time_self, time_other)
            # TODO: U, R, etc
        return False

    def implies_quick(self, other):
        '''
        :return: True if we can quickly determine that self implies other, False otherwise
        Assumes both nodes' operands have been sorted with sort_operands
        '''
        self_lower_bounds = sorted({op.lower for op in self.operands if op.operator in {'G', 'F', 'U', 'R'}})
        len_self = len(self.operands)
        len_other = len(other.operands)
        for self_lower in self_lower_bounds:
            found = True
            j = 0
            for i in range(len_other):
                not_implies = order = True
                while j < len_self and not_implies and order:
                    if self.operands[j].implies_quick_inner(other.operands[i], self_lower, other.current_time):
                        not_implies = False
                        break
                    if other.operands[i].get_imply_search_key() < self.operands[j].get_imply_search_key():
                        order = False
                        break
                    j += 1
                if not_implies: # j >= len(self.operands) or not order:
                    # we break the loop because no operand in self implies other.operands[i]
                    found = False
                    break
            if found:
                return True
        return False

    def lists_to_tuples(l):
        if isinstance(l, list) or isinstance(l, tuple):
            return tuple(Node.lists_to_tuples(el) for el in l)
        return l

    def check_boolean_closure(self, pred):
        match self.operator:
            case '!' | '&&' | '||' | ',' | '->':
                return any(op.check_boolean_closure(pred) for op in self.operands)
            case _:
                return pred(self)
