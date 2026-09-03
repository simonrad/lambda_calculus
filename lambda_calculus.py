#!/usr/bin/env python3

'''
An interpreter (parser and evaluator) of lambda calculus code.
'''

import sys
from types import MappingProxyType # MappingProxyType is like a frozendict.
from collections.abc import Mapping # Used in type hints as Mapping[KT, VT].


# Done: Parse LC code
# Done: Evaluate LC code (lazily)
# Done: Implement basic templates
# Done: Print the Expr including its bindings: Substitute all the free variables with their bindings.

# TODO: Fully substitute (reduce) the resulting Ast
#   - Watch out for infinite recursion; in that case we cannot fully substitute.
# TODO: Compare the performance of reduction vs Expr.eval()
# TODO: Test eval on factorial of 5. It's fast! But is it correct?
# TODO: Interpret and print the resulting LC value nicely (e.g. true, 12, [4, 6, false])
# TODO: Consider adding syntax sugar: let{var1=expr1;var2=expr2;}(expr) -> (/var1.(/var2.expr)expr2)expr1
# TODO: Write some LC functions
#   - booleans
#   - pairs
#   - lists
#     - reverse
#   - binary numbers
#     - compare
#     - add
#     - subtract
#     - multiply
# TODO: Add some more test cases

# TODO: Alternative way of printing the evaluated Expr: Build the complete list of all unique Exprs, and print each Expr along with its required var name replacements (e.g. 'with x = x_11').
# TODO: Consider passing debug info about code location into parse() and Ast()


LAMBDA = '/' # The character to use as lambda, e.g. 'λ'

WRAP_DIRECTIVE = '#wrap_with_template'
WRAP_PLACEHOLDER = '{INSERT_WRAPPED_CODE}'

VARIABLE = 'var'
FUNCTION = 'func'
CALL = 'call'
AST_TYPES = (VARIABLE, FUNCTION, CALL)

class Ast:
    '''
    An Abstract Syntax Tree. Represents some lambda calculus code.
    '''
    def __init__(self, kind, *args):
        assert kind in AST_TYPES
        if kind == VARIABLE:
            assert len(args) == 1 # variable_name
            assert type(args[0]) is str
            self.variable_name = args[0]
            assert is_valid_identifier(self.variable_name)
        elif kind == FUNCTION:
            assert len(args) == 2 # variable_name, ast
            assert type(args[0]) is str
            assert type(args[1]) is Ast
            self.variable_name = args[0]
            self.function_body = args[1]
            assert is_valid_identifier(self.variable_name)
        elif kind == CALL:
            assert len(args) >= 2 # ast, ast, ...
            for arg in args:
                assert type(arg) is Ast
        self.kind = kind
        self.args = args

    def substitute(self, bindings: Mapping[str, Expr], nonfree_vars: frozenset[str], allow_unbound_vars = False):
        '''
        Returns self with all free variables replaced with their bindings.

        Any variables in nonfree_vars will not be replaced. These are function
        parameters that are not bound to a specific value, because the function
        is not yet applied.
        '''
        assert type(bindings) is MappingProxyType
        assert type(nonfree_vars) is frozenset
        if self.kind == VARIABLE:
            if self.variable_name in nonfree_vars:
                return self
            if allow_unbound_vars and self.variable_name not in bindings:
                return self
            assert self.variable_name in bindings, 'Unbound variable {!r}'.format(self.variable_name)
            return bindings[self.variable_name].to_substituted_ast(allow_unbound_vars)
        elif self.kind == FUNCTION:
            return Ast(
                FUNCTION,
                self.variable_name,
                self.function_body.substitute(bindings, nonfree_vars.union({self.variable_name}), allow_unbound_vars),
            )
        elif self.kind == CALL:
            substituted_args = tuple(
                arg.substitute(bindings, nonfree_vars, allow_unbound_vars)
                for arg in self.args
            )
            return Ast(CALL, *substituted_args)
        else:
            assert False

    def _to_shorter_ast_partially(self):
        '''
        Attempt to return a shorter version of self by substituting variables. This is best-effort.
        '''
        if self.kind == VARIABLE:
            return self
        elif self.kind == FUNCTION:
            return Ast(
                FUNCTION,
                self.variable_name,
                self.function_body.to_shorter_ast(),
            )
        elif self.kind == CALL:
            shorter_args = tuple(
                arg.to_shorter_ast()
                for arg in self.args
            )
            current_ast = Ast(CALL, *shorter_args)
            best_ast = current_ast
            best_ast_len = len(best_ast.to_code())
            for i in range(len(current_ast.args) - 1):
                f = current_ast.args[0]
                a = current_ast.args[1]
                remaining_args = current_ast.args[2:]
                if f.kind != FUNCTION:
                    # Evaluating f at this point would be complicated. Instead, give up.
                    break
                # Apply f to a.
                new_f = f.function_body.substitute(
                    MappingProxyType({f.variable_name: Expr(a, MappingProxyType({}))}),
                    frozenset({}),
                    allow_unbound_vars = True,
                )
                if len(remaining_args) > 0:
                    current_ast = Ast(CALL, *((new_f,) + remaining_args))
                else:
                    current_ast = new_f
                current_ast_len = len(current_ast.to_code())
                if current_ast_len < best_ast_len:
                    best_ast = current_ast
                    best_ast_len = current_ast_len
            return best_ast
        else:
            assert False

    def to_shorter_ast(self):
        '''
        Attempt to return a shorter version of self by substituting variables. This is best-effort.
        '''
        result = self
        old_len = len(result.to_code())
        while True:
            result = result._to_shorter_ast_partially()
            new_len = len(result.to_code())
            assert new_len <= old_len
            if new_len >= old_len:
                return result
            old_len = new_len

    def to_tuple(self):
        return (self.kind, *(arg if type(arg) is str else arg.to_tuple() for arg in self.args))

    def to_code(self, parens = False):
        if self.kind == VARIABLE:
            return self.variable_name
        elif self.kind == FUNCTION:
            result = '{}{}.{}'.format(LAMBDA, self.variable_name, self.function_body.to_code(False))
            return '(' + result + ')' if parens else result
        elif self.kind == CALL:
            result = ' '.join(arg.to_code(True) for arg in self.args)
            return '(' + result + ')' if parens else result

def is_valid_identifier(variable_name):
    return variable_name.replace('_', 'X').isalnum() and LAMBDA not in variable_name

def match_paren(lc_code: str, start_index: int):
    '''
    Returns the index of the matching closing paren.
    '''
    assert lc_code[start_index] == '('
    count = 0
    for i in range(start_index, len(lc_code)):
        c = lc_code[i]
        if c == '(':
            count += 1
        if c == ')':
            count -= 1
        if count == 0:
            return i
    assert False, 'Could not find matching close paren'

def remove_comments(lc_code: str):
    return '\n'.join(
        line.split('#', 1)[0] for line in lc_code.splitlines()
    )

def parse(lc_code: str):
    '''
    Returns an Ast of lc_code.
    Pre: Comments have already been removed from lc_code.
    '''
    lc_code = lc_code.strip()
    assert len(lc_code) > 0, 'Attempted to parse an empty code string'

    # Parse lc_code as a sequence of 1 or more Asts.
    # If it ends up being just 1 Ast, parse() resolves to that Ast.
    # If it ends up being 2 or more Asts, parse() resolves to a CALL Ast.
    i = 0
    ast_list = []
    while i < len(lc_code):
        if lc_code[i].isspace():
            i += 1
        elif lc_code[i] == LAMBDA:
            variable_name, function_body = lc_code[i+1:].split('.', 1)
            variable_name = variable_name.strip()
            ast_list.append(Ast(FUNCTION, variable_name, parse(function_body)))
            i = len(lc_code) # We've consumed up to the end of lc_code
        elif lc_code[i] == '(':
            index_of_close_paren = match_paren(lc_code, i)
            ast_list.append(parse(lc_code[i+1:index_of_close_paren]))
            i = index_of_close_paren + 1
        else:
            # Variable name or other identifier
            assert is_valid_identifier(lc_code[i]), 'Unexpected character {!r} in code {!r}'.format(lc_code[i], lc_code[max(i-20, 0) : i+21])
            variable_name = ''
            while i < len(lc_code) and is_valid_identifier(lc_code[i]):
                variable_name += lc_code[i]
                i += 1
            ast_list.append(Ast(VARIABLE, variable_name))

    assert len(ast_list) >= 1
    if len(ast_list) >= 2:
        return Ast(CALL, *ast_list)
    else:
        return ast_list[0]


class Expr:
    '''
    Allows you to lazily evaluate lambda calculus code.

    An Expr is an Ast plus some variable bindings.
    Think of an Expr as a lambda calculus 'value' that can be passed around or
    assigned to a variable.

    Any Expr can be evaluated (lazily). Once evaluated, an Expr will reduce to a
    lambda calculus 'value', which is a function. In other words, once
    evaluated, the Expr's Ast will be of kind FUNCTION.

    An Expr can point at another Expr, which means they are the same value.
    The data structure is: (ast, bindings) | pointer_to_another_expr
    '''
    def __init__(self, ast: Ast, bindings: Mapping[str, Expr]):
        assert type(ast) is Ast
        assert type(bindings) is MappingProxyType
        self.ast = ast
        self.bindings = bindings
        self.pointer = None # May point to another Expr. In that case, self.ast and self.bindings will be set to None.
        self.substituted_ast = None # A cached result to avoid recomputing it.

    def resolve(self):
        '''
        Returns the non-pointing Expr that self directly or indirectly points at, or self.
        '''
        if self.pointer is None:
            return self
        if self.pointer.pointer is None:
            return self.pointer
        result = self.pointer.resolve()
        self.pointer = result # Compress the chain of pointers to make future resolves faster.
        return result

    def apply(self, arg: Expr):
        '''
        Returns a new Expr that is the result of applying the function `self` to the argument `arg`.
        '''
        assert type(arg) is Expr
        self = self.eval()
        assert self.ast.kind == FUNCTION

        new_bindings = self.bindings.copy()
        new_bindings[self.ast.variable_name] = arg
        new_bindings = MappingProxyType(new_bindings)

        return Expr(
            ast = self.ast.function_body,
            bindings = new_bindings,
        )

    def _set_pointer(self, new_pointee: Expr):
        assert type(new_pointee) is Expr
        self.ast = None
        self.bindings = None
        self.substituted_ast = None
        self.pointer = new_pointee

    def _eval_partially(self):
        '''
        Makes some progress in evaluating self, unless self is already fully evaluated (i.e. reduced to a function definition).
        '''
        self = self.resolve()
        if self.ast.kind == FUNCTION:
            return
        elif self.ast.kind == VARIABLE:
            binding = self.bindings.get(self.ast.variable_name)
            assert binding is not None, 'Unbound variable {!r}'.format(self.ast.variable_name)
            self._set_pointer(binding)
        elif self.ast.kind == CALL:
            arg_exprs = tuple(
                Expr(arg_ast, self.bindings)
                for arg_ast in self.ast.args
            )
            assert len(arg_exprs) >= 2
            result = arg_exprs[0]
            for arg in arg_exprs[1:]:
                result = result.apply(arg)
            self._set_pointer(result)
        else:
            assert False

    def eval(self):
        '''
        Fully evaluates self. Afterwards, self.resolve().ast.kind will be FUNCTION.
        '''
        while self.resolve().ast.kind != FUNCTION:
            self._eval_partially()
        return self.resolve()

    def to_substituted_ast(self, allow_unbound_vars = False):
        '''
        Returns self.ast with all free variables replaced with their bindings.
        '''
        self = self.resolve()
        if self.substituted_ast is not None:
            return self.substituted_ast
        if len(self.bindings) == 0 and allow_unbound_vars:
            # There's nothing to substitute.
            return self.ast
        substituted_ast = self.ast.substitute(self.bindings, frozenset({}), allow_unbound_vars).to_shorter_ast()
        if not allow_unbound_vars:
            # We can't bluntly cache the result if allow_unbound_vars is True,
            # because it would cause future calls where allow_unbound_vars is False
            # to behave incorrectly.
            self.substituted_ast = substituted_ast
        return substituted_ast

    def to_code(self, parens = False):
        return self.to_substituted_ast().to_code(parens)


def apply_templates(lc_code: str):
    '''
    Finds any WRAP_DIRECTIVEs at the top of lc_code and applies them.
    '''
    templates = []
    for line in lc_code.splitlines():
        if not line.startswith(WRAP_DIRECTIVE):
            break
        filepath = line.removeprefix(WRAP_DIRECTIVE)
        filepath = remove_comments(filepath).strip()
        templates.append(filepath)
    templates.reverse() # Apply the templates in reverse order, so that the first one is the outer-most shell.
    for filepath in templates:
        with open(filepath, 'r') as f:
            contents = f.read()
            contents = remove_comments(contents)
        assert contents.count(WRAP_PLACEHOLDER) == 1, 'Template file {!r} must have exactly one {} in it'.format(filepath, WRAP_PLACEHOLDER)
        lc_code = '\n\n(\n' + lc_code + '\n)\n\n'
        lc_code = contents.replace(WRAP_PLACEHOLDER, lc_code)
    return lc_code


def eval_lc(lc_code: str):
    lc_code = apply_templates(lc_code)
    lc_code = remove_comments(lc_code)
    ast = parse(lc_code)
    expr = Expr(ast, MappingProxyType({}))
    return expr.eval()


def run_code_from_stdin():
    lc_code = sys.stdin.read()
    expr = eval_lc(lc_code)
    print(expr.to_code())


def print_code_from_stdin():
    lc_code = sys.stdin.read()
    lc_code = apply_templates(lc_code)
    lc_code = remove_comments(lc_code)
    print(lc_code)


def run_tests():
    parse_test_cases = (
        '(/x./y.x y z (y z) x) (/p.p) z',
    )

    print('Parse test cases:')
    for lc_code in parse_test_cases:
        test_does_pass = parse(lc_code).to_code() == lc_code
        print(' ', 'Pass' if test_does_pass else 'FAIL', ' ', lc_code)
        if not test_does_pass:
            print('    ' + lc_code)
            print('    ' + parse(lc_code).to_code())
            sys.exit(1)

    eval_test_cases = (
        # (input_lc_code, expected_output_lc_code)
        ('(/x./y./z.x x) (/x.x) zzz ((/x.x x) (/x.x x))',  '/x.x'),
    )

    print('Eval test cases:')
    for (input_lc_code, expected_output_lc_code) in eval_test_cases:
        actual_output_lc_code = eval_lc(input_lc_code).to_code()
        test_does_pass = actual_output_lc_code == expected_output_lc_code
        print(' ', 'Pass' if test_does_pass else 'FAIL', ' ', input_lc_code, ' -> ', expected_output_lc_code)
        if not test_does_pass:
            print('    expected: ' + expected_output_lc_code)
            print('    actual:   ' + actual_output_lc_code)
            sys.exit(1)


if __name__ == '__main__':
    if len(sys.argv) == 2 and sys.argv[1] == 'test':
        run_tests()
    elif len(sys.argv) == 2 and sys.argv[1] == 'run':
        run_code_from_stdin()
    elif len(sys.argv) == 2 and sys.argv[1] == 'print':
        print_code_from_stdin()
    else:
        sys.exit('Usage: {} <run|test>'.format(sys.argv[0]))


