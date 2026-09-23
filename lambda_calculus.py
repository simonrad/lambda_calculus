#!/usr/bin/env python3

'''
An interpreter (parser and evaluator) of lambda calculus code.
'''

import re
import sys
import time
from frozendict import frozendict # Third-party library [https://pypi.org/project/frozendict/]
from functools import cached_property, lru_cache, wraps
from types import NoneType
from typing import Any


# Done: Parse LC code
# Done: Evaluate LC code (lazily)
# Done: Implement basic templates
# Done: Print the Expr including its bindings: Substitute all the free variables with their bindings.
# Done: Enforce that CALLs are only 1 argument
# Done: Replace MappingProxyType with frozendict [https://pypi.org/project/frozendict/]
# Done: Consider adding syntax sugar: let{var1=expr1;var2=expr2;}(expr) -> (/var1.(/var2.expr)expr2)expr1
# Done: Test eval on factorial of 5. It's fast, and correct!
# Done: Add syntax sugar for binary number literals like 42
# Done: Test factorial of 7 with binary numbers natively. (It does not require a high recursion depth, unlike Church numerals.)
# Done: Interpret and print the resulting LC value nicely (e.g. true, 12, [4, 6, false])
# Done: Support returning a type identifier from the LC code (e.g. return (pair type_id value_of_that_type))

# TODO: Fully beta reduce (substitute) the resulting Ast
# TODO: Compare the performance of reduction vs Expr.eval()

# TODO: Write some LC functions
# TODO: Write tests of all the LC library functions

# TODO: Consider passing debug info about code location into parse() and Ast()


LAMBDA = '/' # The character to use as lambda, e.g. 'λ'

WRAP_DIRECTIVE = '#wrap_with_template'
WRAP_PLACEHOLDER = '{INSERT_WRAPPED_CODE}'

VARIABLE = 'var'
FUNCTION = 'func'
CALL = 'call'
AST_TYPES = (VARIABLE, FUNCTION, CALL)

MINIMAL_LIBRARY_PREFIX = '#wrap_with_template ./lambda_codes/minimal_library.template.lc\n'

TYPE_TAG_BOOL = 10
TYPE_TAG_BNN  = 11
TYPE_TAG_LIST = 12
NOT_TYPE_TAGGED = 'not_type_tagged'


def memoize_method(maxsize = 128):
    def decorator(func):
        @wraps(func)
        def method_wrapper(self, *args, **kwargs):
            # Create an instance-specific lru_cache if it doesn't exist
            cache_name = f'_cache_{func.__name__}'
            if not hasattr(self, cache_name):
                # Bind the cache to a local bound method wrapper
                bound_cache = lru_cache(maxsize = maxsize)(func.__get__(self, type(self)))
                setattr(self, cache_name, bound_cache)

            # Call the instance-specific cache
            return getattr(self, cache_name)(*args, **kwargs)
        return method_wrapper
    return decorator


class Ast:
    '''
    An Abstract Syntax Tree. Represents some lambda calculus code.
    '''
    def __init__(self, kind, *args):
        assert kind in AST_TYPES
        if kind == VARIABLE:
            assert len(args) == 1 # variable_name
            self.variable_name = args[0]
            assert type(self.variable_name) is str
            assert is_valid_identifier(self.variable_name), 'Not a valid variable name: {!r}'.format(self.variable_name)
        elif kind == FUNCTION:
            assert len(args) == 2 # variable_name, ast
            self.variable_name = args[0]
            self.function_body = args[1]
            assert type(self.variable_name) is str
            assert type(self.function_body) is Ast
            assert is_valid_identifier(self.variable_name), 'Not a valid variable name: {!r}'.format(self.variable_name)
        elif kind == CALL:
            assert len(args) == 2 # ast, ast
            self.function = args[0]
            self.argument = args[1]
            assert type(self.function) is Ast
            assert type(self.argument) is Ast
        else:
            assert False
        self.kind = kind
        self.args = args

    def substitute_exprs(self, bindings: frozendict[str, Expr], nonfree_vars: frozenset[str]) -> Ast:
        '''
        Returns self with all free variables replaced with their bindings.

        Any variables in nonfree_vars will not be replaced. These are function
        parameters that are not bound to a specific value, because the function
        is not yet applied.
        '''
        assert type(bindings) is frozendict
        assert type(nonfree_vars) is frozenset
        if self.kind == VARIABLE:
            if self.variable_name in nonfree_vars:
                return self
            assert self.variable_name in bindings, 'Unbound variable {!r}'.format(self.variable_name)
            return bindings[self.variable_name].to_substituted_ast()
        elif self.kind == FUNCTION:
            return Ast(
                FUNCTION,
                self.variable_name,
                self.function_body.substitute_exprs(bindings, nonfree_vars.union({self.variable_name})),
            )
        elif self.kind == CALL:
            substituted_args = tuple(
                arg.substitute_exprs(bindings, nonfree_vars)
                for arg in self.args
            )
            return Ast(CALL, *substituted_args)
        else:
            assert False

    def apply(self, arg: Ast) -> Ast:
        # TODO
        raise NotImplementedError('Ast.apply() is not yet implemented')

    def reduce(self, mode) -> Ast:
        # TODO
        assert mode in ('lazy_full', 'lazy_to_lambda')
        raise NotImplementedError('Ast.reduce() is not yet implemented')

    @cached_property
    def free_vars(self) -> frozenset[str]:
        if self.kind == VARIABLE:
            return frozenset((self.variable_name,))
        elif self.kind == FUNCTION:
            return self.function_body.free_vars - {self.variable_name}
        elif self.kind == CALL:
            return self.function.free_vars | self.argument.free_vars
        else:
            assert False

    def to_tuple(self):
        return (self.kind, *(arg if type(arg) is str else arg.to_tuple() for arg in self.args))

    def to_code(self, parens = False) -> str:
        if self.kind == VARIABLE:
            return self.variable_name
        elif self.kind == FUNCTION:
            result = '{}{}.{}'.format(LAMBDA, self.variable_name, self.function_body.to_code(False))
            return '(' + result + ')' if parens else result
        elif self.kind == CALL:
            result = '{} {}'.format(self.function.to_code(self.function.kind != CALL), self.argument.to_code(True))
            return '(' + result + ')' if parens else result
        else:
            assert False

def is_identifier_char(s: str):
    # Note that s can be more than one character.
    return s.replace('_', 'X').isalnum() and (LAMBDA not in s) and len(s) > 0

def is_valid_identifier(variable_name: str):
    return is_identifier_char(variable_name) and not variable_name[0].isdigit()

def is_space_or_empty(s: str):
    return s.isspace() or len(s) == 0

def match_paren(lc_code: str, start_index: int, open_paren = '(', close_paren = ')') -> int:
    '''
    Returns the index of the matching closing paren.
    '''
    assert len(open_paren) == 1
    assert len(close_paren) == 1
    assert lc_code[start_index] == open_paren
    count = 0
    for i in range(start_index, len(lc_code)):
        c = lc_code[i]
        if c == open_paren:
            count += 1
        if c == close_paren:
            count -= 1
        if count == 0:
            return i
    assert False, 'Could not find matching close paren {!r}'.format(close_paren)

def build_binary_natural_number_ast(n: int) -> Ast:
    assert type(n) is int
    assert n >= 0
    bits = [] # Starting with the least significant digit
    remaining = n
    while remaining != 0:
        bits.append(remaining & 1)
        remaining >>= 1
    assert len(bits) == 0 or bits[-1] == 1

    # Start with the most significant binary digit, and build a linked list of booleans.
    lc_code = 'nil'
    for bit in reversed(bits):
        assert bit in (0, 1)
        bit_bool_str = str(bool(bit)).lower()
        lc_code = '(cons {} {})'.format(bit_bool_str, lc_code)

    lc_code = MINIMAL_LIBRARY_PREFIX + lc_code
    result_ast = parse_fully(lc_code)
    assert len(result_ast.free_vars) == 0, 'Expected no free vars; got {!r}'.format(set(result_ast.free_vars))
    return result_ast

def parse_let_syntax_sugar(code_between_braces: str, main_code_between_parens: str) -> Ast:
    '''
    Support some syntax sugar: let{var1=expr1;var2=expr2;}(expr) -> (/var1.(/var2.expr)expr2)expr1
    Note that the final var=expr must end in a ';'.
    Note that the main expr (after the '}') must be wrapped in '()'.
    '''

    # Split the variable assignments by ';'. Ignore semicolons that occur inside a nested let{}.
    i = 0
    assignments_list = []
    current_assignment_start_index = 0
    while i < len(code_between_braces):
        c = code_between_braces[i]
        if c == ';':
            assignments_list.append(code_between_braces[current_assignment_start_index:i])
            current_assignment_start_index = i + 1
            i += 1
        elif c == '{':
            # Skip to the closing brace. We need to skip semicolons that occur inside a nested let{}.
            close_brace_index = match_paren(code_between_braces, i, '{', '}')
            i = close_brace_index + 1
        else:
            i += 1

    code_after_final_semicolon = code_between_braces[current_assignment_start_index:]
    assert is_space_or_empty(code_after_final_semicolon), "Inside a let{...} block, the final 'var=expr' assignment must end in a ';'"

    # Parse each assignment. (`var = expr`)
    assignment_pairs = []
    for code_str in assignments_list:
        assert '=' in code_str, "Assignment in let{{...}} does not contain an '=' sign: {!r}".format(code_str)
        var_name, expr_code = code_str.split('=', 1)
        var_name = var_name.strip()
        assert is_valid_identifier(var_name), "Text to the left of '=' sign in let{{...}} is not a valid variable name: {!r}".format(var_name)
        expr_ast = parse(expr_code)
        assignment_pairs.append((var_name, expr_ast))

    # Start with the main expression, and wrap with var bindings (by defining
    # and applying functions) starting with the last `var=expr` assignment.
    result_ast = parse(main_code_between_parens)
    for (var_name, var_expr_ast) in reversed(assignment_pairs):
        result_ast = Ast(CALL, Ast(FUNCTION, var_name, result_ast), var_expr_ast)
    return result_ast

def remove_comments(lc_code: str) -> str:
    return '\n'.join(
        line.split('#', 1)[0] for line in lc_code.splitlines()
    )

def parse(lc_code: str, as_a_list = False) -> Ast:
    '''
    Returns an Ast of lc_code.
    Pre: Comments have already been removed from lc_code.
    '''
    lc_code = lc_code.strip()
    if not as_a_list:
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
        elif lc_code[i] == '[':
            # Support some syntax sugar: [val1 val2 val3] for a singly linked list.
            index_of_close_bracket = match_paren(lc_code, i, '[', ']')
            values = parse(lc_code[i+1:index_of_close_bracket], as_a_list = True)
            # Build a linked list of the values.
            list_ast = NIL_AST
            for val in reversed(values):
                # Build list_ast = (cons {val} {list_ast}).
                first_call = Ast(CALL, CONS_AST, val)
                second_call = Ast(CALL, first_call, list_ast)
                list_ast = second_call
            ast_list.append(list_ast)
            i = index_of_close_bracket + 1
        elif lc_code[i:i+3] == 'let' and (match_obj := re.match(r'let\s*{', lc_code[i:])):
            # Support some syntax sugar: let{var1=expr1;var2=expr2;}(expr) -> (/var1.(/var2.expr)expr2)expr1
            # Note that the final var=expr must end in a ';'.
            # Note that the main expr (after the '}') must be wrapped in '()'.
            assert match_obj.span()[0] == 0
            open_brace_index = i + match_obj.span()[1] - 1
            assert lc_code[open_brace_index] == '{'
            close_brace_index = match_paren(lc_code, open_brace_index, '{', '}')
            open_paren_index = lc_code.index('(', close_brace_index + 1)
            assert is_space_or_empty(lc_code[close_brace_index+1:open_paren_index]), 'let{...} must be followed by parentheses (...)'
            close_paren_index = match_paren(lc_code, open_paren_index)
            ast_list.append(parse_let_syntax_sugar(
                lc_code[open_brace_index+1:close_brace_index],
                lc_code[open_paren_index+1:close_paren_index],
            ))
            i = close_paren_index + 1
        elif lc_code[i].isdigit():
            # Support natural number literals (like 42).
            # We turn these into a binary natural number.
            # (A BNN is a list of booleans, where the head is the least significant bit.)
            number_str = ''
            while i < len(lc_code) and lc_code[i].isdigit():
                number_str += lc_code[i]
                i += 1
            ast_list.append(build_binary_natural_number_ast(int(number_str)))
        else:
            # Variable name or other identifier
            assert is_identifier_char(lc_code[i]), 'Unexpected character {!r} in code {!r}'.format(lc_code[i], lc_code[max(i-20, 0) : i+21])
            variable_name = ''
            while i < len(lc_code) and is_identifier_char(lc_code[i]):
                variable_name += lc_code[i]
                i += 1
            ast_list.append(Ast(VARIABLE, variable_name))

    if as_a_list:
        return ast_list
    else:
        assert len(ast_list) >= 1
        result = ast_list[0]
        for ast in ast_list[1:]:
            result = Ast(CALL, result, ast)
        return result


class Expr:
    '''
    Allows you to lazily evaluate lambda calculus code.

    An Expr is an Ast plus variable bindings for all of the Ast's free variables.
    Think of an Expr as a closure, or as a lambda calculus 'value' that can be
    passed around or assigned to a variable.

    Note that an Expr will never have free variables.
    (More precisely, Expr.to_substituted_ast() will never have free variables,
    because the Expr.ast's free variables are all bound to the Expr.bindings.)

    Any Expr can be evaluated (lazily). Once evaluated, an Expr will resolve to
    an Ast of kind FUNCTION.

    An Expr can point at another Expr, which means they are the same value.
    The data structure is: (ast, bindings) | pointer_to_another_expr
    '''
    def __init__(self, ast: Ast, bindings: frozendict[str, Expr]):
        assert type(ast) is Ast
        assert type(bindings) is frozendict
        self.ast = ast
        self.bindings = bindings
        self.pointer = None # May point to another Expr. In that case, self.ast and self.bindings will be set to None.
        self.substituted_ast = None # A cached result to avoid recomputing it.
        # Assert that all the ast's free variables are bound in the bindings.
        for free_var in ast.free_vars:
            assert free_var in bindings, 'Unbound variable {!r}'.format(free_var)

    def resolve(self) -> Expr:
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

    def apply(self, arg: Expr) -> Expr:
        '''
        Returns a new Expr that is the result of applying the function `self` to the argument `arg`.
        '''
        assert type(arg) is Expr
        self = self.eval()
        assert self.ast.kind == FUNCTION

        new_bindings = self.bindings.set(self.ast.variable_name, arg)

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
            assert len(arg_exprs) == 2
            result = arg_exprs[0].apply(arg_exprs[1])
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

    def to_substituted_ast(self) -> Ast:
        '''
        Returns self.ast with all free variables replaced with their bindings.
        '''
        self = self.resolve()
        if self.substituted_ast is None:
            self.substituted_ast = self.ast.substitute_exprs(self.bindings, frozenset({}))
        return self.substituted_ast

    def to_code(self, parens = False) -> str:
        return self.to_substituted_ast().to_code(parens)


def make_ast_or_expr(type_to_make: type):
    assert type_to_make in (Ast, Expr)
    if type_to_make is Ast:
        def make_ast(lc_code: str):
            return parse(lc_code)
        return make_ast
    if type_to_make is Expr:
        def make_expr(lc_code: str):
            return Expr(parse(lc_code), frozendict({}))
        return make_expr

def as_bool(lc_value: Ast | Expr) -> bool:
    '''
    Interprets the lc_value as a boolean.
    (As defined here: https://en.wikipedia.org/wiki/Church_encoding#Church_Booleans )
    '''
    make_arg = make_ast_or_expr(type(lc_value))

    true_lc = '/_true_x./y._true_x'
    false_lc = '/_false_x./y.y'

    result_lc = lc_value.apply(make_arg(true_lc)).apply(make_arg(false_lc)).to_code()

    if result_lc == true_lc:
        return True
    elif result_lc == false_lc:
        return False
    else:
        assert False, 'as_bool(): LC value did not behave like a boolean'

def as_optional(lc_value: Ast | Expr) -> (Ast | Expr | NoneType):
    '''
    Interprets the lc_value as an optional value.
    (As defined here: https://en.wikipedia.org/wiki/Church_encoding#Optional_values )
    If the lc_value is nil, returns None.
    '''
    make_arg = make_ast_or_expr(type(lc_value))

    param_name = '__very_special_nil_indicator_value'
    nil_result_lc = '/{}.{}'.format(param_name, param_name)

    result = lc_value.apply(make_arg(nil_result_lc)).apply(make_arg('/x.x'))
    result_ast = result.reduce('lazy_to_lambda') if isinstance(result, Ast) else result.eval().ast

    if result_ast.kind == FUNCTION and result_ast.variable_name == param_name and result.to_code() == nil_result_lc:
        # The lc_value is nil.
        return None
    else:
        # The lc_value is non-nil (some value).
        return result

def as_pair(lc_value: Ast | Expr) -> tuple[Ast | Expr, Ast | Expr]:
    '''
    Interprets the lc_value as a pair.
    (As defined here: https://en.wikipedia.org/wiki/Church_encoding#Church_pairs )
    '''
    make_arg = make_ast_or_expr(type(lc_value))

    true_lc = '/_true_x./y._true_x'
    false_lc = '/_false_x./y.y'

    first  = lc_value.apply(make_arg(true_lc))
    second = lc_value.apply(make_arg(false_lc))

    return (first, second)

def as_list(lc_value: Ast | Expr) -> list[Ast | Expr]:
    '''
    Interprets the lc_value as a singly-linked list.
    (A list is an optional pair, where the first item is the payload and second item is the remainder list.)
    '''
    result_list = []
    remainder_list = lc_value

    while True:
        pair_or_none = as_optional(remainder_list)
        if pair_or_none is None:
            return result_list
        item, remainder_list = as_pair(pair_or_none)
        result_list.append(item)

def as_binary_natural_number(lc_value: Ast | Expr) -> int:
    '''
    Interprets the lc_value as a binary unsigned int (>= 0).
    (A binary unsigned int is a list of booleans (bits) where the head is the LEAST significant bit.)
    '''
    bits = [int(as_bool(item)) for item in as_list(lc_value)]

    return sum(
        bit << i
        for i, bit in enumerate(bits)
    )

def as_type_tagged(lc_value: Ast | Expr) -> tuple[bool, Any]:
    '''
    Interprets the lc_value as a type_tag_and_val_pair if possible.
    Returns (success, interpreted_value) where success is True iff the lc_value and all sub-values are type-tagged.
    '''
    lc_value_ast = lc_value.reduce('lazy_to_lambda') if isinstance(lc_value, Ast) else lc_value.eval().ast

    if not (lc_value_ast.kind == FUNCTION and lc_value_ast.variable_name == '_type_tag_and_val_pair_f'):
        return (False, NOT_TYPE_TAGGED)

    type_tag, value = as_pair(lc_value)
    type_tag = as_binary_natural_number(type_tag)

    if type_tag == TYPE_TAG_BOOL:
        return (True, as_bool(value))
    elif type_tag == TYPE_TAG_BNN:
        return (True, as_binary_natural_number(value))
    elif type_tag == TYPE_TAG_LIST:
        result_success = True
        result_list = []
        for e in as_list(value):
            success, interpreted_e = as_type_tagged(e)
            result_success = result_success and success
            result_list.append(interpreted_e)
        return (result_success, result_list)
    else:
        assert False, 'Unexpected type tag {}'.format(type_tag)


def apply_templates(lc_code: str) -> str:
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

def parse_fully(lc_code: str) -> Ast:
    lc_code = apply_templates(lc_code)
    lc_code = remove_comments(lc_code)
    ast = parse(lc_code)
    return ast

def eval_lc(lc_code: str) -> Expr:
    ast = parse_fully(lc_code)
    expr = Expr(ast, frozendict({}))
    return expr.eval()

NIL_AST = parse_fully(MINIMAL_LIBRARY_PREFIX + 'nil')
CONS_AST = parse_fully(MINIMAL_LIBRARY_PREFIX + 'cons')


def run_code_from_stdin():
    lc_code = sys.stdin.read()
    expr = eval_lc(lc_code)
    print(expr.to_code())
    is_type_tagged, interpreted_value = as_type_tagged(expr)
    print(interpreted_value)


def print_code_from_stdin():
    lc_code = sys.stdin.read()
    lc_code = apply_templates(lc_code)
    lc_code = remove_comments(lc_code)
    print(lc_code)


def run_tests():
    parse_test_cases = [
        '(/x./y.x y z (y z) x) (/p.p) z',
    ]

    print('Parse test cases:')
    for lc_code in parse_test_cases:
        test_does_pass = parse(lc_code).to_code() == lc_code
        print(' ', 'Pass' if test_does_pass else 'FAIL', ' ', lc_code)
        if not test_does_pass:
            print('    ' + lc_code)
            print('    ' + parse(lc_code).to_code())
            sys.exit(1)

    wrap_prefix_lc = '#wrap_with_template ./lambda_codes/library.template.lc\n'
    expr_to_code = lambda expr: expr.to_code()
    expr_to_bool = lambda expr: as_bool(expr)
    expr_to_int  = lambda expr: as_binary_natural_number(expr)

    eval_test_cases = [
        # (input_lc_code, transform_func, expected_output)
        ('(/x./y./z.x x) (/x.x) (/zzz.zzz) ((/x.x x) (/x.x x))', expr_to_code, '/x.x'),
        (wrap_prefix_lc + 'not false', expr_to_bool, True),
        (wrap_prefix_lc + 'not true', expr_to_bool, False),
        (wrap_prefix_lc + 'and false false', expr_to_bool, False),
        (wrap_prefix_lc + 'and true false', expr_to_bool, False),
        (wrap_prefix_lc + 'and false true', expr_to_bool, False),
        (wrap_prefix_lc + 'and true true', expr_to_bool, True),
        (wrap_prefix_lc + 'or false false', expr_to_bool, False),
        (wrap_prefix_lc + 'or true false', expr_to_bool, True),
        (wrap_prefix_lc + 'or false true', expr_to_bool, True),
        (wrap_prefix_lc + 'or true true', expr_to_bool, True),
        (wrap_prefix_lc + 'xor false false', expr_to_bool, False),
        (wrap_prefix_lc + 'xor true false', expr_to_bool, True),
        (wrap_prefix_lc + 'xor false true', expr_to_bool, True),
        (wrap_prefix_lc + 'xor true true', expr_to_bool, False),
        (wrap_prefix_lc + 'bools_are_equal false false', expr_to_bool, True),
        (wrap_prefix_lc + 'bools_are_equal true false', expr_to_bool, False),
        (wrap_prefix_lc + 'bools_are_equal false true', expr_to_bool, False),
        (wrap_prefix_lc + 'bools_are_equal true true', expr_to_bool, True),
        (wrap_prefix_lc + 'cn_to_bn (cn_pred cn_2)', expr_to_int, 1),
        (wrap_prefix_lc + 'cn_to_bn (cn_pred cn_1)', expr_to_int, 0),
        (wrap_prefix_lc + 'cn_to_bn (cn_pred cn_0)', expr_to_int, 0),
        (wrap_prefix_lc + 'cn_to_bn (cn_add cn_3 cn_7)', expr_to_int, 10),
        (wrap_prefix_lc + 'cn_to_bn (cn_add cn_7 cn_3)', expr_to_int, 10),
        (wrap_prefix_lc + 'cn_to_bn (cn_sub cn_3 cn_7)', expr_to_int, 0),
        (wrap_prefix_lc + 'cn_to_bn (cn_sub cn_7 cn_3)', expr_to_int, 4),
        (wrap_prefix_lc + 'cn_to_bn (cn_mult cn_3 cn_7)', expr_to_int, 21),
        (wrap_prefix_lc + 'cn_to_bn (cn_mult cn_7 cn_3)', expr_to_int, 21),
        (wrap_prefix_lc + 'cn_to_bn (cn_exp cn_3 cn_2)', expr_to_int, 9),
        (wrap_prefix_lc + 'cn_to_bn (cn_exp cn_2 cn_3)', expr_to_int, 8),
        (wrap_prefix_lc + 'cn_to_bn (cn_exp cn_1 cn_3)', expr_to_int, 1),
        (wrap_prefix_lc + 'cn_to_bn (cn_exp cn_3 cn_1)', expr_to_int, 3),
        (wrap_prefix_lc + 'cn_to_bn (cn_exp cn_3 cn_0)', expr_to_int, 1),
        (wrap_prefix_lc + 'cn_5 not false # Return true if odd', expr_to_bool, True),
        (wrap_prefix_lc + '(cn_factorial cn_5) not false # Return false if even', expr_to_bool, False),
        (wrap_prefix_lc + 'cn_to_bn (cn_factorial cn_5)', expr_to_int, 120),
        (                 '0', expr_to_int, 0),
        (                 '(27)', expr_to_int, 27),
        (wrap_prefix_lc + 'incr 0', expr_to_int, 1),
        (wrap_prefix_lc + 'incr 1', expr_to_int, 2),
        (wrap_prefix_lc + 'incr 2', expr_to_int, 3),
        (wrap_prefix_lc + 'incr 3', expr_to_int, 4),
        (wrap_prefix_lc + 'incr [false]', expr_to_int, 1),
        (wrap_prefix_lc + 'incr [false false]', expr_to_int, 1),
        (wrap_prefix_lc + 'incr (incr 168)', expr_to_int, 170),
        (wrap_prefix_lc + 'incr (incr (incr (incr (incr bn_0))))', expr_to_int, 5),
        (wrap_prefix_lc + 'head_of 0 true', expr_to_bool, True),
        (wrap_prefix_lc + 'head_of 0 false', expr_to_bool, False),
        (wrap_prefix_lc + 'head_of 4 true', expr_to_bool, False),
        (wrap_prefix_lc + 'head_of 4 false', expr_to_bool, False),
        (wrap_prefix_lc + 'head_of 3 true', expr_to_bool, True),
        (wrap_prefix_lc + 'head_of 3 false', expr_to_bool, True),
        (wrap_prefix_lc + 'tail_of 8', expr_to_int, 4),
        (wrap_prefix_lc + 'tail_of (tail_of 8)', expr_to_int, 2),
        (wrap_prefix_lc + 'tail_of (tail_of (tail_of 8))', expr_to_int, 1),
        (wrap_prefix_lc + 'tail_of (tail_of (tail_of (tail_of 8)))', expr_to_int, 0),
        (wrap_prefix_lc + 'tail_of (tail_of (tail_of (tail_of (tail_of 8))))', expr_to_int, 0),
        (wrap_prefix_lc + 'is_nil 0', expr_to_bool, True),
        (wrap_prefix_lc + 'is_nil 8', expr_to_bool, False),
        (wrap_prefix_lc + 'is_nil (bn_cons false nil)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_cons false nil', expr_to_int, 0),
        (wrap_prefix_lc + 'bn_cons true nil', expr_to_int, 1),
        (wrap_prefix_lc + 'bn_cons false 8', expr_to_int, 16),
        (wrap_prefix_lc + 'bn_cons true 8', expr_to_int, 17),
        (wrap_prefix_lc + 'bn_is_normalized 0', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized 1', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized 2', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized 3', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized 4', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized [true]', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized [false]', expr_to_bool, False),
        (wrap_prefix_lc + 'bn_is_normalized [true  true]', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized [false true]', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized [true  false]', expr_to_bool, False),
        (wrap_prefix_lc + 'bn_is_normalized [false false]', expr_to_bool, False),
        (wrap_prefix_lc + 'bn_is_normalized (bn_cons false nil)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (bn_normalize [false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (bn_normalize [true  false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (bn_normalize [false false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (bn_normalize [true  false false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (bn_normalize [false true  false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (bn_normalize [true  true  false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_normalize [false]', expr_to_int, 0),
        (wrap_prefix_lc + 'bn_normalize [true  false]', expr_to_int, 1),
        (wrap_prefix_lc + 'bn_normalize [false false]', expr_to_int, 0),
        (wrap_prefix_lc + 'bn_normalize [true  false false]', expr_to_int, 1),
        (wrap_prefix_lc + 'bn_normalize [false true  false]', expr_to_int, 2),
        (wrap_prefix_lc + 'bn_normalize [true  true  false]', expr_to_int, 3),
        (wrap_prefix_lc + 'decr 0', expr_to_int, 0),
        (wrap_prefix_lc + 'decr 1', expr_to_int, 0),
        (wrap_prefix_lc + 'decr 2', expr_to_int, 1),
        (wrap_prefix_lc + 'decr 3', expr_to_int, 2),
        (wrap_prefix_lc + 'decr 4', expr_to_int, 3),
        (wrap_prefix_lc + 'decr (bn_unnormalize 0)', expr_to_int, 0),
        (wrap_prefix_lc + 'decr (bn_unnormalize 1)', expr_to_int, 0),
        (wrap_prefix_lc + 'decr (bn_unnormalize 2)', expr_to_int, 1),
        (wrap_prefix_lc + 'decr (bn_unnormalize 3)', expr_to_int, 2),
        (wrap_prefix_lc + 'decr (bn_unnormalize 4)', expr_to_int, 3),
        (wrap_prefix_lc + 'decr_normalized (bn_unnormalize 0)', expr_to_int, 7),
        (wrap_prefix_lc + 'decr_normalized (bn_unnormalize 1)', expr_to_int, 0),
        (wrap_prefix_lc + 'decr_normalized (bn_unnormalize 2)', expr_to_int, 1),
        (wrap_prefix_lc + 'decr_normalized (bn_unnormalize 3)', expr_to_int, 2),
        (wrap_prefix_lc + 'decr_normalized (bn_unnormalize 4)', expr_to_int, 3),
        (wrap_prefix_lc + 'bn_is_normalized (decr 0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (decr 1)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (decr 2)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (decr 3)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (decr 4)', expr_to_bool, True),
        (wrap_prefix_lc + 'is_zero nil', expr_to_bool, True),
        (wrap_prefix_lc + 'is_zero 0', expr_to_bool, True),
        (wrap_prefix_lc + 'is_zero 1', expr_to_bool, False),
        (wrap_prefix_lc + 'is_zero 2', expr_to_bool, False),
        (wrap_prefix_lc + 'is_zero 3', expr_to_bool, False),
        (wrap_prefix_lc + 'is_zero [false true]', expr_to_bool, False),
        (wrap_prefix_lc + 'is_zero [true  false]', expr_to_bool, False),
        (wrap_prefix_lc + 'is_zero [false false]', expr_to_bool, True),
        (wrap_prefix_lc + 'add 3 7', expr_to_int, 10),
        (wrap_prefix_lc + 'add 7 3', expr_to_int, 10),
        (wrap_prefix_lc + 'add 0 4', expr_to_int, 4),
        (wrap_prefix_lc + 'add 4 0', expr_to_int, 4),
        (wrap_prefix_lc + 'add 8 12', expr_to_int, 20),
        (wrap_prefix_lc + 'add 12 8', expr_to_int, 20),
        (wrap_prefix_lc + 'add 389480456237 7924028946985', expr_to_int, 8313509403222),
        (wrap_prefix_lc + 'add 389480956261846756091384378324562937 79240248576384173532487308489469085', expr_to_int, 468721204838230929623871686814032022),
        (wrap_prefix_lc + 'bn_is_normalized (add 3 7)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add 7 3)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add 0 4)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add 4 0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add 8 12)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add 12 8)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add 389480456237 7924028946985)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add [false false] [false false])', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (add [true false false] [false false])', expr_to_bool, False), # Note `add` does not always return a normalized result if the input is not normalized
        (wrap_prefix_lc + 'bn_unnormalize 10', expr_to_int, 10),
        (wrap_prefix_lc + 'bn_is_normalized (bn_unnormalize 10)', expr_to_bool, False),
        (wrap_prefix_lc + 'sub   0   0', expr_to_int, 0),
        (wrap_prefix_lc + 'sub   3   7', expr_to_int, 0),
        (wrap_prefix_lc + 'sub   7   3', expr_to_int, 4),
        (wrap_prefix_lc + 'sub   0   1', expr_to_int, 0),
        (wrap_prefix_lc + 'sub   1   0', expr_to_int, 1),
        (wrap_prefix_lc + 'sub   0   2', expr_to_int, 0),
        (wrap_prefix_lc + 'sub   2   0', expr_to_int, 2),
        (wrap_prefix_lc + 'sub   8  12', expr_to_int, 0),
        (wrap_prefix_lc + 'sub  12   8', expr_to_int, 4),
        (wrap_prefix_lc + 'sub  75  45', expr_to_int, 30),
        (wrap_prefix_lc + 'sub 977 766', expr_to_int, 211),
        (wrap_prefix_lc + 'sub (bn_unnormalize   0) (bn_unnormalize   0)', expr_to_int, 0),
        (wrap_prefix_lc + 'sub (bn_unnormalize   3) (bn_unnormalize   7)', expr_to_int, 0),
        (wrap_prefix_lc + 'sub (bn_unnormalize   7) (bn_unnormalize   3)', expr_to_int, 4),
        (wrap_prefix_lc + 'sub (bn_unnormalize   0) (bn_unnormalize   1)', expr_to_int, 0),
        (wrap_prefix_lc + 'sub (bn_unnormalize   1) (bn_unnormalize   0)', expr_to_int, 1),
        (wrap_prefix_lc + 'sub (bn_unnormalize   0) (bn_unnormalize   2)', expr_to_int, 0),
        (wrap_prefix_lc + 'sub (bn_unnormalize   2) (bn_unnormalize   0)', expr_to_int, 2),
        (wrap_prefix_lc + 'sub (bn_unnormalize   8) (bn_unnormalize  12)', expr_to_int, 0),
        (wrap_prefix_lc + 'sub (bn_unnormalize  12) (bn_unnormalize   8)', expr_to_int, 4),
        (wrap_prefix_lc + 'sub (bn_unnormalize  75) (bn_unnormalize  45)', expr_to_int, 30),
        (wrap_prefix_lc + 'sub (bn_unnormalize 977) (bn_unnormalize 766)', expr_to_int, 211),
        (wrap_prefix_lc + 'sub (               977) (bn_unnormalize 766)', expr_to_int, 211),
        (wrap_prefix_lc + 'sub (bn_unnormalize 977) (               766)', expr_to_int, 211),
        (wrap_prefix_lc + 'bn_is_normalized (sub   0   0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   3   7)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   7   3)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   0   1)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   1   0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   0   2)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   2   0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub   8  12)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub  12   8)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub  75  45)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (sub 977 766)', expr_to_bool, True),
        (wrap_prefix_lc + 'mult   0   0', expr_to_int, 0),
        (wrap_prefix_lc + 'mult   3   7', expr_to_int, 21),
        (wrap_prefix_lc + 'mult   7   3', expr_to_int, 21),
        (wrap_prefix_lc + 'mult   0   1', expr_to_int, 0),
        (wrap_prefix_lc + 'mult   1   0', expr_to_int, 0),
        (wrap_prefix_lc + 'mult   0   2', expr_to_int, 0),
        (wrap_prefix_lc + 'mult   2   0', expr_to_int, 0),
        (wrap_prefix_lc + 'mult   8  12', expr_to_int, 8 * 12),
        (wrap_prefix_lc + 'mult  12   8', expr_to_int, 12 * 8),
        (wrap_prefix_lc + 'mult  75  45', expr_to_int, 75 * 45),
        (wrap_prefix_lc + 'mult 977 766', expr_to_int, 977 * 766),
        (wrap_prefix_lc + 'bn_is_normalized (mult   0   0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   3   7)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   7   3)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   0   1)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   1   0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   0   2)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   2   0)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult   8  12)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult  12   8)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult  75  45)', expr_to_bool, True),
        (wrap_prefix_lc + 'bn_is_normalized (mult 977 766)', expr_to_bool, True),
        (wrap_prefix_lc + 'divide 0 3 true', expr_to_int, 0),
        (wrap_prefix_lc + 'divide 0 3 false', expr_to_int, 0),
        (wrap_prefix_lc + 'divide 7 3 true', expr_to_int, 2),
        (wrap_prefix_lc + 'divide 7 3 false', expr_to_int, 1),
        (wrap_prefix_lc + 'divide 8 3 true', expr_to_int, 2),
        (wrap_prefix_lc + 'divide 8 3 false', expr_to_int, 2),
        (wrap_prefix_lc + 'divide 9 3 true', expr_to_int, 3),
        (wrap_prefix_lc + 'divide 9 3 false', expr_to_int, 0),
        (wrap_prefix_lc + 'divide 123 1 true', expr_to_int, 123),
        (wrap_prefix_lc + 'divide 123 1 false', expr_to_int, 0),
        (wrap_prefix_lc + 'divide 123 4 true', expr_to_int, 30),
        (wrap_prefix_lc + 'divide 123 4 false', expr_to_int, 3),
        (wrap_prefix_lc + 'divide 123 5 true', expr_to_int, 24),
        (wrap_prefix_lc + 'divide 123 5 false', expr_to_int, 3),
        (wrap_prefix_lc + 'divide 1 0 true', expr_to_int, 1),
        (wrap_prefix_lc + 'divide 1 0 false', expr_to_int, 1),
        (wrap_prefix_lc + 'divide 2 0 true', expr_to_int, 3),
        (wrap_prefix_lc + 'divide 2 0 false', expr_to_int, 2),
        (wrap_prefix_lc + 'divide 3 0 true', expr_to_int, 3),
        (wrap_prefix_lc + 'divide 3 0 false', expr_to_int, 3),
        (wrap_prefix_lc + 'factorial 7',  expr_to_int, 2*3*4*5*6*7),
        (wrap_prefix_lc + 'factorial 8',  expr_to_int, 2*3*4*5*6*7*8),
        (wrap_prefix_lc + 'factorial 9',  expr_to_int, 2*3*4*5*6*7*8*9),
        (wrap_prefix_lc + 'factorial 10', expr_to_int, 2*3*4*5*6*7*8*9*10),
        (wrap_prefix_lc + 'factorial 11', expr_to_int, 2*3*4*5*6*7*8*9*10*11),
        (wrap_prefix_lc + 'factorial 12', expr_to_int, 2*3*4*5*6*7*8*9*10*11*12),
        (wrap_prefix_lc + 'factorial 13', expr_to_int, 2*3*4*5*6*7*8*9*10*11*12*13),
        (wrap_prefix_lc + 'factorial 14', expr_to_int, 2*3*4*5*6*7*8*9*10*11*12*13*14),
        (wrap_prefix_lc + 'factorial 15', expr_to_int, 2*3*4*5*6*7*8*9*10*11*12*13*14*15),
        (wrap_prefix_lc + 'item_of (prev_of (next_of (next_of (make_doubly_linked_list [100 101 102] nil)))) 50', expr_to_int, 101),
        (wrap_prefix_lc + 'nth_of (infinite_incr_seq 10) 8 500', expr_to_int, 18),
        (wrap_prefix_lc + 'nth_of [10] 0 500', expr_to_int, 10),
        (wrap_prefix_lc + 'nth_of [10] 1 500', expr_to_int, 500),
        (wrap_prefix_lc + 'nth_of [10] 8 500', expr_to_int, 500),
        (wrap_prefix_lc + 'type_list [(type_bnn 72) (type_bool true) (type_list [(type_bool false)]) (type_list [])]', as_type_tagged, (True, [72, True, [False], []])),
        (wrap_prefix_lc + 'type_list [72 (type_bnn 42)]', as_type_tagged, (False, [NOT_TYPE_TAGGED, 42])),
        (wrap_prefix_lc + 'type_list_of type_bnn [72 42 69 0 120]', as_type_tagged, (True, [72, 42, 69, 0, 120])),
        (wrap_prefix_lc + 'are_equal        (bn_unnormalize  8) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'are_equal        (bn_unnormalize  9) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'are_equal        (bn_unnormalize 10) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'are_not_equal    (bn_unnormalize  8) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'are_not_equal    (bn_unnormalize  9) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'are_not_equal    (bn_unnormalize 10) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'less_than        (bn_unnormalize  8) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'less_than        (bn_unnormalize  9) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'less_than        (bn_unnormalize 10) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'less_or_equal    (bn_unnormalize  8) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'less_or_equal    (bn_unnormalize  9) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'less_or_equal    (bn_unnormalize 10) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'greater_than     (bn_unnormalize  8) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'greater_than     (bn_unnormalize  9) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'greater_than     (bn_unnormalize 10) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'greater_or_equal (bn_unnormalize  8) (bn_unnormalize  9)', expr_to_bool, False),
        (wrap_prefix_lc + 'greater_or_equal (bn_unnormalize  9) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'greater_or_equal (bn_unnormalize 10) (bn_unnormalize  9)', expr_to_bool, True),
        (wrap_prefix_lc + 'type_list_of type_bnn (reverse [100 3 4 5 6 7])', as_type_tagged, (True, [7, 6, 5, 4, 3, 100])),
        (wrap_prefix_lc + 'type_list_of type_bnn (concat [100 3 4] [5 6 7])', as_type_tagged, (True, [100, 3, 4, 5, 6, 7])),
        (wrap_prefix_lc + 'type_list_of type_bnn (map [100 3 4 5 6 7] /x. mult 2 x)', as_type_tagged, (True, [200, 6, 8, 10, 12, 14])),

        # TODO: Add tests of:
        #   - apply_n_times
        #   - bn_to_cn
        #   - flatten
        #   - flat_map
        #   - len
    ]

    # for i in range(20):
    #     for j in range(i+3):
    #         eval_test_cases.append(
    #             (wrap_prefix_lc + 'sub (bn_unnormalize {}) (bn_unnormalize {})'.format(i, j), expr_to_int, max(i - j, 0))
    #         )
    # for i in range(20):
    #     for j in range(i+3):
    #         eval_test_cases.append(
    #             (wrap_prefix_lc + 'bn_is_normalized (sub {} {})'.format(i, j), expr_to_bool, True)
    #         )

    # for i in range(20):
    #     for j in range(20):
    #         eval_test_cases.append(
    #             (wrap_prefix_lc + 'mult (bn_unnormalize {}) (bn_unnormalize {})'.format(i, j), expr_to_int, i * j)
    #         )
    # for i in range(20):
    #     for j in range(20):
    #         eval_test_cases.append(
    #             (wrap_prefix_lc + 'bn_is_normalized (mult {} {})'.format(i, j), expr_to_bool, True)
    #         )

    print('Eval test cases:')
    for (input_lc_code, transform_func, expected_output) in eval_test_cases:
        start_time = time.time()
        actual_output = transform_func(eval_lc(input_lc_code))
        elapsed = time.time() - start_time
        test_does_pass = actual_output == expected_output
        print(' ', 'Pass' if test_does_pass else 'FAIL', ' ',
              input_lc_code.replace(wrap_prefix_lc, '').replace('\n', '\n' + ' '*9),
              ' -> ', expected_output, ' ({} ms)'.format(int(elapsed * 1000)))
        if not test_does_pass:
            print('    expected:', expected_output)
            print('    actual:  ', actual_output)
            sys.exit(1)


if __name__ == '__main__':
    sys.setrecursionlimit(5000)

    if len(sys.argv) == 2 and sys.argv[1] == 'test':
        run_tests()
    elif len(sys.argv) == 2 and sys.argv[1] == 'run':
        run_code_from_stdin()
    elif len(sys.argv) == 2 and sys.argv[1] == 'print':
        print_code_from_stdin()
    else:
        sys.exit('Usage: {} <run|test>'.format(sys.argv[0]))


