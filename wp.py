import operator
import typing
from typing import Union

from z3 import Int, IntVal, Implies, Not, And, Or, Solver, unsat, Ast

from syntax.tree import Tree
from syntax.while_lang import parse

Formula: typing.TypeAlias = Ast | bool
PVar: typing.TypeAlias = str
Env: typing.TypeAlias = dict[PVar, Union[Formula, 'Invariant']]
Invariant: typing.TypeAlias = typing.Callable[[Env], Formula]

INVARIANT_KEY = "linv"

OP = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": operator.floordiv,
    "!=": operator.ne,
    ">": operator.gt,
    "<": operator.lt,
    "<=": operator.le,
    ">=": operator.ge,
    "=": operator.eq,
}


def get_unique_id(env: Env, var: str) -> str:
    """
    Get a unique identifier for a variable.
    """
    i = 0
    while f"{var}_{i}" in env:
        i += 1
    return f"{var}_{i}"


def mk_env(pvars: set[PVar]) -> Env:
    """
    Create an environment with the given program variables.
    """
    return {v: Int(v) for v in pvars}


def upd(d: Env, k: PVar, v: Formula) -> Env:
    """
    Update the value of a key in the environment.
    """
    d = d.copy()
    d[k] = v
    return d


def get_id(ast: Tree) -> str:
    """
    Get the identifier from an AST node.
    """
    assert ast.root == "id"
    return ast.subtrees[0].root


def get_all_ids(ast: Tree) -> set[str]:
    """
    Get all identifiers from an AST.
    """
    return {get_id(ast) for ast in ast.nodes if ast.root == "id"}


def eval_expr(ast: Tree, env: Env) -> Formula:
    """
    Evaluate an expression AST node.
    """
    match ast.root, ast.subtrees:
        case "id", _:
            return env[get_id(ast)]
        case "num", [num_tree]:
            return IntVal(num_tree.root)
        case op, [l, r]:
            return OP[op](eval_expr(l, env), eval_expr(r, env))
        case _:
            assert False, f"Unknown expression AST node: {ast}"


def wp(ast: Tree, Q: Invariant) -> Invariant:
    """
    Compute the weakest precondition of a command AST node.
    """
    match ast.root, ast.subtrees:
        case "skip", _:
            return Q
        case ":=", [x, e]:
            return lambda env: Q(upd(env, get_id(x), eval_expr(e, env)))
        case ";", [c1, c2]:
            return wp(c1, wp(c2, Q))
        case "if", [cond, then_branch, else_branch]:
            def new_Q(env: Env) -> Formula:
                b = eval_expr(cond, env)
                Q_then = wp(then_branch, Q)
                Q_else = wp(else_branch, Q)
                return Or(And(b, Q_then(env)), And(Not(b), Q_else(env)))

            return new_Q
        case "while", [cond, body]:
            def new_Q(env: Env) -> Formula:
                inv = env[INVARIANT_KEY]

                body_vars = {id: Int(get_unique_id(env, id)) for id in get_all_ids(body)}
                sub_env = env | body_vars

                body_wp = wp(body, inv)(sub_env)
                P_init = inv(env)
                P = inv(sub_env)
                B = eval_expr(cond, sub_env)

                return And(
                    P_init,
                    And(
                        Implies(
                            And(P, B),
                            body_wp),
                        Implies(
                            And(P, Not(B)),
                            Q(sub_env)))
                )

            return new_Q
        case _:
            assert False, f"Unknown command AST node: {ast}"


def verify(P: Invariant, ast: Tree, Q: Invariant, linv: Invariant) -> bool:
    """Verify a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """

    env = mk_env(get_all_ids(ast))
    env[INVARIANT_KEY] = linv
    wp_inv = wp(ast, Q)

    s = Solver()
    s.add(Not(Implies(P(env), wp_inv(env))))
    if s.check() == unsat:
        return True
    else:
        print(s.model())
        return False


def main():
    # example program
    # pvars = ["a", "b", "i", "n"]
    # program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"
    # P = lambda _: True
    # Q = lambda d: d["a"] == d["b"]
    # linv = lambda d: d["a"] == d["b"]

    #
    # Following are other programs that you might want to try
    #

    ## Program 1
    # pvars = ['x', 'i', 'y']
    # program = "y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"
    # P = lambda d: d['x'] > 0
    # Q = lambda d: d['x'] > 0
    # linv = lambda d: d['x'] > 0

    ## Program 2
    program = "while a != b do if a > b then a := a - b else b := b - a"
    P = lambda d: And(d['a'] > 0, d['b'] > 0)
    Q = lambda d: And(d['a'] > 0, d['a'] == d['b'])
    linv = lambda d: And(d['a'] > 0, d['b'] > 0)

    ast = parse(program)

    if ast is not None:
        print(">> Valid program.")
        # Your task is to implement "verify"
        verify(P, ast, Q, linv=linv)
    else:
        print(">> Invalid program.")


if __name__ == "__main__":
    main()
