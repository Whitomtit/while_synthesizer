import operator
import typing
from typing import Union

from z3 import Int, IntVal, Implies, Not, And, Or, Solver, unsat, sat, Ast, ForAll, Array, IntSort, Store, \
    Select, is_array, ModelRef

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
    "mod": operator.mod,
    "and": And,
    "or": Or,
}


def get_unique_id(env: Env, var: str) -> str:
    """
    Get a unique identifier for a variable.
    """
    i = 0
    while f"{var}_{i}" in env:
        i += 1
    return f"{var}_{i}"


def mk_env(pvars: set[PVar], parrays: set[PVar]) -> Env:
    """
    Create an environment with the given program variables.
    """
    return {v: Int(v) for v in pvars} | {v: Array(v, IntSort(), IntSort()) for v in parrays}


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


def get_array_ids(ast: Tree) -> set[str]:
    """
    Get all array identifiers from an AST.
    """
    return {get_id(ast.subtrees[0]) for ast in ast.nodes if ast.root == "array"}


def get_non_array_ids(ast: Tree) -> set[str]:
    """
    Get all non-array identifiers from an AST.
    """
    return get_all_ids(ast) - get_array_ids(ast)


def eval_expr(ast: Tree, env: Env) -> Formula:
    """
    Evaluate an expression AST node.
    """
    match ast.root, ast.subtrees:
        case "id", _:
            return env[get_id(ast)]
        case "num", [num_tree]:
            return IntVal(num_tree.root)
        case "array", [id, idx]:
            return Select(env[get_id(id)], eval_expr(idx, env))
        case "hole", _:
            return ast.var
        case "not", [cond]:
            return Not(eval_expr(cond, env))
        case "false", _:
            return False
        case "true", _:
            return True
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
            if x.root == "array":
                def new_Q(env: Env) -> Formula:
                    id = get_id(x.subtrees[0])
                    idx = eval_expr(x.subtrees[1], env)
                    return Q(upd(env, id, Store(env[id], idx, eval_expr(e, env))))

                return new_Q

            def new_Q(env: Env) -> Formula:
                # TODO: Maybe exception?
                if is_array(env[get_id(x)]):
                    assert is_array(env[get_id(e)])
                return Q(upd(env, get_id(x), eval_expr(e, env)))

            return new_Q
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

                body_vars = {id: Int(get_unique_id(env, id)) for id in get_non_array_ids(body)}
                body_vars = body_vars | {id: Array(get_unique_id(env, id), IntSort(), IntSort()) for id in
                                         get_array_ids(body)}
                sub_env = env | body_vars

                body_wpi = wp(body, inv)

                body_wp = body_wpi(sub_env)
                double_wp = wp(body, body_wpi)(sub_env)

                P_init = inv(env)
                b_init = eval_expr(cond, env)

                start_P = inv(sub_env)
                start_B = eval_expr(cond, sub_env)

                after_one_P = wp(body, inv)(sub_env)
                after_one_B = wp(body, lambda exp_env: eval_expr(cond, exp_env))(sub_env)

                bounded_vars = list(body_vars.values())
                return Or(
                    And(
                        P_init,
                        Not(b_init),
                        Q(env)
                    ),
                    And(
                        P_init,
                        b_init,
                        body_wpi(env),
                        ForAll(
                            bounded_vars,
                            And(
                                Implies(
                                    And(start_P, start_B, body_wp),
                                    And(
                                        after_one_P,
                                        Or(
                                            double_wp,
                                            Not(after_one_B)
                                        )
                                    )
                                ),
                                Implies(
                                    And(after_one_P, Not(after_one_B), body_wp),
                                    wp(body, Q)(sub_env)
                                )
                            )
                        ) if bounded_vars else True
                    )
                )

            return new_Q
        case "assert", [cond]:
            return lambda env: And(eval_expr(cond, env), Q(env))
        case _:
            assert False, f"Unknown command AST node: {ast}"


def inner_synthesize(ast: Tree, linv: Invariant, inputs: list[Invariant], outputs: list[Invariant]) -> ModelRef | None:
    assert len(inputs) == len(outputs)
    if not inputs:
        inputs = [lambda _: True]
        outputs = [lambda _: True]

    env = mk_env(get_non_array_ids(ast), get_array_ids(ast))
    free_vars = list(env.values())

    env[INVARIANT_KEY] = linv

    sub_formula = True
    for input, output in zip(inputs, outputs):
        wp_out = wp(ast, output)
        sub_formula = And(sub_formula, Implies(input(env), wp_out(env)))

    s = Solver()

    s.add(
        ForAll(
            free_vars,
            sub_formula
        )
    )
    if s.check() == sat:
        return s.model()
    else:
        return None


def unfold_while(ast: Tree, iterations: int) -> Tree:
    """
    Unfold a while loop for a given number of iterations.
    """
    if ast.root == "while":
        [cond, body] = ast.subtrees
        if iterations == 0:
            return Tree("assert", [Tree("not", [cond])])
        else:
            return Tree(";", [Tree("assert", [cond]), Tree(";", [body, unfold_while(ast, iterations - 1)])])
    elif ast.root == "hole":
        return ast
    return Tree(ast.root, [unfold_while(subtree, iterations) for subtree in ast.subtrees])


def synthesize(ast: Tree, linv: Invariant, inputs: list[Invariant], outputs: list[Invariant]) -> ModelRef | None:
    """
    Synthesize a model for a program AST node.
    """
    holes = [ast for ast in ast.nodes if ast.root == "hole"]
    for idx, hole in enumerate(holes):
        hole.var = Int(f'__hole_{idx}')

    model = inner_synthesize(ast, linv, inputs, outputs)
    if model is not None:
        print(">> Synthesized with no unfolding.")
        return model

    for i in range(1, 10):
        unfolded_ast = unfold_while(ast, i)
        model = inner_synthesize(unfolded_ast, linv, inputs, outputs)
        if model is not None:
            print(f">> Synthesized with {i} unfoldings.")
            return model

    return None


def inner_verify(P: Invariant, ast: Tree, Q: Invariant, linv: Invariant) -> bool:
    env = mk_env(get_non_array_ids(ast), get_array_ids(ast))
    env[INVARIANT_KEY] = linv
    wp_inv = wp(ast, Q)

    s = Solver()
    s.add(Not(Implies(P(env), wp_inv(env))))
    if s.check() == unsat:
        return True
    else:
        return False


def verify(P: Invariant, ast: Tree, Q: Invariant, linv: Invariant) -> bool:
    """Verify a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """

    if inner_verify(P, ast, Q, linv):
        return True

    for i in range(1, 10):
        unfolded_ast = unfold_while(ast, i)
        if inner_verify(P, unfolded_ast, Q, linv):
            return True

    return False


def pretty_repr(ast: Tree, model: ModelRef, depth=0) -> str:
    indent = "    " * depth
    match ast.root, ast.subtrees:
        case "skip", _:
            return indent + "skip"
        case ":=", [x, e]:
            return pretty_repr(x, model, depth) + " := " + pretty_repr(e, model)
        case ";", [c1, c2]:
            return (f"{pretty_repr(c1, model, depth)};\n"
                    f"{pretty_repr(c2, model, depth)}")
        case "if", [cond, then_branch, else_branch]:
            return (f"{indent}if {pretty_repr(cond, model)} then (\n"
                    f"{pretty_repr(then_branch, model, depth + 1)}\n"
                    f"{indent}) else (\n"
                    f"{pretty_repr(else_branch, model, depth + 1)})")
        case "while", [cond, body]:
            return (f"{indent}while {pretty_repr(cond, model)} do (\n"
                    f"{pretty_repr(body, model, depth + 1)}\n"
                    f"{indent})")
        case "id", [id_tree]:
            return indent + id_tree.root
        case "num", [num_tree]:
            return indent + str(num_tree.root)
        case "hole", _:
            return indent + str(0 if model[ast.var] is None else model[ast.var]) if model is not None else "??"
        case "assert", [cond]:
            return f"{indent}assert {pretty_repr(cond, model)}"
        case "not", [cond]:
            return f"{indent}not ({pretty_repr(cond, model)})"
        case "array", [id, idx]:
            return f"{indent}{pretty_repr(id, model)}[{pretty_repr(idx, model)}]"
        case "false", _:
            return indent + "false"
        case "true", _:
            return indent + "true"
        case op, [l, r]:
            return f"({pretty_repr(l, model)} {op} {pretty_repr(r, model)})"
        case _:
            assert False, f"Unknown command AST node: {ast}"


def main():
    program = """
        a[??] := ??;
        x := ??;
        assert x > 0;
        b := a[x + 5]
        """
    P = lambda d: True
    Q = lambda d: d["b"] == 6
    linv = lambda d: True

    ast = parse(program)

    if ast is not None:
        print(">> Valid program.")
        model = synthesize(ast, linv, [P], [Q])
        if model is None:
            print(">> Could not find a model.")
        else:
            print(">> Found a model.")
            full_program = pretty_repr(ast, model)
            print(full_program)
            ast = parse(full_program)
            for P, Q in zip([P], [Q]):
                assert verify(P, ast, Q, linv)
    else:
        print(">> Invalid program.")


if __name__ == "__main__":
    main()
