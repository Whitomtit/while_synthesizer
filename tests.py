from wp import *


def test_skip():
    assert verify(lambda _: True, parse('skip'),
                  lambda _: True, lambda _: False)


def test_set_1():
    assert verify(lambda _: True, parse('a := b'),
                  lambda d: d['a'] == d['b'], lambda _: False)


def test_set_2():
    assert verify(lambda d: d['c'] != d['b'], parse('a := b ; a := c'),
                  lambda d: And(d['a'] != d['b'], d['a'] == d['c']), lambda _: False)


def test_set_3():
    assert verify(lambda _: True, parse('a := b ; c := a'),
                  lambda d: And(d['a'] == d['b'], d['a'] == d['c']), lambda _: False)


def test_bad_set():
    assert not verify(lambda d: d['c'] != d['b'], parse('a := b ; a := c'),
                      lambda d: And(d['a'] == d['b'], d['a'] == d['c']), lambda _: False)


def test_ite_1():
    assert verify(lambda d: d['a'] == d['b'], parse('if a = b then c := a else d := a'),
                  lambda d: And(d['a'] == d['b'], d['a'] == d['c']), lambda _: False)


def test_ite_2():
    assert verify(lambda d: d['a'] != d['b'], parse('if a = b then c := a else d := a'),
                  lambda d: And(d['a'] != d['b'], d['a'] == d['d']), lambda _: False)


def test_bad_ite_1():
    assert not verify(lambda d: d['a'] == d['b'], parse('if a = b then a := c else a := d'),
                      lambda d: And(d['a'] == d['b'], d['a'] == d['c']), lambda _: False)


def test_bad_ite_2():
    assert not verify(lambda d: d['a'] != d['b'], parse('if a = b then a := c else a := d'),
                      lambda d: And(d['a'] == d['b'], d['a'] == d['d']), lambda _: False)


def test_gift_1():
    assert verify(lambda _: True, parse("a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"),
                  lambda d: And(d['a'] == d['b'], d['i'] >= d['n']), lambda d: d['a'] == d['b'])


def test_gift_2():
    assert verify(lambda d: d['x'] > 0,
                  parse("y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"),
                  lambda d: d['x'] > 0, lambda d: And(d['x'] > 0, d['y'] >= 0))


def test_gift_3():
    assert verify(lambda d: And(d['a'] > 0, d['b'] > 0),
                  parse("while a != b do if a > b then a := a - b else b := b - a"),
                  lambda d: And(d['a'] > 0, d['a'] == d['b']), lambda d: d['a'] > 0)


def test_gift_1_OLD():
    assert verify(lambda _: True, parse("a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"),
                  lambda d: d['a'] == d['b'], lambda d: d['a'] == d['b'])


def test_gift_2_OLD():
    assert not verify(lambda d: d['x'] > 0,
                      parse("y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"),
                      lambda d: d['x'] > 0, lambda d: d['x'] > 0)


def test_gift_3_OLD():
    assert verify(lambda d: And(d['a'] > 0, d['b'] > 0),
                  parse("while a != b do if a > b then a := a - b else b := b - a"),
                  lambda d: And(d['a'] > 0, d['a'] == d['b']), lambda d: And(d['a'] > 0, d['b'] > 0))


def test_non_stopping() -> None:
    ast = parse(
        """
        i := 0;
        while i = 0 do (
            skip
        )
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['i'] == 0,
        )

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return False

    assert verify(P, ast, Q, linv)


def test_non_stopping_2() -> None:
    ast = parse(
        """
        while i = 0 do (
            skip
        )
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['i'] == 0,
        )

    def P(env: Env) -> Formula:
        return env['i'] == 0

    def Q(env: Env) -> Formula:
        return False

    assert verify(P, ast, Q, linv)


def test_stopping() -> None:
    ast = parse(
        """
        i := 0;
        while i != 0 do (
            skip
        )
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['i'] == 0,
        )

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return False

    assert not verify(P, ast, Q, linv)


def test_stopping_2() -> None:
    ast = parse(
        """
        while i = 0 do (
            skip
        )
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['i'] != 0,
        )

    def P(env: Env) -> Formula:
        return env['i'] != 0

    def Q(env: Env) -> Formula:
        return False

    assert not verify(P, ast, Q, linv)


def test_div_special_case() -> None:
    ast = parse(
        """
        i := 0;
        while (b * i) <= a do (
            i := i + 1
        );
        i := i - 1
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['a'] == 100,
            env['b'] == 5,
            env['b'] * (env['i'] - 1) <= env['a'],

        )

    def P(env: Env) -> Formula:
        return And(
            env['b'] == 5,
            env['a'] == 100
        )

    def Q(env: Env) -> Formula:
        return env['i'] == 20

    assert verify(P, ast, Q, linv)


def test_div_special_case_2() -> None:
    ast = parse(
        """
        i := 0;
        while (b * i) <= a do (
            i := i + 1
        );
        i := i - 1
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['a'] == 100,
            env['b'] == 5,
            env['b'] * (env['i'] - 1) <= env['a'],

        )

    def P(env: Env) -> Formula:
        return And(
            env['b'] == 5,
            env['a'] == 100
        )

    def Q(env: Env) -> Formula:
        return env['i'] == 21

    assert not verify(P, ast, Q, linv)


def test_div() -> None:
    ast = parse(
        """
        i := 0;
        while (b * i) <= a do (
            i := i + 1
        );
        i := i - 1
    """)
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(
            env['b'] * (env['i'] - 1) <= env['a'],
        )

    def P(env: Env) -> Formula:
        return And(env['a'] > 0, env['b'] > 0)

    def Q(env: Env) -> Formula:
        return And(
            env['b'] * env['i'] <= env['a'],
            env['b'] * (env['i'] + 1) > env['a'],
        )

    assert verify(P, ast, Q, linv)


def test_if() -> None:
    ast = parse(
        """
        a := 1;
        (
            if a = 1 then
                a := 2
            else
                skip
        );
        (
            if a = 2 then
                (
                    a := 3;
                    (
                        if a = 4 then
                            a := 5
                        else
                             skip
                    )
                )                        
            else
                skip
        )
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return True

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env['a'] == 3

    assert verify(P, ast, Q, linv)


def test_if_2() -> None:
    ast = parse(
        """
        a := 1;
        (
            if a = 1 then
                a := 2
            else
                skip
        );
        (
            if a = 2 then
                (
                    a := 3;
                    (
                        if a = 4 then
                            a := 5
                        else
                             skip
                    )
                )                        
            else
                skip
        )
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return True

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env['a'] == 1

    assert not verify(P, ast, Q, linv)
