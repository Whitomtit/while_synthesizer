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


# def test_gift_2_OLD():
#     assert not verify(lambda d: d['x'] > 0,
#                       parse("y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"),
#                       lambda d: d['x'] > 0, lambda d: d['x'] > 0)


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


def test_feature_1_if() -> None:
    ast = parse(
        """
        if x < ?? then 
            y := ?? 
        else
            y := ??
        """
    )
    assert ast is not None

    in_1 = lambda d: d["x"] == 0
    out_1 = lambda d: d["y"] == 3

    in_2 = lambda d: d["x"] == 1
    out_2 = lambda d: d["y"] == 5

    in_3 = lambda d: d["x"] == -4
    out_3 = lambda d: d["y"] == 3

    ins = [in_1, in_2, in_3]
    outs = [out_1, out_2, out_3]
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    for P, Q in zip(ins, outs):
        assert verify(P, ast, Q, linv)


def test_feature_2_while() -> None:
    ast = parse(
        """
        y := ??;
        assert y < 9;
        i := ??;
        n := ??;
        while i < n do (
            assert y >= 7;
            y := y + ??;
            assert y >= 9;
            i := i + 1
        );
        assert y >= 20
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    for P, Q in zip(ins, outs):
        assert verify(P, ast, Q, linv)


def test_simple_initialization() -> None:
    ast = parse(
        """
        x := ??;
        y := ??;
        assert x = y;
        assert x > 2;
        while x > 0 do (
            x := x - 1;
            assert y >= 0
        );
        assert x = 0;
        assert y = ??
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_incremental_change() -> None:
    ast = parse(
        """
        y := ??;
        x := ??;
        assert (y > 0);
        assert (x > (8 * y));
        while x > y do (
            x := x - 1;
            y := y + 1
        );
        assert x = y

        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_constant_cond_nested_holes() -> None:
    ast = parse(
        """
        x := ??;
        y := 10;
        while x > 0 do (
            y := y + ??;
            x := x - ??
        );
        assert y = 20

        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_bound_increment() -> None:
    ast = parse(
        """
        x := ??;
        y := 0;
        assert(x < 5);
        while x < 5 do (
            x := x + 1;
            y := y + ??
        );
        assert x = 5;
        assert y = (5 * ??)

        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_exact_matching() -> None:
    ast = parse(
        """
        y := ??;
        x := y;
        assert x > 5;
        while x > 0 do (
            x := x - 1;
            y := y - 1
        );
        assert x = 0;
        assert y = 0
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_summation_pattern() -> None:
    ast = parse(
        """
        y := 0;
        x := ??;
        z := ??;
        assert z > 3;
        assert x > 2;
        while x > 0 do (
            y := y + z;
            x := x - 1
        );
        assert y = (?? * z)
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_cond_and_alt_assign() -> None:
    ast = parse(
        """
        x := ??;
        if x < 5 then 
            y := 10 
        else
            y := 20;
        assert y > 10
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_loop_nested_assertions() -> None:
    ast = parse(
        """
        y := ??;
        x := 5;
        while x > 0 do (
            assert y > 0;
            y := y + ??;
            x := x - 1
        );
        assert y = (?? * 5)
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_zeroing_out() -> None:
    ast = parse(
        """
        x := ??;
        y := x;
        assert x > 2;
        while x > 0 do (
            x := x - 1;
            y := y - ??
        );
        assert y = 0

        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_complex() -> None:
    ast = parse(
        """
        x := ??;
        y := ??;
        z := ??;
        assert x > y;
        if x > 5 then 
            z := z + ?? 
        else
            z := z - ??;
        while x > y do (
            x := x - ??;
            assert x > y;
            if z < 0 then
                y := y + ??
            else
                y := y - ??;
            assert y >= 0
        );
        assert (x = y) or (x = (y - 1))
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_complex_2() -> None:
    ast = parse(
        """
        a := ??;
        b := ??;
        c := ??;
        d := ??;
        assert a > b;
        if c > ?? then
            d := d + ??
        else
            d := d - ??;
        while (a > b) and (d < ??) do (
            a := a - 1;
            b := b + ??;
            c := c - ??;
            assert c >= 0;
            if (b mod 2) = 0 then
                d := d + 1
            else
                d := d - 1
        );
        assert (a = b) or (c = 0);
        assert d < 10
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_no_unfold() -> None:
    ast = parse(
        """
        x := ??;
        while not (x = 0) do (
            assert (x > 0);
            x := x + 1
        );
        assert false
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_sort_swap() -> None:
    ast = parse(
        """
        a[0] := 7;
        a[1] := 5;
        a[2] := 13;
        a[3] := 17;
        
        a[??] := a[1];
        a[??] := a[0];
        a[0] := a[??];
        
        assert (a[0] < a[1]);
        assert (a[1] < a[2]);
        assert (a[2] < a[3])
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    assert verify(lambda _: True, ast, lambda _: True, linv)


def test_hard_sort_swap() -> None:
    ast = parse(
        """
        a[0] := 7;
        a[1] := 5;
        a[2] := 13;
        a[3] := 17;
        
        a[??] := a[??];
        a[??] := a[??];
        a[??] := a[??];
        
        assert (a[0] < a[1]);
        assert (a[1] < a[2]);
        assert (a[2] < a[3])
        """
    )
    assert ast is not None

    ins = []
    outs = []
    linv = lambda d: True

    model = synthesize(ast, linv, ins, outs)
    assert model is None


def test_array_init() -> None:
    ast = parse(
        """
        arr[0] := ??;
        arr[1] := ??;
        arr[3] := arr[0] + (arr[1] + arr[2]);
        assert (arr[0] > 0);
        assert (arr[1] > 0)
        """
    )
    assert ast is not None

    ins = ["arr[2] > 5", "arr[2] = 4", "true"]
    outs = ["arr[3] > 10", "arr[3] = 9", "arr[0] > 2"]
    linv = lambda d: True

    ins = [parse_PBE(i) for i in ins]
    outs = [parse_PBE(o) for o in outs]

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    for P, Q in zip(ins, outs):
        assert verify(P, ast, Q, linv)


def test_array_loop_manipulation() -> None:
    ast = parse(
        """
        arr[1] := arr[0] + ??;
        arr[2] := arr[1] - ??;
        while (arr[0] > 0) do (
            assert (arr[0] > 0);
            arr[0] := arr[0] - 1;
            arr[2] := arr[2] + 1
        );
        assert (arr[2] = arr[1])
        """
    )
    assert ast is not None

    ins = ["arr[0] = 4"]
    outs = ["arr[2] = 7"]
    linv = lambda d: True

    ins = [parse_PBE(i) for i in ins]
    outs = [parse_PBE(o) for o in outs]

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    for P, Q in zip(ins, outs):
        assert verify(P, ast, Q, linv)


def test_array_access() -> None:
    ast = parse(
        """
        arr[index] := 5;
        arr[index + 1] := arr[index] + ??
        """
    )
    assert ast is not None

    ins = ["index >= 0", "index = 1"]
    outs = ["arr[index + 1] >= 8", "arr[2] = 10"]
    linv = lambda d: True

    ins = [parse_PBE(i) for i in ins]
    outs = [parse_PBE(o) for o in outs]

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    for P, Q in zip(ins, outs):
        assert verify(P, ast, Q, linv)


def test_binary_search() -> None:
    ast = parse(
        """
        arr[0] := 1;
        arr[1] := 3;
        arr[2] := 7;
        arr[3] := 8;
        arr[4] := 10;
        arr[5] := 12;
        arr[6] := 15;
        arr[7] := 17;
        arr[8] := 20;
        arr[9] := 25;
        arr[10] := 30;
        arr[11] := 35;
        arr[12] := 40;
        arr[13] := 45;
        arr[14] := 50;

        n := 15;

        low := 0;
        high := n - 1;
        index := ??;

        while low <= high do (
            mid := (low + high) / 2;
            if arr[mid] = target then (
                index := mid;
                low := high + ??
            )
            else if arr[mid] < target then (
                low := mid + ??
            )
            else (
                high := mid - ??
            )
        )
        """
    )
    assert ast is not None

    ins = ["target = 1", "target = 2", "target = 40", "target = 25"]
    outs = ["index = 0", "index = -1", "index = 12", "index = 9"]
    linv = lambda d: True

    ins = [parse_PBE(i) for i in ins]
    outs = [parse_PBE(o) for o in outs]

    model = synthesize(ast, linv, ins, outs)
    assert model is not None

    full_program = pretty_repr(ast, model)
    ast = parse(full_program)

    for P, Q in zip(ins, outs):
        assert verify(P, ast, Q, linv)
