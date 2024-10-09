from syntax.while_lang import parse
from wp import eval_expr, synthesize, verify, pretty_repr, get_all_ids

def parse_expr(expr_text: str):
    expr_ast = parse(f'assert ({expr_text})')
    if expr_ast is None:
        return None
    return expr_ast.subtrees[0]

def main():
    program_ast = None
    print ("Enter a program (enter dot to finish): ")
    while program_ast is None:
        program_text = ""
        while not program_text.endswith("."):
            program_text += input()
        program_text = program_text[:-1]
        program_ast = parse(program_text)
        if program_ast is None:
            print("Invalid program. Try again")
    
    print("Program parsed successfully")
    print("Do you want to provide PBEs for the program? (y/n)")

    inputs = []
    outputs = []

    answer = input()
    while answer == "y" or answer == "Y":
        print("Enter input example: ")
        input_ast = None
        while input_ast is None:
            input_example = input()
            input_ast = parse_expr(input_example)
            if input_ast is None:
                print("Invalid input. Try again")
            if not get_all_ids(input_ast).issubset(get_all_ids(program_ast)):
                print("Invalid input. Input may contain only variables from the program. Try again.")
                input_ast = None

        print("Enter output example: ")
        output_ast = None
        while output_ast is None:
            output_example = input()
            output_ast = parse_expr(output_example)
            if output_ast is None:
                print("Invalid output. Try again")
            if not get_all_ids(output_ast).issubset(get_all_ids(program_ast)):
                print("Invalid output. Output may contain only variables from the program. Try again.")
                output_ast = None
        
        inputs.append(input_ast)
        outputs.append(output_ast)

        print("Do you want to provide more examples? (y/n)")
        answer = input()

    linv_ast = None
    print("Enter loop invariant (leave empty to omit): ")
    while linv_ast is None:
        linv_text = input()
        if linv_text == "":
            break
        linv_ast = parse_expr(linv_text)
        if linv_ast is None:
            print("Invalid loop invariant. Try again")

    linv = lambda env: eval_expr(linv_ast, env) if linv_ast is not None else True
    inputs = [lambda env: eval_expr(input_ast, env) for input_ast in inputs]
    outputs = [lambda env: eval_expr(output_ast, env) for output_ast in outputs]

    if not inputs:
        inputs = [lambda env: True]
        outputs = [lambda env: True]

    model = synthesize(program_ast, linv, inputs, outputs)
    if model is None:
        print(">> Could not find a model.")
    else:
        print(">> Found a model.")
        print(">> Full program:")
        full_program = pretty_repr(program_ast, model)
        print(full_program)
        program_ast = parse(full_program)
        for i, (P, Q) in enumerate(zip(inputs, outputs)):
            if not verify(P, program_ast, Q, linv):
                print(">> Verification failed for example", i)
                print(">> Counterexample:")
                print(">> Input:", pretty_repr(P, model))
                print(">> Output:", pretty_repr(Q, model))
                break
        print(">> Verification successful.")

if __name__ == "__main__":
    main()