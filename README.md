## Final Project 236347

### While Language Extension

In this project, we extended the base While language to support several new features, enhancing its expressiveness and
flexibility for synthesis tasks:

- **Integer Holes (`??`)**: We introduced `??` as a numeric placeholder. During synthesis, `??` can be replaced by a
  numeric literal that satisfies the given constraints, enabling flexible handling of unspecified values within
  programs.

- **Boolean Expressions**: We added support for boolean expressions to enrich conditional logic. The language now
  includes:
    - **Constants**: `true` and `false`.
    - **Logical Operators**: `and`, `or`, and `not` for combining boolean values.

- **Arrays**: Arrays provide structured data storage without the need for explicit declarations. Key features include:
    - **Dynamic Indexing**: Array indices can be any numeric expression, including `??`, allowing for flexible and
      dynamic index assignment.
    - **Assignment**: Specific positions within arrays can be assigned values, making arrays versatile for iterative and
      conditional operations.
    - **No Predefined Bounds**: Arrays are unbounded, meaning they can be indexed without limitations on size or
      declared range.

- **Assert Statements**: We added support for `assert` statements to enforce behavioral constraints within programs.
  Assertions allow the user to specify conditions that must hold at certain points in the code. During synthesis, the
  tool fills in values for `??` such that all assertions are satisfied.

These extensions allow for the creation of more complex programs, enabling synthesized solutions that adapt to
unspecified numeric values, logical conditions, data structures, and program invariants.

---

### Running the Tool

Follow these steps to set up and run the tool:

1. **Unzip the submission**: Begin by unzipping the submission to your local machine.

2. **Install Requirements**: Navigate to the project directory and install the required Python packages:
   ```bash
   pip install -r requirements.txt
   ```

3. **Run the Tool**: Start the tool by running:
   ```bash
   python main.py
   ```

4. **Enter Program Code**: You’ll be prompted to enter the program code (CLI-based input). Type your code line by line
   and end the input with a dot (`.`) on a new line. If the program cannot be parsed, an error will be displayed, and
   you’ll have the opportunity to try again. This input validation applies to all inputs in the tool.

5. **Specify PBEs (Optional)**: After the program code, you can enter one or more **Programming By Example (PBE)**
   pairs, which are optional. Each PBE consists of:
    - **Input Condition**: A boolean expression in the While language specifying an initial condition.
    - **Output Condition**: A corresponding boolean expression defining the expected final state.

   The tool will synthesize a program that ensures each input condition at the start of the program results in the
   corresponding output condition at the end.

6. **Enter Loop Invariants**: Lastly, you may enter a **loop invariant** as a boolean expression to assist with
   synthesis in programs containing loops. This is optional and can be left empty if not needed.

7. **Run the Synthesizer**: Once all inputs are provided, the synthesizer will attempt to generate a program with the
   specified constraints. If synthesis fails, an error message will indicate the issue. If successful, the tool will
   display:
    - **The Synthesized Program**: This output will show the program with `??` filled in with specific values.
    - **Loop Unfolding Count**: The tool will indicate the number of loop unfoldings used.

### Running the Test

1. **Unzip the submission**: Begin by unzipping the submission to your local machine.

2. **Install Requirements**: Navigate to the project directory and install the required Python packages:
   ```bash
   pip install -r requirements.txt
   ```

3. **Run the Tets**: Start the test by running:
   ```bash
   python -m pytest tests.py
   ```

---

### Features Implemented

Our tool incorporates several key features for synthesizing programs with the While language:

1. **Basic Synthesis with `??` for PBEs and Assertions**: We implemented synthesis support for both **Programming By
   Example (PBE)** and **assert statements**. The tool can replace instances of `??` with numeric literals that satisfy
   both PBEs and assert conditions. Users can provide PBEs, assertions, or a mix of both to guide synthesis, giving
   flexibility in specification.

2. **Weakest Precondition (WP) Enhancements for Loops**: We enhanced the WP calculation for loops by incorporating
   information extracted from assert statements within the loops. This reduces the need for explicit loop invariants, as
   the tool can leverage assertions to verify loop correctness. For example, in the program below (`test no_unfold`), no
   invariant is needed to show that the loop is endless and that the final assertion is unreachable:
   ```plaintext
   x := ??;
   while not (x = 0) do (
       assert (x > 0);
       x := x + 1
   );
   assert false
   ```
   The tool will synthesize a value for `x` that satisfies the loop and will recognize that the loop is endless,
   preventing the program from reaching `assert false`.

3. **Loop Unfolding**: To handle loops more effectively, we implemented a **loop unfolding** feature. The tool first
   attempts synthesis without unfolding the loop. If that fails, it will incrementally unroll the loop up to a specified
   maximum (default `MAX_UNFOLDING` is 10, which can be adjusted in `wp.py`). This iterative unfolding helps the tool
   handle cases where an exact unfolding depth is needed to satisfy conditions.

   For example, in the program below (`test zeroing_out`), synthesis succeeds with three unfoldings:
   ```plaintext
   x := ??;
   y := x;
   assert (x > 2);
   while (x > 0) do (
       x := x - 1;
       y := y - ??
   );
   assert (y = 0)
   ```
   Here, the tool synthesizes `3` for the initial `x := ??`, ensuring `x > 2` holds at the start, and `1` for `??`
   within the loop body. After three unfoldings, `y` reaches zero, satisfying the final assertion `y = 0`.

4. **Arrays**: The language now supports arrays that do not require explicit declaration, allowing for dynamic usage.
   There are no limitations on the indexing of arrays, meaning you can access and modify any element using a numeric
   expression as an index.

   **Use of `??` in Indices**: A notable feature is the ability to use `??` within array indices. This allows for
   greater
   flexibility in synthesizing programs, as the index can be dynamically determined during synthesis. For example, you
   can assign values to specific positions in an array using expressions that include `??` as follows:
   ```plaintext
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
   ```
   This capability enhances the expressive power of the language, enabling more complex data manipulations and
   algorithms.

## Interesting cases

1. **Binary search**:

   ```plaintext
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
   ```
   With following PBEs:

    ```plaintext
    target = 1;  index = 0
    target = 2;  index = -1
    target = 40; index = 12
    target = 25; index = 9
    ```

   Synthesized code:

    ```plaintext
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
   index := -1;

   while low <= high do (
       mid := (low + high) / 2;
       if arr[mid] = target then (
           index := mid;
           low := high + 2
       )
       else if arr[mid] < target then (
           low := mid + 1
       )
       else (
           high := mid - 1
       )
   )
   ```

2. **Swap**:

   ```plaintext
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
   ```

   Synthesized code:

    ```plaintext
    a[0] := 7;
    a[1] := 5;
    a[2] := 13;
    a[3] := 17;
    
    a[7] := a[1];
    a[7] := a[0];
    a[0] := a[7];
    
    assert (a[0] < a[1]);
    assert (a[1] < a[2]);
    assert (a[2] < a[3])
   ```
   *Note*: Our tool can't synthesize array assigmnets where both index and the value are ??.
   In addition, we couldn't synthesize a case with two swaps.

3. **Complex**:

   ```plaintext
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
   ```

   Synthesized code:

    ```plaintext
    x := 6;
    y := -1;
    z := 0;
    assert (x > y);
    if (x > 5) then (
        z := (z + 0)
    ) else (
        z := (z - 0));
    while (x > y) do (
        x := (x - -1);
        assert (x > y);
        if (z < 0) then (
            y := (y + 0)
        ) else (
            y := (y - -1));
        assert (y >= 0)
    );
    assert ((x = y) or (x = (y - 1)))
   ```

   More cases can be found in `tests.py`.
