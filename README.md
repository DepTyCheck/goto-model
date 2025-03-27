# goto-model

It is a model of some abstract assembly language. Key feature of the model is work with conditional jumps instead of [structured approach](https://en.wikipedia.org/wiki/Structured_programming).

## Current model

There is a machine that operates using only `n` registers.

Each register contains a typed value. The types can be `I` (Natural numbers) or `B` (Boolean).

Allowed operations:
 - `I`
   - `Add r0 r1 r2` - `r0 = r1 + r2`
 - `B`
   - `And r0 r1 r2` - `r0 = r1 & r2`
   - `Or r0 r1 r2` - `r0 = r1 | r2`

The language consists of the following instructions:
 - `exit` - finishes the program execution
 - `<expr>` - expression
 - `label_name:` - puts a label `label_name` into the program
 - `jmp label_name;` - unconditional jump to the label `label_name`
 - `condjmp label_name <cond>;` - conditional jump to the label `label_name`. Condition may take the following forms (`<const>` - compile-time known constant value):
   - `r ? <const>` where `?` is one of `<`, `>`, `<=`, `>=`, `==`, `!=`

## Specified model restrictions

 - A program may have unreachable code due to logical implications. High-level example:
 ```
 if (x > 10) {
   if (x < 10) {
     // unreachable code
   }
 }
 ```

- A program does not provide certain conditions for condjmps.
