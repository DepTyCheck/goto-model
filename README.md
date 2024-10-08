# goto-model

It is a model of some abstract assembly language. Key feature of the model is work with conditional jumps and three generation steps before getting
a complete program.

## Current state

The language consists of the following instructions:
 - `exit;` - finishes the program execution
 - `nop;` - empty instruction, just to fill linear blocks a bit
 - `label_name:` - puts a label `label_name` into the program
 - `jmp label_name;` - unconditional jump to the label `label_name` instruction
 - `condjmp label_name;` - conditional jump to the label `label_name` instruction. It means that 2 paths are possible: either to just skip this instruction,
 or to follow the jump

The model is able to produce any program which CFG is a DAG (Directed Acyclic Graph)
