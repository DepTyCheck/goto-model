# Just some notes about the model

## First idea

The primary solution was trying to create the whole program at once in a linear pattern, by diving goto into 2 parts:
```
source ----goto----> sink
```

It didn't work because I understood badly what I was doing, or trying to do.

## Syntactic success

Why to bother with linearity? Let's just start with a CFG, numerate its vertices (0 is the root) and build a program, using it as a guidance.

For the continuation-passing style I need some structure representing a graph, that is "quite recursive". That is, I don't need to check
a lot of properties to just make it bigger.

What do I know about my CFGs despite of being a graph?
 1. There's a starting vertex, from which I can reach any other
 2. There are no more than 2 edges going out of any vertex

I remembered that binary trees were actually a great structure in terms of functional programming! Moreover, my CFGs had it
as their part (as long as property 1 existed). Thus, I started experimenting with the thing

I quickly realised that the usage of absolute indices would again give me terrible proofs in constructors, so eventually I moved to Brujin indices,
and it was the last part of the puzzle.

## Semantic... eew?

### First attempt

It is, probably, impossible to enumerate all total programs with any CFG allowed. Instead, I bound the set to only such CFGs that are DAGs plus cycles
where reversed edges connect a parent and a child in the abstract tree.

It is still a very rich set. For example, consider the following CFG:
```
 |->Lin
 |  Blk
 |   |
 |  Lin<-|
 |-<Blk  | 
     |   |
    Lin  |
    Blk>-|
```
This CFG is impossible to create with casual `for` or `while` constructions.

The question is, how to generate a dynamically typed total program with conditions from here?
 1. I need to merge types from different paths
 2. I need to know cycles declaratively as I will need to ensure there is a finish in them

Thus, I need a proper structure to work with DTBC (Directed Tree-Based with Cycles). In such a graph, I can definitely say which vertices are the tops of cycles. 

Is it enough to guarantee finiteness of 2 loops above? Nope, the combination may give an infinite loop.

### Second attempt

**Tricky example:**
```
       y=3
        |
|->    x=0
|      y-=1
|       |
|      x+=1      <-|
|-< condjmp y>0    |
        |          |
       y=10        |
    condjmp x<10 >-|
        |
        |
```
Here, both small loops are finite, but their combination is infinite.


**Important notes:**
 - Every loop must save some part of the context
 - The way out of a loop may not be in its end. For example:
   ```
   i <- ...;
   j = 0
   for (; i < 10; ++i) {
      j = f(i) + j;
   }
   exit;
   ```
   In terms of CFG it can be written as
   ```
          i<-...
           j=0
            |
   |t< condjmp i>=10 <-|
   |        |f         |
   |     j=f(i)+j      |
   |       jmp       >-|
   |        
   |->     exit
   ```
 - Every path in the CFG must be reachable. That is, every `condjmp` instruction must depend on some unknown value
 - Every condition check gives information about the value. It must be considered to do the point above properly:
   ```
          i<-...
            |
   |-t< condjmp i>=10
   |        |f
   ||t< condjmp i>=10
   ||       |f
   ||      j=32
   ||      exit
   ||
   ||->    j=0
   |       exit
   |
   |-->    j=16
           exit
   ```
   In this program it's impossible to reach the linear block with `j=0`
 - Certain conditions may give more information about a value:
   ```
   x = False  -- x's type is Bool
   is_x_bool = True

   if (some_cond) {
      x = 10
      is_x_bool = False
   }

   if (is_x_bool) {
      -- here x is definitely Bool
   } else {
      -- here x is definitely Integer
   }
   ```

#### Approximation

 - Let's allow only nested loops
 - Let's not allow DAG + loops, only tree + loops
 - Let's not think about the problem of implicative conditions (j >= 10 -> j >= 5)
 - Let's not think about situations when type can be introspected due to the context (is_x_bool)



#### Value

Value has
 - Type <-> allowed operations
 - Determination <-> is it valid for condition checking
 - Raw value <-> expression using _determined/undetermined values_
   **Note:** actually, 1 value can be stored as 2 boundaries with the same expression

Minimum amount of types:
 - B[oolean] - And and Or operations
 - I[nteger] - Add operation

Unknown - a special Value which value is unknown

#### Model

Tree + loops CFG allows to make a model where every block is created mostly sequentially:
 - We can clearly understand the current stack of loops which we are in
 - We can clearly say that we never get into any of the blocks already created; we merely come from them

Thus, we can speak about the context of generation:

Source is a place from which `jmp`/`condjmp` happens. It is *open* if it is outside the loop stack, and *closed* otherwise.

There's no need in sinks yet as long as we don't allow DAGs and all loops are nested.

**Note:** I may not fix the precise form of the condition, only the variable(s) it uses

Context has
 - Current loop stack. Each element looks like (loopContextGuarantees, loopSavedContext, closedSources)
   - loopContextGuarantess - values and types that are must be preserved
   - loopSavedContext - the context right before we've entered the loop
   - closedSources - a list of closed sources
 - Current open sources
 - Current values (in registers or in memory)
 - Auxiliary data
   - Unknown values counter which is needed to introduce new unknown values

The greatest question of the whole model: how to operate with loops? Because it leads to severe context shift:

 - Loop introduction. It is always possible. We must declare what part of the context is saved during the loop iterations. It can be different things:
   1. Save a whole value
   2. Save a value's type only
   Moreover, in the loop we don't know current iteration, which means it's impossible to guess the values that are not guaranteed to be preserved. So, the algorithm:
   1. Save the current context
   2. Create a new unknown variables counter
   3. Choose a part of the context to be preserved
   4. Create the new context values and types
   5. Copy the new context's parts that are related to the guarantees

 - Loop finish. It is possible when
   1. We intend to add another edge further
   2. There's a closed source that uses a decreasing/increasing variable
   Another thing is to mutate the context to a state that it will have after the loop. I can find all the preservations during the iteration (values, types). The algorithm:
   1. Observe the context of the loop iteration to find preservations:
     - Values that depend only on themselves. For such, we can find their iteration function
     - Preserved values (check loop guarantees plus there may be constants)
     - Preserved types (same stuff as above)
   2. Apply the loop diff to the saved context:
     - If a value is preserved, then just put it
     - If only a type is preserved,
       - and there's the iteration function, introduce new value in the saved context (will require to use another new value - number of loop iterations)
       - there's no iteration function - just new value
     - Nothing preserved
       - Just make a value with unknown type
