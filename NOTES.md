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

Is it enough to guarantee finiteness of 2 loops above? Nope, the combination may give an infinite loop
