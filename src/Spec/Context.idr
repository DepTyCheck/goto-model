module Spec.Context

import public Spec.Context.Source
import public Spec.Context.Loop

{-
  the Program starts from 1 point
  this point fixates undetermined values
  after that, I work with these initial values
  I can remove any of them
  can I introduce any? No during usual instruction, but during merge - yes
  I must store the global count of undetermined values in order to save myself from sudden index conflicts
  This value must be used during every merge. Thankfully, the program is built linearly
  Then, what happens in a loop?
  loop may make many iterations
  after a loop we do similar things as in merge. Thus, during unwind we use the same global value to introduce changed undetermined values.
  If we can, we just change the expressions using the same undet values from saved context

  Step:
    Choice sources to sink (mask magic)
    Merge sources (function)
    Make a linear block (argument)
    Push sources (Possible)

  To start a loop:
  - there are no restrictions

  During a loop we forbid
  - merge from free sources (even though it could be acceptable... how? These free sources are known at the start
    of the loop. They must satisfy the guarantees, i.e. any GValue and GType are bijected with values from these free sources. Of course,
    they must be winded as the main context after)
    [Applies at the moment of source choice]
       MaybeStartLoop mergedSrc remSrcs' mergedUc curSrc remSrcs curUc =>  -- TODO: I can remove these 3 arguments and take Nat as number of new loops
  - making a LinearBlock where there's no undet variable depending on self
  
  To finish a loop:
  - there must be an undet value that depends on self
  - there must be an undet self-depending value that is monotonic
  
  Solutions:
  I. Add 2 constructors to Program: BeginLoop and EndLoop
     - BeginLoop: save current context, wind it and go further
     - EndLoop: must copy logic of Step because need to check 2nd finish condition. Also, returns back the context
     Pros:
     - very easy to begin new loop
     - need to change Step: filter by 2nd condition
     - copypaste to end the loop
     Cons:
     - every function will have to handle BeginLoop, EndLoop
  II. Modify Step directly
      - Need to somehow open loops
      - Need to rework the choice and extraction of sources (can help to get rid of HasTrueBut)
      - Merge is unchanged
      - Linear block is unchanged
      - add filter by 2nd condition
      - Possible also closes loops
     Pros:
     - fixes current design issue with HasTrueBut
     - no completely new cases in functions
     - no copypaste
     Cons:
     - too many variables in one constructor
     - probably bad derivation order
-}

