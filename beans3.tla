
------------ MODULE beans3 ------------------
EXTENDS Integers
CONSTANTS R, G, B
ASSUME /\ R \in 0..100
       /\ G \in 0..100
       /\ B \in 0..100
       /\ R+G+B > 0

VARIABLES r,g,b

Init == /\ r = R
        /\ g = G
        /\ b = B

RR == /\ r > 1
      /\ r' = r - 2 /\ UNCHANGED g /\ UNCHANGED b

GG == /\ g > 1
      /\ g' = g - 2  /\ UNCHANGED r /\ UNCHANGED b

BB == /\ b > 1
      /\ b' = b - 2  /\ UNCHANGED r /\ UNCHANGED g

RG == /\ r > 0
      /\ g > 0
      /\ r' = r - 1
      /\ g' = g - 1
      /\ b' = b + 1

RB == /\ r > 0
      /\ b > 0
      /\ r' = r - 1
      /\ b' = b - 1
      /\ g' = g + 1

BG == /\ b > 0
      /\ g > 0
      /\ b' = b - 1
      /\ g' = g - 1
      /\ r' = r + 1

Next == \/ RR
        \/ GG
        \/ BB
        \/ RG
        \/ RB
        \/ BG
        \/ UNCHANGED r /\ UNCHANGED g /\ UNCHANGED b

vars == <<r,g,b>>
Spec == Init /\ [] [Next]_vars
             /\ WF_vars(Next) \* Weak Fairness

TypeOK ==   r+b+g >= 0

Termination == <> (r+b+g < 2)
DecreasingN == [] [r'+g'+b' < r+g+b]_vars

===========================================================

Consider a coffee can containing an arbitrary (but finite) number of beans. The beans come in 3 different colors: red, green, and blue. Now consider the following program:

Choose two beans from the can;

if they are the same color, toss them out

if they are different colors, toss them out and add a bean of the third color

Repeat.
