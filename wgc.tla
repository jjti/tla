---- MODULE wgc -----

EXTENDS FiniteSets, Naturals, Sequences, TLC

(* --algorithm WolfGoatCabbage {
    variables
        side = "left",
        left = {"wolf", "goat", "cabbage"},
        right = {},
        take = "";

    define {
        Options == (IF side = "left" THEN left ELSE right) \union {""}
        Stop ==
            \/ Cardinality(right) = 3
            \/ side = "right" /\ {"wolf", "goat"} \subseteq left
            \/ side = "left" /\ {"wolf", "goat"} \subseteq right
            \/ side = "right" /\ {"goat", "cabbage"} \subseteq left
            \/ side = "left" /\ {"goat", "cabbage"} \subseteq right
    };

    {
        loop:
        while (~Stop) {
            with (o \in Options) {
                if (o /= "") {
                    take := o;
                    if (side = "left") {
                        left := left \ {o};
                        right := right \union {o};
                    } else {
                        left := left \union {o};
                        right := right \ {o};
                    };
                } else {
                    take := "empty";
                };
            };

            if (Cardinality(right) = 3) { assert FALSE; };
            side := IF side = "left" THEN "right" ELSE "left"; \* flip sides
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a3cfccdd" /\ chksum(tla) = "b4abdc46")
VARIABLES side, left, right, take, pc

(* define statement *)
Options == (IF side = "left" THEN left ELSE right) \union {""}
Stop ==
    \/ Cardinality(right) = 3
    \/ side = "right" /\ {"wolf", "goat"} \subseteq left
    \/ side = "left" /\ {"wolf", "goat"} \subseteq right
    \/ side = "right" /\ {"goat", "cabbage"} \subseteq left
    \/ side = "left" /\ {"goat", "cabbage"} \subseteq right


vars == << side, left, right, take, pc >>

Init == (* Global variables *)
        /\ side = "left"
        /\ left = {"wolf", "goat", "cabbage"}
        /\ right = {}
        /\ take = ""
        /\ pc = "loop"

loop == /\ pc = "loop"
        /\ IF ~Stop
              THEN /\ \E o \in Options:
                        IF o /= ""
                           THEN /\ take' = o
                                /\ IF side = "left"
                                      THEN /\ left' = left \ {o}
                                           /\ right' = (right \union {o})
                                      ELSE /\ left' = (left \union {o})
                                           /\ right' = right \ {o}
                           ELSE /\ take' = "empty"
                                /\ UNCHANGED << left, right >>
                   /\ IF Cardinality(right') = 3
                         THEN /\ Assert(FALSE, 
                                        "Failure of assertion at line 40, column 43.")
                         ELSE /\ TRUE
                   /\ side' = (IF side = "left" THEN "right" ELSE "left")
                   /\ pc' = "loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << side, left, right, take >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == loop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
==========================

A farmer with a wolf, a goat, and a cabbage must cross a river by boat. The boat can carry only the farmer and a single item. If left unattended together, the wolf would eat the goat, or the goat would eat the cabbage. How can they cross the river without anything being eaten?
