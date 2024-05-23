---- MODULE wgc -----

EXTENDS FiniteSets, Naturals, Sequences, TLC

(* --algorithm WolfGoatCabbage {
    variables
        side = "left",
        left = {"wolf", "goat", "cabbage"},
        right = {};

    define {
        Stop ==
            \/ Cardinality(right) = 3
            \/ side = "right" /\ {"wolf", "goat"} \subseteq left
            \/ side = "left" /\ {"wolf", "goat"} \subseteq right
            \/ side = "right" /\ {"goat", "cabbage"} \subseteq left
            \/ side = "left" /\ {"goat", "cabbage"} \subseteq right
    };

    fair process (id=0)
    variables
        transport = "",
        options = {};
    {
        loop:
        while (~Stop) {
            \* choose one or nothing from this side of the bank
            options := IF side = "left" THEN left ELSE right;
            with (o \in options \union {""}) {
                if (o /= "") {
                    transport := o;
                    if (side = "left") {
                        left := left \ {o};
                        right := right \union {o};
                    } else {
                        left := left \union {o};
                        right := right \ {o};
                    };
                } else {
                    transport := "empty";
                };
            };

            if (Cardinality(right) = 3) {
                assert FALSE;
            };

            \* flip sides
            side := IF side = "left" THEN "right" ELSE "left";
        };
    };
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d0492699" /\ chksum(tla) = "642d7336")
VARIABLES side, left, right, pc

(* define statement *)
Stop ==
    \/ Cardinality(right) = 3
    \/ side = "right" /\ {"wolf", "goat"} \subseteq left
    \/ side = "left" /\ {"wolf", "goat"} \subseteq right
    \/ side = "right" /\ {"goat", "cabbage"} \subseteq left
    \/ side = "left" /\ {"goat", "cabbage"} \subseteq right

VARIABLES transport, options

vars == << side, left, right, pc, transport, options >>

ProcSet == {0}

Init == (* Global variables *)
        /\ side = "left"
        /\ left = {"wolf", "goat", "cabbage"}
        /\ right = {}
        (* Process id *)
        /\ transport = ""
        /\ options = {}
        /\ pc = [self \in ProcSet |-> "loop"]

loop == /\ pc[0] = "loop"
        /\ IF ~Stop
              THEN /\ options' = (IF side = "left" THEN left ELSE right)
                   /\ \E o \in options' \union {""}:
                        IF o /= ""
                           THEN /\ transport' = o
                                /\ IF side = "left"
                                      THEN /\ left' = left \ {o}
                                           /\ right' = (right \union {o})
                                      ELSE /\ left' = (left \union {o})
                                           /\ right' = right \ {o}
                           ELSE /\ transport' = "empty"
                                /\ UNCHANGED << left, right >>
                   /\ IF Cardinality(right') = 3
                         THEN /\ Assert(FALSE, 
                                        "Failure of assertion at line 45, column 17.")
                         ELSE /\ TRUE
                   /\ side' = (IF side = "left" THEN "right" ELSE "left")
                   /\ pc' = [pc EXCEPT ![0] = "loop"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << side, left, right, transport, options >>

id == loop

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(id)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
==========================

A farmer with a wolf, a goat, and a cabbage must cross a river by boat. The boat can carry only the farmer and a single item. If left unattended together, the wolf would eat the goat, or the goat would eat the cabbage. How can they cross the river without anything being eaten?
