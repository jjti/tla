---- MODULE cassandra -----

EXTENDS TLC

(* --algorithm Cassandra {
    variables
        test = 0;

    fair process (f \in {1, 2, 3}) {
        loop:
        print f;
    };
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8832e498" /\ chksum(tla) = "e6eaa612")
VARIABLES test, pc

vars == << test, pc >>

ProcSet == ({1, 2, 3})

Init == (* Global variables *)
        /\ test = 0
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ PrintT(f)
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ test' = test

f(self) == loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2, 3}: f(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2, 3} : WF_vars(f(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

===========================
