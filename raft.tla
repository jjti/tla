---- MODULE raft -----

EXTENDS Integers, Sequences, TLC

CONSTANTS
    N,        \* server count.
    M,        \* count for a majority.
    TermLimit \* limit of steps after which a process stops.

ASSUME
    /\ N          \in 1..7
    /\ M          \in 1..N
    /\ TermLimit  \in 1..10

(* --algorithm Raft {
    variables
        \* states of the leaders. leader, follower, or candidate.
        states = [l \in Leaders |-> "follower"],

        \* each server's current term.
        currentTerm = [l \in Leaders |-> 1],

        \* votes for each term. key is the term of voting, value is the pid of the Voter.
        votes = [t \in 1..TermLimit+1 |-> << >>], \* TODO: get rid of the +1, shouldn't need it.

        \* servers send followers messages via AppendEntries.
        msgs = [l \in Leaders |-> << >>],

        \* whether the last heartbeat was dropped.
        msgs_dropped = [l \in Leaders |-> TRUE],

        \* the applied logs on each server.
        logs = [l \in Leaders |-> << >>];

    define {
        Leaders   == 1     .. N
        Voters    == N+1   .. N*2
        Followers == N*2+1 .. N*3

        \* "at most one leader can be elected in a given term."
        ElectionSafety == 
            \A a \in Leaders:
                IF   states[a] = "leader"
                THEN \A b \in Leaders: b = a \/ states[b] /= "leader" \/ currentTerm[b] /= currentTerm[a]
                ELSE TRUE

        TypeOK ==
            ElectionSafety
    }

    \* "Invoked by candidates to gather votes"
    macro RequestVote(pid) {
        \* wait for a "dropped" heartbeat, ie a period where we have not heard from a leader.
        \* do not vote twice. If we already voted in the next term, don't do anything.
        await msgs_dropped[pid] /\ Len(SelectSeq(votes[currentTerm[pid]+1], LAMBDA v: v.src = pid)) = 0;

        \* "Send RequestVote RPCs to all other servers"
        states[pid]             := "candidate";        \* "conversion to candidate"
        currentTerm[pid]        := currentTerm[pid]+1; \* "Increment currentTerm"
        votes[currentTerm[pid]] := Append(votes[currentTerm[pid]], [
            src         |-> pid,
            candidateId |-> pid
        ]);
        msgs_dropped[pid] := FALSE;
    }

    \* check votes from the election. This server wins if a majority of
    \* other servers voted for it in the same term.
    macro CheckVotes(pid) {
        await
            \/ \E l \in Leaders: Len(SelectSeq(votes[currentTerm[pid]], LAMBDA v: v.candidateId = l)) >= M
            \/ states[pid] /= "candidate";

        \* "If votes received from majority of servers: become leader"
        if (states[pid] = "candidate" /\ Len(SelectSeq(votes[currentTerm[pid]], LAMBDA v: v.candidateId = pid)) >= M) {
            states[pid] := "leader";
        };
    }

    \* send an AppendEntries request to followers.
    macro AppendEntries(pid, data) {
        msgs := [l \in Leaders |->
            IF   l = pid
            THEN msgs[l]
            ELSE Append(msgs[l], [
                src   |-> pid,
                term  |-> currentTerm[pid],
                index |-> Len(logs[pid]),
                data  |-> data
            ])
        ];
    }

    \* leader process.
    fair process (l \in Leaders)
    variables pid = self; {
        leader_loop:
        while (currentTerm[pid]+1 <= TermLimit) {
            leader_election:
            while (states[pid] /= "leader") {
                \* when heartbeat timer times out, start election as candidate.
                request_vote:
                RequestVote(pid);

                \* check if this leader won.
                check_votes:
                CheckVotes(pid);
            };

            \* send empty data.
            heartbeat:
            AppendEntries(pid, "");
        };
    };


    \* voter process.
    fair process (v \in Voters)
    variables pid = self - N, req = {}; {
        voter_loop:
        while (currentTerm[pid]+1 <= TermLimit) {
            await
                \* "Reply false if term < currentTerm"
                /\ Len(SelectSeq(votes[currentTerm[pid]+1], LAMBDA v: v.src /= pid)) > 0
                \* "If votedFor is null or candidateId"
                /\ Len(SelectSeq(votes[currentTerm[pid]+1], LAMBDA v: v.src = pid)) = 0;

            \* Just vote for the first one.
            req := Head(votes[currentTerm[pid]+1]);
            votes[currentTerm[pid]+1] := Append(votes[currentTerm[pid]+1], [
                src         |-> pid,
                candidateId |-> req.candidateId
            ]);
        };
    };

    \* follower process.
    fair process (f \in Followers)
    variables pid = self - N*2, req = {}; {
        follower_loop:
        while (currentTerm[pid]+1 <= TermLimit) {
            \* wait for a new heartbeat to arrive.
            follower_recv_heartbeat:
            await Len(msgs[pid]) > 0;

            req       := Head(msgs[pid]);
            msgs[pid] := Tail(msgs[pid]);

            either {
                if (req.src /= pid /\ req.term >= currentTerm[pid]) {
                    states[pid]       := "follower";
                    currentTerm[pid]  := req.term;
                };

                msgs_dropped[pid] := FALSE;
            } or {
                msgs_dropped[pid] := TRUE;
            };
        };
    };
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "59fe790b" /\ chksum(tla) = "4c462440")
\* Process variable pid of process l at line 96 col 15 changed to pid_
\* Process variable pid of process v at line 119 col 15 changed to pid_v
\* Process variable req of process v at line 119 col 31 changed to req_
VARIABLES states, currentTerm, votes, msgs, msgs_dropped, logs, pc

(* define statement *)
Leaders   == 1     .. N
Voters    == N+1   .. N*2
Followers == N*2+1 .. N*3


ElectionSafety ==
    \A a \in Leaders:
        IF   states[a] = "leader"
        THEN \A b \in Leaders: b = a \/ states[b] /= "leader" \/ currentTerm[b] /= currentTerm[a]
        ELSE TRUE

TypeOK ==
    ElectionSafety

VARIABLES pid_, pid_v, req_, pid, req

vars == << states, currentTerm, votes, msgs, msgs_dropped, logs, pc, pid_, 
           pid_v, req_, pid, req >>

ProcSet == (Leaders) \cup (Voters) \cup (Followers)

Init == (* Global variables *)
        /\ states = [l \in Leaders |-> "follower"]
        /\ currentTerm = [l \in Leaders |-> 1]
        /\ votes = [t \in 1..TermLimit+1 |-> << >>]
        /\ msgs = [l \in Leaders |-> << >>]
        /\ msgs_dropped = [l \in Leaders |-> TRUE]
        /\ logs = [l \in Leaders |-> << >>]
        (* Process l *)
        /\ pid_ = [self \in Leaders |-> self]
        (* Process v *)
        /\ pid_v = [self \in Voters |-> self - N]
        /\ req_ = [self \in Voters |-> {}]
        (* Process f *)
        /\ pid = [self \in Followers |-> self - N*2]
        /\ req = [self \in Followers |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Leaders -> "leader_loop"
                                        [] self \in Voters -> "voter_loop"
                                        [] self \in Followers -> "follower_loop"]

leader_loop(self) == /\ pc[self] = "leader_loop"
                     /\ IF currentTerm[pid_[self]]+1 <= TermLimit
                           THEN /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << states, currentTerm, votes, msgs, 
                                     msgs_dropped, logs, pid_, pid_v, req_, 
                                     pid, req >>

leader_election(self) == /\ pc[self] = "leader_election"
                         /\ IF states[pid_[self]] /= "leader"
                               THEN /\ pc' = [pc EXCEPT ![self] = "request_vote"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "heartbeat"]
                         /\ UNCHANGED << states, currentTerm, votes, msgs, 
                                         msgs_dropped, logs, pid_, pid_v, req_, 
                                         pid, req >>

request_vote(self) == /\ pc[self] = "request_vote"
                      /\ msgs_dropped[pid_[self]] /\ Len(SelectSeq(votes[currentTerm[pid_[self]]+1], LAMBDA v: v.src = pid_[self])) = 0
                      /\ states' = [states EXCEPT ![pid_[self]] = "candidate"]
                      /\ currentTerm' = [currentTerm EXCEPT ![pid_[self]] = currentTerm[pid_[self]]+1]
                      /\ votes' = [votes EXCEPT ![currentTerm'[pid_[self]]] =                            Append(votes[currentTerm'[pid_[self]]], [
                                                                                  src         |-> pid_[self],
                                                                                  candidateId |-> pid_[self]
                                                                              ])]
                      /\ msgs_dropped' = [msgs_dropped EXCEPT ![pid_[self]] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "check_votes"]
                      /\ UNCHANGED << msgs, logs, pid_, pid_v, req_, pid, req >>

check_votes(self) == /\ pc[self] = "check_votes"
                     /\ \/ \E l \in Leaders: Len(SelectSeq(votes[currentTerm[pid_[self]]], LAMBDA v: v.candidateId = l)) >= M
                        \/ states[pid_[self]] /= "candidate"
                     /\ IF states[pid_[self]] = "candidate" /\ Len(SelectSeq(votes[currentTerm[pid_[self]]], LAMBDA v: v.candidateId = pid_[self])) >= M
                           THEN /\ states' = [states EXCEPT ![pid_[self]] = "leader"]
                           ELSE /\ TRUE
                                /\ UNCHANGED states
                     /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                     /\ UNCHANGED << currentTerm, votes, msgs, msgs_dropped, 
                                     logs, pid_, pid_v, req_, pid, req >>

heartbeat(self) == /\ pc[self] = "heartbeat"
                   /\ msgs' =         [l \in Leaders |->
                                  IF   l = pid_[self]
                                  THEN msgs[l]
                                  ELSE Append(msgs[l], [
                                      src   |-> pid_[self],
                                      term  |-> currentTerm[pid_[self]],
                                      index |-> Len(logs[pid_[self]]),
                                      data  |-> ""
                                  ])
                              ]
                   /\ pc' = [pc EXCEPT ![self] = "leader_loop"]
                   /\ UNCHANGED << states, currentTerm, votes, msgs_dropped, 
                                   logs, pid_, pid_v, req_, pid, req >>

l(self) == leader_loop(self) \/ leader_election(self) \/ request_vote(self)
              \/ check_votes(self) \/ heartbeat(self)

voter_loop(self) == /\ pc[self] = "voter_loop"
                    /\ IF currentTerm[pid_v[self]]+1 <= TermLimit
                          THEN /\ /\ Len(SelectSeq(votes[currentTerm[pid_v[self]]+1], LAMBDA v: v.src /= pid_v[self])) > 0
                                  
                                  /\ Len(SelectSeq(votes[currentTerm[pid_v[self]]+1], LAMBDA v: v.src = pid_v[self])) = 0
                               /\ req_' = [req_ EXCEPT ![self] = Head(votes[currentTerm[pid_v[self]]+1])]
                               /\ votes' = [votes EXCEPT ![currentTerm[pid_v[self]]+1] =                              Append(votes[currentTerm[pid_v[self]]+1], [
                                                                                             src         |-> pid_v[self],
                                                                                             candidateId |-> req_'[self].candidateId
                                                                                         ])]
                               /\ pc' = [pc EXCEPT ![self] = "voter_loop"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << votes, req_ >>
                    /\ UNCHANGED << states, currentTerm, msgs, msgs_dropped, 
                                    logs, pid_, pid_v, pid, req >>

v(self) == voter_loop(self)

follower_loop(self) == /\ pc[self] = "follower_loop"
                       /\ IF currentTerm[pid[self]]+1 <= TermLimit
                             THEN /\ pc' = [pc EXCEPT ![self] = "follower_recv_heartbeat"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << states, currentTerm, votes, msgs, 
                                       msgs_dropped, logs, pid_, pid_v, req_, 
                                       pid, req >>

follower_recv_heartbeat(self) == /\ pc[self] = "follower_recv_heartbeat"
                                 /\ Len(msgs[pid[self]]) > 0
                                 /\ req' = [req EXCEPT ![self] = Head(msgs[pid[self]])]
                                 /\ msgs' = [msgs EXCEPT ![pid[self]] = Tail(msgs[pid[self]])]
                                 /\ \/ /\ IF req'[self].src /= pid[self] /\ req'[self].term >= currentTerm[pid[self]]
                                             THEN /\ states' = [states EXCEPT ![pid[self]] = "follower"]
                                                  /\ currentTerm' = [currentTerm EXCEPT ![pid[self]] = req'[self].term]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << states, 
                                                                  currentTerm >>
                                       /\ msgs_dropped' = [msgs_dropped EXCEPT ![pid[self]] = FALSE]
                                    \/ /\ msgs_dropped' = [msgs_dropped EXCEPT ![pid[self]] = TRUE]
                                       /\ UNCHANGED <<states, currentTerm>>
                                 /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                                 /\ UNCHANGED << votes, logs, pid_, pid_v, 
                                                 req_, pid >>

f(self) == follower_loop(self) \/ follower_recv_heartbeat(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Leaders: l(self))
           \/ (\E self \in Voters: v(self))
           \/ (\E self \in Followers: f(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Leaders : WF_vars(l(self))
        /\ \A self \in Voters : WF_vars(v(self))
        /\ \A self \in Followers : WF_vars(f(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=======================
