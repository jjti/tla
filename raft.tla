---- MODULE raft -----

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    N, \* server count.
    M, \* count for a majority.
    T, \* term limit.
    E  \* log entry count.

ASSUME
    /\ N \in 1..7
    /\ M \in 1..N
    /\ T \in Nat
    /\ E \in Nat

(* --algorithm Raft {
    variables
        \* states of the leaders. leader, follower, or candidate.
        states = [l \in Leaders |-> "follower"],

        \* each server's current term.
        currentTerm = [l \in Leaders |-> 1],

        \* whether the last heartbeat was dropped.
        electionTimeout = [l \in Leaders |-> TRUE],

        \* votes for each term. key is the term of voting, value is the pid of the Voter.
        votes = [t \in 1..T+1 |-> << >>], \* TODO: get rid of the +1, shouldn't need it.

        \* leaders send followers messages via AppendEntries.
        msgs = [l \in Leaders |-> << >>],

        \* "log entries; each entry contains command for state machine,
        \* and term when entry was received by leader (first index is 1)".
        logs = [l \in Leaders |-> << >>];

    define {
        Leaders   == 1     .. N
        Voters    == N+1   .. N*2
        Followers == N*2+1 .. N*3

        ToSet(seq)  == {seq[i]: i \in 1..Len(seq)}
        MaxInSet(S) == CHOOSE x \in S : \A y \in S : y <= x
        MinInSet(S) == CHOOSE x \in S : \A y \in S : x =< y

        \* whether all log entries between two servers match up to the max matching entry.
        MatchingPrefix(l1, l2) ==
            LET
                Min(a, b)       == IF a < b THEN a ELSE b
                MinLen          == Min(Len(logs[l1]), Len(logs[l2]))
                MatchingUpTo(j) == {i \in 1..j: logs[l1][i].term = logs[l2][i].term /\ logs[l1][i].cmd = logs[l2][i].cmd}
                MaxMatching     == MaxInSet(MatchingUpTo(MinLen)) \* max index of matching log entry
            IN
                IF MinLen = 0 THEN TRUE ELSE MatchingUpTo(MaxMatching) = 1..MaxMatching

        \* whether the leader l1 is as at least as up to date as l2.
        \* "Raft determines which of two logs is more up-to-date by comparing the index and term of the last entries in the
        \* logs. If the logs have last entries with different terms, then the log with the later term is more up-to-date. If the logs
        \* end with the same term, then whichever log is longer is more up-to-date."
        UpToDate(l1, l2) ==
            IF   Len(logs[l2]) = 0
            THEN TRUE
            ELSE Len(logs[l1]) > 0 /\
                (logs[l1][Len(logs[l1])].term > logs[l2][Len(logs[l2])].term \/
                (logs[l1][Len(logs[l1])].term = logs[l2][Len(logs[l2])].term /\ Len(logs[l1]) >= Len(logs[l2])))

        \* "at most one leader can be elected in a given term."
        ElectionSafety == 
            \A a \in {l \in Leaders : states[l] = "leader"}:
                \A b \in Leaders \ {a}: states[b] /= "leader" \/ currentTerm[a] /= currentTerm[b]

        \* "a leader never overwrites or deletes entries in its log; it only appends new entries."
        LeaderAppendOnly == 
            [][
                \A l \in {l \in Leaders: states[l] = "leader"}:
                    \A i \in 1..Len(logs[l]): logs'[l][i].cmd = logs[l][i].cmd /\ logs'[l][i].term = logs[l][i].term
            ]_logs

        \* "if two logs contain an entry with the same index and term, then the logs are identical in
        \* all entries up through the given index."
        \* going to check: find the last max index they match (term/index/cmd). Assert all entries up to that match too.
        LogMatching ==
            \A a, b \in Leaders:
                (a # b) => MatchingPrefix(a, b)

        \* "if a log entry is committed in a given term, then that entry will be present in the logs
        \* of the leaders for all higher-numbered terms."
        \* just going to check this with: servers with higher terms have all the logs of servers with lower terms
        LeaderCompleteness ==
            \A a \in Leaders:
                \A b \in {l \in Leaders : currentTerm[l] > currentTerm[a] /\ states[l] = "leader"}:
                    \A i \in 1..Len(logs[a]):
                        \E j \in 1..Len(logs[b]): logs[i].cmd = logs[j].cmd

        \* "if a server has applied a log entry at a given index to its state machine, no other server
        \* will ever apply a different log entry for the same index"
        StateMachineSafety ==
            \A a, b \in Leaders:
                (a # b) => \A i \in 1..Len(logs[a]): i > Len(logs[b]) \/ logs[a][i].cmd = logs[b][i].cmd
    }

    \* "Invoked by candidates to gather votes"
    macro RequestVote(pid) {
        \* "If election timeout elapses without receiving AppendEntries RPC from current leader or
        \* granting vote to candidate: convert to candidate"
        await electionTimeout[pid] /\ Len(SelectSeq(votes[currentTerm[pid]+1], LAMBDA v: v.src = pid)) = 0;

        \* "Send RequestVote RPCs to all other servers"
        states[pid]             := "candidate";        \* "conversion to candidate"
        currentTerm[pid]        := currentTerm[pid]+1; \* "Increment currentTerm"
        votes[currentTerm[pid]] := Append(votes[currentTerm[pid]], [
            src          |-> pid,
            candidateId  |-> pid
        ]);
        electionTimeout[pid] := FALSE;
    }

    \* check votes from the election. This server wins if a majority of other servers voted for it in the same term.
    macro CheckVotes(pid) {
        await
            \/ Len(SelectSeq(votes[currentTerm[pid]], LAMBDA v: v.candidateId = pid)) >= M
            \/ states[pid] /= "candidate";

        \* "If votes received from majority of servers: become leader"
        if (states[pid] = "candidate" /\ Len(SelectSeq(votes[currentTerm[pid]], LAMBDA v: v.candidateId = pid)) >= M) {
            states[pid] := "leader";
        };
    }

    \* send an AppendEntries request to followers.
    macro AppendEntries(pid, cmd, prevLogIndex, prevLogTerm) {
        msgs := [l \in Leaders |->
            IF   l = pid
            THEN msgs[l]
            ELSE Append(msgs[l], [
                src          |-> pid,
                term         |-> currentTerm[pid],
                prevLogIndex |-> prevLogIndex,
                prevLogTerm  |-> prevLogTerm,
                cmd          |-> cmd
            ])
        ];
    }

    \* leader process.
    fair process (l \in Leaders)
    variables
        pid          = self,
        cmd          = 0,    \* current client request index. Goes up to E.
        prevLogIndex = 0,
        prevLogTerm  = 0;    \* "index of log entry immediately preceding new ones"
    {
        leader_loop:
        while (currentTerm[pid]+1 <= T /\ cmd < E) {
            leader_election:
            while (states[pid] /= "leader") {
                \* when heartbeat timer times out, start election as candidate.
                request_vote:
                RequestVote(pid);

                \* check if this leader won.
                check_votes:
                CheckVotes(pid);
            };

            \* "Upon election: send initial empty AppendEntries RPCs (heartbeat) to each server;"
            heartbeat:
            AppendEntries(pid, -1, E+1, E+1);

            \* Send entries from the point of the max entry we have seen.
            cmd          := IF Len(logs[pid]) > 0 THEN logs[pid][Len(logs[pid])].cmd + 1 ELSE 1;
            prevLogIndex := Len(logs[pid]);
            prevLogTerm  := IF Len(logs[pid]) > 0 THEN logs[pid][Len(logs[pid])].term ELSE 0;

            \* "If command received from client: append entry to local log"
            logs[pid] := Append(logs[pid], [
                term |-> currentTerm[pid],
                cmd  |-> cmd
            ]);

            \* "If last log index ≥ nextIndex for a follower: send AppendEntries RPC with log
            \* entries starting at nextIndex"
            append_entries:
            AppendEntries(pid, cmd, prevLogIndex, prevLogTerm);

            \* assert Len(msgs[2]) = 2;
        };
    };

    \* voter process.
    fair process (v \in Voters)
    variables
        pid = self - N,
        req = {};
    {
        voter_loop:
        while (currentTerm[pid]+1 <= T) {
            await
                LET
                    \* "Reply false if term < currentTerm"
                    Votes == ToSet(votes[currentTerm[pid]+1])
                IN
                    \* "candidate’s log is at least as up-to-date as receiver’s log, grant vote"
                    /\ \E v \in Votes: v.src /= pid /\ UpToDate(v.src, pid)
                    \* "If votedFor is null or candidateId"
                    /\ ~\E v \in Votes: v.src = pid;

            req := Head(SelectSeq(votes[currentTerm[pid]+1], LAMBDA v: UpToDate(v.src, pid)));
            votes[currentTerm[pid]+1] := Append(votes[currentTerm[pid]+1], [
                src         |-> pid,
                candidateId |-> req.candidateId
            ]);
        };
    };

    \* follower process.
    fair process (f \in Followers)
    variables
        pid = self - N*2,
        req = {};
    {
        follower_loop:
        while (currentTerm[pid]+1 <= T) {
            \* wait for a new AppendEntries message to arrive.
            follower_recv_msg:
            await Len(msgs[pid]) > 0;

            req       := Head(msgs[pid]);
            msgs[pid] := Tail(msgs[pid]);

            either {
                \* "If RPC request or response contains term T > currentTerm: set currentTerm = T, convert to follower"
                if (req.src /= pid /\ req.term >= currentTerm[pid]) {
                    states[pid]      := "follower";
                    currentTerm[pid] := req.term;
                };

                \* "Reply false if log doesn’t contain an entry at prevLogIndex whose term matches prevLogTerm"
                if (req.prevLogIndex = 0 \/ (req.prevLogIndex <= Len(logs[pid]) /\ req.prevLogTerm = logs[pid][req.prevLogIndex].term)) {
                    \* "If an existing entry conflicts with a new one (same index but different terms),
                    \* delete the existing entry and all that follow it"
                    if (req.prevLogIndex + 1 <= Len(logs[pid]) /\ logs[pid][req.prevLogIndex+1].term /= req.term) {
                        logs[pid] := SubSeq(logs[pid], 1, req.prevLogIndex);
                    };

                    if (req.cmd >= 0) { \* -1 for heartbeat.
                        follower_append_log:
                        logs[pid] := Append(logs[pid], [
                            term |-> req.term,
                            cmd  |-> req.cmd
                        ]);
                    };
                };

                follower_clear_dropped_msg:
                electionTimeout[pid] := FALSE;
            } or {
                electionTimeout[pid] := TRUE;
            };
        };
    };
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "4f58c9d2" /\ chksum(tla) = "e8275f13")
\* Process variable pid of process l at line 149 col 9 changed to pid_
\* Process variable pid of process v at line 194 col 9 changed to pid_v
\* Process variable req of process v at line 195 col 9 changed to req_
VARIABLES states, currentTerm, electionTimeout, votes, msgs, logs, pc

(* define statement *)
Leaders   == 1     .. N
Voters    == N+1   .. N*2
Followers == N*2+1 .. N*3

ToSet(seq)  == {seq[i]: i \in 1..Len(seq)}
MaxInSet(S) == CHOOSE x \in S : \A y \in S : y <= x
MinInSet(S) == CHOOSE x \in S : \A y \in S : x =< y


MatchingPrefix(l1, l2) ==
    LET
        Min(a, b)       == IF a < b THEN a ELSE b
        MinLen          == Min(Len(logs[l1]), Len(logs[l2]))
        MatchingUpTo(j) == {i \in 1..j: logs[l1][i].term = logs[l2][i].term /\ logs[l1][i].cmd = logs[l2][i].cmd}
        MaxMatching     == MaxInSet(MatchingUpTo(MinLen))
    IN
        IF MinLen = 0 THEN TRUE ELSE MatchingUpTo(MaxMatching) = 1..MaxMatching





UpToDate(l1, l2) ==
    IF   Len(logs[l2]) = 0
    THEN TRUE
    ELSE Len(logs[l1]) > 0 /\
        (logs[l1][Len(logs[l1])].term > logs[l2][Len(logs[l2])].term \/
        (logs[l1][Len(logs[l1])].term = logs[l2][Len(logs[l2])].term /\ Len(logs[l1]) >= Len(logs[l2])))


ElectionSafety ==
    \A a \in {l \in Leaders : states[l] = "leader"}:
        \A b \in Leaders \ {a}: states[b] /= "leader" \/ currentTerm[a] /= currentTerm[b]


LeaderAppendOnly ==
    [][
        \A l \in {l \in Leaders: states[l] = "leader"}:
            \A i \in 1..Len(logs[l]): logs'[l][i].cmd = logs[l][i].cmd /\ logs'[l][i].term = logs[l][i].term
    ]_logs




LogMatching ==
    \A a, b \in Leaders:
        (a # b) => MatchingPrefix(a, b)




LeaderCompleteness ==
    \A a \in Leaders:
        \A b \in {l \in Leaders : currentTerm[l] > currentTerm[a] /\ states[l] = "leader"}:
            \A i \in 1..Len(logs[a]):
                \E j \in 1..Len(logs[b]): logs[i].cmd = logs[j].cmd



StateMachineSafety ==
    \A a, b \in Leaders:
        (a # b) => \A i \in 1..Len(logs[a]): i > Len(logs[b]) \/ logs[a][i].cmd = logs[b][i].cmd

VARIABLES pid_, cmd, prevLogIndex, prevLogTerm, pid_v, req_, pid, req

vars == << states, currentTerm, electionTimeout, votes, msgs, logs, pc, pid_, 
           cmd, prevLogIndex, prevLogTerm, pid_v, req_, pid, req >>

ProcSet == (Leaders) \cup (Voters) \cup (Followers)

Init == (* Global variables *)
        /\ states = [l \in Leaders |-> "follower"]
        /\ currentTerm = [l \in Leaders |-> 1]
        /\ electionTimeout = [l \in Leaders |-> TRUE]
        /\ votes = [t \in 1..T+1 |-> << >>]
        /\ msgs = [l \in Leaders |-> << >>]
        /\ logs = [l \in Leaders |-> << >>]
        (* Process l *)
        /\ pid_ = [self \in Leaders |-> self]
        /\ cmd = [self \in Leaders |-> 0]
        /\ prevLogIndex = [self \in Leaders |-> 0]
        /\ prevLogTerm = [self \in Leaders |-> 0]
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
                     /\ IF currentTerm[pid_[self]]+1 <= T /\ cmd[self] < E
                           THEN /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                     votes, msgs, logs, pid_, cmd, 
                                     prevLogIndex, prevLogTerm, pid_v, req_, 
                                     pid, req >>

leader_election(self) == /\ pc[self] = "leader_election"
                         /\ IF states[pid_[self]] /= "leader"
                               THEN /\ pc' = [pc EXCEPT ![self] = "request_vote"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "heartbeat"]
                         /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                         votes, msgs, logs, pid_, cmd, 
                                         prevLogIndex, prevLogTerm, pid_v, 
                                         req_, pid, req >>

request_vote(self) == /\ pc[self] = "request_vote"
                      /\ electionTimeout[pid_[self]] /\ Len(SelectSeq(votes[currentTerm[pid_[self]]+1], LAMBDA v: v.src = pid_[self])) = 0
                      /\ states' = [states EXCEPT ![pid_[self]] = "candidate"]
                      /\ currentTerm' = [currentTerm EXCEPT ![pid_[self]] = currentTerm[pid_[self]]+1]
                      /\ votes' = [votes EXCEPT ![currentTerm'[pid_[self]]] =                            Append(votes[currentTerm'[pid_[self]]], [
                                                                                  src          |-> pid_[self],
                                                                                  candidateId  |-> pid_[self]
                                                                              ])]
                      /\ electionTimeout' = [electionTimeout EXCEPT ![pid_[self]] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "check_votes"]
                      /\ UNCHANGED << msgs, logs, pid_, cmd, prevLogIndex, 
                                      prevLogTerm, pid_v, req_, pid, req >>

check_votes(self) == /\ pc[self] = "check_votes"
                     /\ \/ Len(SelectSeq(votes[currentTerm[pid_[self]]], LAMBDA v: v.candidateId = pid_[self])) >= M
                        \/ states[pid_[self]] /= "candidate"
                     /\ IF states[pid_[self]] = "candidate" /\ Len(SelectSeq(votes[currentTerm[pid_[self]]], LAMBDA v: v.candidateId = pid_[self])) >= M
                           THEN /\ states' = [states EXCEPT ![pid_[self]] = "leader"]
                           ELSE /\ TRUE
                                /\ UNCHANGED states
                     /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                     /\ UNCHANGED << currentTerm, electionTimeout, votes, msgs, 
                                     logs, pid_, cmd, prevLogIndex, 
                                     prevLogTerm, pid_v, req_, pid, req >>

heartbeat(self) == /\ pc[self] = "heartbeat"
                   /\ msgs' =         [l \in Leaders |->
                                  IF   l = pid_[self]
                                  THEN msgs[l]
                                  ELSE Append(msgs[l], [
                                      src          |-> pid_[self],
                                      term         |-> currentTerm[pid_[self]],
                                      prevLogIndex |-> (E+1),
                                      prevLogTerm  |-> (E+1),
                                      cmd          |-> (-1)
                                  ])
                              ]
                   /\ cmd' = [cmd EXCEPT ![self] = IF Len(logs[pid_[self]]) > 0 THEN logs[pid_[self]][Len(logs[pid_[self]])].cmd + 1 ELSE 1]
                   /\ prevLogIndex' = [prevLogIndex EXCEPT ![self] = Len(logs[pid_[self]])]
                   /\ prevLogTerm' = [prevLogTerm EXCEPT ![self] = IF Len(logs[pid_[self]]) > 0 THEN logs[pid_[self]][Len(logs[pid_[self]])].term ELSE 0]
                   /\ logs' = [logs EXCEPT ![pid_[self]] =              Append(logs[pid_[self]], [
                                                               term |-> currentTerm[pid_[self]],
                                                               cmd  |-> cmd'[self]
                                                           ])]
                   /\ pc' = [pc EXCEPT ![self] = "append_entries"]
                   /\ UNCHANGED << states, currentTerm, electionTimeout, votes, 
                                   pid_, pid_v, req_, pid, req >>

append_entries(self) == /\ pc[self] = "append_entries"
                        /\ msgs' =         [l \in Leaders |->
                                       IF   l = pid_[self]
                                       THEN msgs[l]
                                       ELSE Append(msgs[l], [
                                           src          |-> pid_[self],
                                           term         |-> currentTerm[pid_[self]],
                                           prevLogIndex |-> prevLogIndex[self],
                                           prevLogTerm  |-> prevLogTerm[self],
                                           cmd          |-> cmd[self]
                                       ])
                                   ]
                        /\ pc' = [pc EXCEPT ![self] = "leader_loop"]
                        /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                        votes, logs, pid_, cmd, prevLogIndex, 
                                        prevLogTerm, pid_v, req_, pid, req >>

l(self) == leader_loop(self) \/ leader_election(self) \/ request_vote(self)
              \/ check_votes(self) \/ heartbeat(self)
              \/ append_entries(self)

voter_loop(self) == /\ pc[self] = "voter_loop"
                    /\ IF currentTerm[pid_v[self]]+1 <= T
                          THEN /\ LET
                                  
                                      Votes == ToSet(votes[currentTerm[pid_v[self]]+1])
                                  IN
                                  
                                      /\ \E v \in Votes: v.src /= pid_v[self] /\ UpToDate(v.src, pid_v[self])
                                  
                                      /\ ~\E v \in Votes: v.src = pid_v[self]
                               /\ req_' = [req_ EXCEPT ![self] = Head(SelectSeq(votes[currentTerm[pid_v[self]]+1], LAMBDA v: UpToDate(v.src, pid_v[self])))]
                               /\ votes' = [votes EXCEPT ![currentTerm[pid_v[self]]+1] =                              Append(votes[currentTerm[pid_v[self]]+1], [
                                                                                             src         |-> pid_v[self],
                                                                                             candidateId |-> req_'[self].candidateId
                                                                                         ])]
                               /\ pc' = [pc EXCEPT ![self] = "voter_loop"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << votes, req_ >>
                    /\ UNCHANGED << states, currentTerm, electionTimeout, msgs, 
                                    logs, pid_, cmd, prevLogIndex, prevLogTerm, 
                                    pid_v, pid, req >>

v(self) == voter_loop(self)

follower_loop(self) == /\ pc[self] = "follower_loop"
                       /\ IF currentTerm[pid[self]]+1 <= T
                             THEN /\ pc' = [pc EXCEPT ![self] = "follower_recv_msg"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                       votes, msgs, logs, pid_, cmd, 
                                       prevLogIndex, prevLogTerm, pid_v, req_, 
                                       pid, req >>

follower_recv_msg(self) == /\ pc[self] = "follower_recv_msg"
                           /\ Len(msgs[pid[self]]) > 0
                           /\ req' = [req EXCEPT ![self] = Head(msgs[pid[self]])]
                           /\ msgs' = [msgs EXCEPT ![pid[self]] = Tail(msgs[pid[self]])]
                           /\ \/ /\ IF req'[self].src /= pid[self] /\ req'[self].term >= currentTerm[pid[self]]
                                       THEN /\ states' = [states EXCEPT ![pid[self]] = "follower"]
                                            /\ currentTerm' = [currentTerm EXCEPT ![pid[self]] = req'[self].term]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << states, 
                                                            currentTerm >>
                                 /\ IF req'[self].prevLogIndex = 0 \/ (req'[self].prevLogIndex <= Len(logs[pid[self]]) /\ req'[self].prevLogTerm = logs[pid[self]][req'[self].prevLogIndex].term)
                                       THEN /\ IF req'[self].prevLogIndex + 1 <= Len(logs[pid[self]]) /\ logs[pid[self]][req'[self].prevLogIndex+1].term /= req'[self].term
                                                  THEN /\ logs' = [logs EXCEPT ![pid[self]] = SubSeq(logs[pid[self]], 1, req'[self].prevLogIndex)]
                                                  ELSE /\ TRUE
                                                       /\ logs' = logs
                                            /\ IF req'[self].cmd >= 0
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "follower_append_log"]
                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "follower_clear_dropped_msg"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "follower_clear_dropped_msg"]
                                            /\ logs' = logs
                                 /\ UNCHANGED electionTimeout
                              \/ /\ electionTimeout' = [electionTimeout EXCEPT ![pid[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                                 /\ UNCHANGED <<states, currentTerm, logs>>
                           /\ UNCHANGED << votes, pid_, cmd, prevLogIndex, 
                                           prevLogTerm, pid_v, req_, pid >>

follower_append_log(self) == /\ pc[self] = "follower_append_log"
                             /\ logs' = [logs EXCEPT ![pid[self]] =              Append(logs[pid[self]], [
                                                                        term |-> req[self].term,
                                                                        cmd  |-> req[self].cmd
                                                                    ])]
                             /\ pc' = [pc EXCEPT ![self] = "follower_clear_dropped_msg"]
                             /\ UNCHANGED << states, currentTerm, 
                                             electionTimeout, votes, msgs, 
                                             pid_, cmd, prevLogIndex, 
                                             prevLogTerm, pid_v, req_, pid, 
                                             req >>

follower_clear_dropped_msg(self) == /\ pc[self] = "follower_clear_dropped_msg"
                                    /\ electionTimeout' = [electionTimeout EXCEPT ![pid[self]] = FALSE]
                                    /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                                    /\ UNCHANGED << states, currentTerm, votes, 
                                                    msgs, logs, pid_, cmd, 
                                                    prevLogIndex, prevLogTerm, 
                                                    pid_v, req_, pid, req >>

f(self) == follower_loop(self) \/ follower_recv_msg(self)
              \/ follower_append_log(self)
              \/ follower_clear_dropped_msg(self)

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
