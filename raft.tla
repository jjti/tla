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
        currentTerm = [l \in Leaders |-> 0],

        \* whether the last heartbeat was dropped.
        electionTimeout = [l \in Leaders |-> TRUE],

        \* votes for each term. key is the term of voting, value is the pid of the Voter.
        votes = [t \in 1..T |-> << >>],

        \* "candidateId that received vote in current term". Mapping from term to voter to whether it voted.
        voted = [t \in 1..T |-> [l \in Leaders |-> FALSE]],

        \* leaders send followers messages via AppendEntries.
        msgs = [l \in Leaders |-> << >>],

        \* "log entries; each entry contains command for state machine,
        \* and term when entry was received by leader (first index is 1)".
        logs = [l \in Leaders |-> << >>];

    define {
        Leaders   == 1     .. N
        Voters    == N+1   .. N*2
        Followers == N*2+1 .. N*3

        \** HELPERS **\

        ToSet(S)    == {S[i]: i \in 1..Len(S)}
        MaxInSet(S) == CHOOSE x \in S : \A y \in S : y <= x

        \* whether the candidate sending a vote (RPC) is as or more up-to-date than this voter (pid).
        \* "Raft determines which of two logs is more up-to-date by comparing the index and term of the last entries in the
        \* logs. If the logs have last entries with different terms, then the log with the later term is more up-to-date. If the logs
        \* end with the same term, then whichever log is longer is more up-to-date."
        UpToDate(pid, vote) ==
            LET
                HasLogs == Len(logs[pid]) > 0
                LastLog == IF HasLogs THEN logs[pid][Len(logs[pid])] ELSE [term |-> 0]
            IN
                \/ ~HasLogs
                \/ LastLog.term > vote.lastLogTerm
                \/ Len(logs[pid]) <= vote.lastLogIndex


        \** PROPERTIES **\

        \* "a leader never overwrites or deletes entries in its log; it only appends new entries."
        LeaderAppendOnly ==
            [][
                [
                    \A l \in {l \in Leaders: states'[l] = "leader"}:
                        \A i \in 1..Len(logs[l]): logs'[l][i].cmd = logs[l][i].cmd /\ logs'[l][i].term = logs[l][i].term
                ]_states
            ]_logs


        \** INVARIANTS **\

        \* "at most one leader can be elected in a given term."
        ElectionSafety == 
            \A a, b \in Leaders: (a # b) =>
                states[a] /= "leader" \/ states[b] /= "leader" \/ currentTerm[a] /= currentTerm[b]

        \* "if two logs contain an entry with the same index and term, then the logs are identical in
        \* all entries up through the given index."
        LogMatching ==
            \A a, b \in Leaders: (a # b) =>
                LET
                    MaxMatchingIndex == MaxInSet({i \in 1..Len(logs[a]): i <= Len(logs[b]) /\ logs[a][i].term = logs[b][i].term} \union {0})
                IN
                    \* "If two entries in different logs have the same index and term, then they store the same command."
                    \A i \in 1..MaxMatchingIndex: logs[a][i].cmd = logs[b][i].cmd

        \* "if a log entry is committed in a given term, then that entry will be present in the logs
        \* of the leaders for all higher-numbered terms."
        \* just going to check this with: servers with higher terms have all the logs of servers with lower terms
        LeaderCompleteness ==
            \A a \in Leaders:
                \A b \in {l \in Leaders : currentTerm[l] > currentTerm[a] /\ states[l] = "leader"}:
                    \A i \in {i \in 1..Len(logs[a]): logs[a][i].committed}:
                        \E j \in 1..Len(logs[b]): logs[i].cmd = logs[j].cmd

        \* "if a server has applied a log entry at a given index to its state machine, no other server
        \* will ever apply a different log entry for the same index"
        StateMachineSafety ==
            \A a, b \in Leaders: (a # b) =>
                \A i \in {i \in 1..Len(logs[a]): i <= Len(logs[b])}:
                    (logs[a][i].committed /\ logs[b][i].committed) => logs[a][i].cmd = logs[b][i].cmd
    }

    \* "Invoked by candidates to gather votes"
    macro RequestVote(pid) {
        \* "If election timeout elapses without receiving AppendEntries RPC from current leader or
        \* granting vote to candidate: convert to candidate"
        \* "Each server will vote for at most one candidate in a given term, on a first-come-first-served basis"
        await electionTimeout[pid] /\ currentTerm[pid] < T /\ ~voted[currentTerm[pid]+1][pid];

        \* "Send RequestVote RPCs to all other servers"
        states[pid]             := "candidate";        \* "conversion to candidate"
        currentTerm[pid]        := currentTerm[pid]+1; \* "Increment currentTerm"
        votes[currentTerm[pid]] := Append(votes[currentTerm[pid]], [
            candidateId  |-> pid,
            lastLogIndex |-> Len(logs[pid]),   \* "index of candidate’s last log entry"
            lastLogTerm  |-> IF Len(logs[pid]) > 0 THEN logs[pid][Len(logs[pid])].term ELSE 0
        ]);
        voted[currentTerm[pid]][pid] := TRUE;
        electionTimeout[pid]         := FALSE;
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
        while (currentTerm[pid] < T /\ cmd < E) {
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
            AppendEntries(pid, -1, E+1, E+1);

            \* Send entries from the point of the max entry we have seen.
            cmd          := IF Len(logs[pid]) > 0 THEN logs[pid][Len(logs[pid])].cmd + 1 ELSE 1;
            prevLogIndex := Len(logs[pid]);
            prevLogTerm  := IF Len(logs[pid]) > 0 THEN logs[pid][Len(logs[pid])].term ELSE 0;
            logs[pid]    := Append(logs[pid], [ \* "If command received from client: append entry to local log"
                term      |-> currentTerm[pid],
                cmd       |-> cmd,
                committed |-> FALSE
            ]);

            \* "If last log index ≥ nextIndex for a follower: send AppendEntries RPC with log
            \* entries starting at nextIndex"
            append_entries:
            AppendEntries(pid, cmd, prevLogIndex, prevLogTerm);
        };
    };

    \* voter process. This is only for voting for other candidates, not self.
    fair process (v \in Voters)
    variables
        pid      = self - N,
        voteReq  = {};
    {
        voter_loop:
        with (t \in 1..T) { \* "If votedFor is null or candidateId" (check we did not already vote).
            await
                LET
                    Votes == ToSet(votes[t])
                IN
                    \* "Reply false if term < currentTerm"
                    /\ t >= currentTerm[pid]
                    /\ ~voted[t][pid]
                    \* "candidate’s log is at least as up-to-date as receiver’s log, grant vote"
                    /\ \E v \in Votes: UpToDate(pid, v);

            voteReq  := Head(SelectSeq(votes[t], LAMBDA v: UpToDate(pid, v)));
            votes[t] := Append(votes[t], [
                candidateId  |-> voteReq.candidateId,
                lastLogTerm  |-> voteReq.lastLogTerm,
                lastLogIndex |-> voteReq.lastLogIndex
            ]);
            voted[t][pid] := TRUE;
        };
    };

    \* follower process.
    fair process (f \in Followers)
    variables
        pid = self - N*2,
        msg = {};
    {
        follower_loop:
        while (TRUE) {
            \* wait for a new AppendEntries message to arrive.
            follower_recv_msg:
            await Len(msgs[pid]) > 0;

            msg       := Head(msgs[pid]);
            msgs[pid] := Tail(msgs[pid]);

            \* "Reply false if term < currentTerm".
            if (msg.term >= currentTerm[pid]) {
                either {
                    \* "If the leader’s term (included in its RPC) is at least
                    \* as large as the candidate’s current term, then the candidate
                    \* recognizes the leader as legitimate and returns to follower
                    \* state."
                    states[pid]          := "follower";
                    currentTerm[pid]     := msg.term;
                    electionTimeout[pid] := FALSE;

                    \* ignore heartbeats.
                    if (msg.cmd >= 0) {
                        \* "Reply false if log doesn’t contain an entry at prevLogIndex whose term matches prevLogTerm"
                        if ((msg.prevLogIndex = 0 /\ Len(logs[pid]) = 0) \/
                            (msg.prevLogIndex > 0 /\ msg.prevLogIndex <= Len(logs[pid]) /\ msg.prevLogTerm = logs[pid][msg.prevLogIndex].term)) {
                            \* "If an existing entry conflicts with a new one (same index but different terms),
                            \* delete the existing entry and all that follow it"
                            if (msg.prevLogIndex+1 <= Len(logs[pid]) /\ logs[pid][msg.prevLogIndex+1].term /= msg.term) {
                                logs[pid] := Append(
                                    SubSeq(logs[pid], 1, msg.prevLogIndex),
                                    [
                                        term      |-> msg.term,
                                        cmd       |-> msg.cmd,
                                        committed |-> FALSE
                                    ]
                                );
                            } else {
                                logs[pid] := Append(logs[pid], [
                                    term      |-> msg.term,
                                    cmd       |-> msg.cmd,
                                    committed |-> FALSE
                                ]);
                            };
                        };
                    };
                } or {
                    \* fake a dropped heartbeat/msg.
                    electionTimeout[pid] := TRUE;
                };
            };
        };
    };
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2a8837b6" /\ chksum(tla) = "4eaed4eb")
\* Process variable pid of process l at line 159 col 9 changed to pid_
\* Process variable pid of process v at line 200 col 9 changed to pid_v
VARIABLES states, currentTerm, electionTimeout, votes, voted, msgs, logs, pc

(* define statement *)
Leaders   == 1     .. N
Voters    == N+1   .. N*2
Followers == N*2+1 .. N*3



ToSet(S)    == {S[i]: i \in 1..Len(S)}
MaxInSet(S) == CHOOSE x \in S : \A y \in S : y <= x





UpToDate(pid, vote) ==
    LET
        HasLogs == Len(logs[pid]) > 0
        LastLog == IF HasLogs THEN logs[pid][Len(logs[pid])] ELSE [term |-> 0]
    IN
        \/ ~HasLogs
        \/ LastLog.term > vote.lastLogTerm
        \/ Len(logs[pid]) <= vote.lastLogIndex





LeaderAppendOnly ==
    [][
        [
            \A l \in {l \in Leaders: states'[l] = "leader"}:
                \A i \in 1..Len(logs[l]): logs'[l][i].cmd = logs[l][i].cmd /\ logs'[l][i].term = logs[l][i].term
        ]_states
    ]_logs





ElectionSafety ==
    \A a, b \in Leaders: (a # b) =>
        states[a] /= "leader" \/ states[b] /= "leader" \/ currentTerm[a] /= currentTerm[b]



LogMatching ==
    \A a, b \in Leaders: (a # b) =>
        LET
            MaxMatchingIndex == MaxInSet({i \in 1..Len(logs[a]): i <= Len(logs[b]) /\ logs[a][i].term = logs[b][i].term} \union {0})
        IN

            \A i \in 1..MaxMatchingIndex: logs[a][i].cmd = logs[b][i].cmd




LeaderCompleteness ==
    \A a \in Leaders:
        \A b \in {l \in Leaders : currentTerm[l] > currentTerm[a] /\ states[l] = "leader"}:
            \A i \in {i \in 1..Len(logs[a]): logs[a][i].committed}:
                \E j \in 1..Len(logs[b]): logs[i].cmd = logs[j].cmd



StateMachineSafety ==
    \A a, b \in Leaders: (a # b) =>
        \A i \in {i \in 1..Len(logs[a]): i <= Len(logs[b])}:
            (logs[a][i].committed /\ logs[b][i].committed) => logs[a][i].cmd = logs[b][i].cmd

VARIABLES pid_, cmd, prevLogIndex, prevLogTerm, pid_v, voteReq, pid, msg

vars == << states, currentTerm, electionTimeout, votes, voted, msgs, logs, pc, 
           pid_, cmd, prevLogIndex, prevLogTerm, pid_v, voteReq, pid, msg >>

ProcSet == (Leaders) \cup (Voters) \cup (Followers)

Init == (* Global variables *)
        /\ states = [l \in Leaders |-> "follower"]
        /\ currentTerm = [l \in Leaders |-> 0]
        /\ electionTimeout = [l \in Leaders |-> TRUE]
        /\ votes = [t \in 1..T |-> << >>]
        /\ voted = [t \in 1..T |-> [l \in Leaders |-> FALSE]]
        /\ msgs = [l \in Leaders |-> << >>]
        /\ logs = [l \in Leaders |-> << >>]
        (* Process l *)
        /\ pid_ = [self \in Leaders |-> self]
        /\ cmd = [self \in Leaders |-> 0]
        /\ prevLogIndex = [self \in Leaders |-> 0]
        /\ prevLogTerm = [self \in Leaders |-> 0]
        (* Process v *)
        /\ pid_v = [self \in Voters |-> self - N]
        /\ voteReq = [self \in Voters |-> {}]
        (* Process f *)
        /\ pid = [self \in Followers |-> self - N*2]
        /\ msg = [self \in Followers |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Leaders -> "leader_loop"
                                        [] self \in Voters -> "voter_loop"
                                        [] self \in Followers -> "follower_loop"]

leader_loop(self) == /\ pc[self] = "leader_loop"
                     /\ IF currentTerm[pid_[self]] < T /\ cmd[self] < E
                           THEN /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                     votes, voted, msgs, logs, pid_, cmd, 
                                     prevLogIndex, prevLogTerm, pid_v, voteReq, 
                                     pid, msg >>

leader_election(self) == /\ pc[self] = "leader_election"
                         /\ IF states[pid_[self]] /= "leader"
                               THEN /\ pc' = [pc EXCEPT ![self] = "request_vote"]
                                    /\ UNCHANGED << msgs, logs, cmd, 
                                                    prevLogIndex, prevLogTerm >>
                               ELSE /\ msgs' =         [l \in Leaders |->
                                                   IF   l = pid_[self]
                                                   THEN msgs[l]
                                                   ELSE Append(msgs[l], [
                                                       term         |-> currentTerm[pid_[self]],
                                                       prevLogIndex |-> (E+1),
                                                       prevLogTerm  |-> (E+1),
                                                       cmd          |-> (-1)
                                                   ])
                                               ]
                                    /\ cmd' = [cmd EXCEPT ![self] = IF Len(logs[pid_[self]]) > 0 THEN logs[pid_[self]][Len(logs[pid_[self]])].cmd + 1 ELSE 1]
                                    /\ prevLogIndex' = [prevLogIndex EXCEPT ![self] = Len(logs[pid_[self]])]
                                    /\ prevLogTerm' = [prevLogTerm EXCEPT ![self] = IF Len(logs[pid_[self]]) > 0 THEN logs[pid_[self]][Len(logs[pid_[self]])].term ELSE 0]
                                    /\ logs' = [logs EXCEPT ![pid_[self]] =                 Append(logs[pid_[self]], [
                                                                                term      |-> currentTerm[pid_[self]],
                                                                                cmd       |-> cmd'[self],
                                                                                committed |-> FALSE
                                                                            ])]
                                    /\ pc' = [pc EXCEPT ![self] = "append_entries"]
                         /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                         votes, voted, pid_, pid_v, voteReq, 
                                         pid, msg >>

request_vote(self) == /\ pc[self] = "request_vote"
                      /\ electionTimeout[pid_[self]] /\ currentTerm[pid_[self]] < T /\ ~voted[currentTerm[pid_[self]]+1][pid_[self]]
                      /\ states' = [states EXCEPT ![pid_[self]] = "candidate"]
                      /\ currentTerm' = [currentTerm EXCEPT ![pid_[self]] = currentTerm[pid_[self]]+1]
                      /\ votes' = [votes EXCEPT ![currentTerm'[pid_[self]]] =                            Append(votes[currentTerm'[pid_[self]]], [
                                                                                  candidateId  |-> pid_[self],
                                                                                  lastLogIndex |-> Len(logs[pid_[self]]),
                                                                                  lastLogTerm  |-> IF Len(logs[pid_[self]]) > 0 THEN logs[pid_[self]][Len(logs[pid_[self]])].term ELSE 0
                                                                              ])]
                      /\ voted' = [voted EXCEPT ![currentTerm'[pid_[self]]][pid_[self]] = TRUE]
                      /\ electionTimeout' = [electionTimeout EXCEPT ![pid_[self]] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "check_votes"]
                      /\ UNCHANGED << msgs, logs, pid_, cmd, prevLogIndex, 
                                      prevLogTerm, pid_v, voteReq, pid, msg >>

check_votes(self) == /\ pc[self] = "check_votes"
                     /\ \/ Len(SelectSeq(votes[currentTerm[pid_[self]]], LAMBDA v: v.candidateId = pid_[self])) >= M
                        \/ states[pid_[self]] /= "candidate"
                     /\ IF states[pid_[self]] = "candidate" /\ Len(SelectSeq(votes[currentTerm[pid_[self]]], LAMBDA v: v.candidateId = pid_[self])) >= M
                           THEN /\ states' = [states EXCEPT ![pid_[self]] = "leader"]
                           ELSE /\ TRUE
                                /\ UNCHANGED states
                     /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                     /\ UNCHANGED << currentTerm, electionTimeout, votes, 
                                     voted, msgs, logs, pid_, cmd, 
                                     prevLogIndex, prevLogTerm, pid_v, voteReq, 
                                     pid, msg >>

append_entries(self) == /\ pc[self] = "append_entries"
                        /\ msgs' =         [l \in Leaders |->
                                       IF   l = pid_[self]
                                       THEN msgs[l]
                                       ELSE Append(msgs[l], [
                                           term         |-> currentTerm[pid_[self]],
                                           prevLogIndex |-> prevLogIndex[self],
                                           prevLogTerm  |-> prevLogTerm[self],
                                           cmd          |-> cmd[self]
                                       ])
                                   ]
                        /\ pc' = [pc EXCEPT ![self] = "leader_loop"]
                        /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                        votes, voted, logs, pid_, cmd, 
                                        prevLogIndex, prevLogTerm, pid_v, 
                                        voteReq, pid, msg >>

l(self) == leader_loop(self) \/ leader_election(self) \/ request_vote(self)
              \/ check_votes(self) \/ append_entries(self)

voter_loop(self) == /\ pc[self] = "voter_loop"
                    /\ \E t \in 1..T:
                         /\ LET
                                Votes == ToSet(votes[t])
                            IN
                            
                                /\ t >= currentTerm[pid_v[self]]
                                /\ ~voted[t][pid_v[self]]
                            
                                /\ \E v \in Votes: UpToDate(pid_v[self], v)
                         /\ voteReq' = [voteReq EXCEPT ![self] = Head(SelectSeq(votes[t], LAMBDA v: UpToDate(pid_v[self], v)))]
                         /\ votes' = [votes EXCEPT ![t] =             Append(votes[t], [
                                                              candidateId  |-> voteReq'[self].candidateId,
                                                              lastLogTerm  |-> voteReq'[self].lastLogTerm,
                                                              lastLogIndex |-> voteReq'[self].lastLogIndex
                                                          ])]
                         /\ voted' = [voted EXCEPT ![t][pid_v[self]] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << states, currentTerm, electionTimeout, msgs, 
                                    logs, pid_, cmd, prevLogIndex, prevLogTerm, 
                                    pid_v, pid, msg >>

v(self) == voter_loop(self)

follower_loop(self) == /\ pc[self] = "follower_loop"
                       /\ pc' = [pc EXCEPT ![self] = "follower_recv_msg"]
                       /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                       votes, voted, msgs, logs, pid_, cmd, 
                                       prevLogIndex, prevLogTerm, pid_v, 
                                       voteReq, pid, msg >>

follower_recv_msg(self) == /\ pc[self] = "follower_recv_msg"
                           /\ Len(msgs[pid[self]]) > 0
                           /\ msg' = [msg EXCEPT ![self] = Head(msgs[pid[self]])]
                           /\ msgs' = [msgs EXCEPT ![pid[self]] = Tail(msgs[pid[self]])]
                           /\ IF msg'[self].term >= currentTerm[pid[self]]
                                 THEN /\ \/ /\ states' = [states EXCEPT ![pid[self]] = "follower"]
                                            /\ currentTerm' = [currentTerm EXCEPT ![pid[self]] = msg'[self].term]
                                            /\ electionTimeout' = [electionTimeout EXCEPT ![pid[self]] = FALSE]
                                            /\ IF msg'[self].cmd >= 0
                                                  THEN /\ IF (msg'[self].prevLogIndex = 0 /\ Len(logs[pid[self]]) = 0) \/
                                                             (msg'[self].prevLogIndex > 0 /\ msg'[self].prevLogIndex <= Len(logs[pid[self]]) /\ msg'[self].prevLogTerm = logs[pid[self]][msg'[self].prevLogIndex].term)
                                                             THEN /\ IF msg'[self].prevLogIndex+1 <= Len(logs[pid[self]]) /\ logs[pid[self]][msg'[self].prevLogIndex+1].term /= msg'[self].term
                                                                        THEN /\ logs' = [logs EXCEPT ![pid[self]] =              Append(
                                                                                                                        SubSeq(logs[pid[self]], 1, msg'[self].prevLogIndex),
                                                                                                                        [
                                                                                                                            term      |-> msg'[self].term,
                                                                                                                            cmd       |-> msg'[self].cmd,
                                                                                                                            committed |-> FALSE
                                                                                                                        ]
                                                                                                                    )]
                                                                        ELSE /\ logs' = [logs EXCEPT ![pid[self]] =              Append(logs[pid[self]], [
                                                                                                                        term      |-> msg'[self].term,
                                                                                                                        cmd       |-> msg'[self].cmd,
                                                                                                                        committed |-> FALSE
                                                                                                                    ])]
                                                             ELSE /\ TRUE
                                                                  /\ logs' = logs
                                                  ELSE /\ TRUE
                                                       /\ logs' = logs
                                         \/ /\ electionTimeout' = [electionTimeout EXCEPT ![pid[self]] = TRUE]
                                            /\ UNCHANGED <<states, currentTerm, logs>>
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << states, currentTerm, 
                                                      electionTimeout, logs >>
                           /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                           /\ UNCHANGED << votes, voted, pid_, cmd, 
                                           prevLogIndex, prevLogTerm, pid_v, 
                                           voteReq, pid >>

f(self) == follower_loop(self) \/ follower_recv_msg(self)

Next == (\E self \in Leaders: l(self))
           \/ (\E self \in Voters: v(self))
           \/ (\E self \in Followers: f(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Leaders : WF_vars(l(self))
        /\ \A self \in Voters : WF_vars(v(self))
        /\ \A self \in Followers : WF_vars(f(self))

\* END TRANSLATION 


=======================
