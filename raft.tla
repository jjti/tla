---- MODULE raft -----

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    N, \* server count.
    M, \* count for a majority.
    T, \* term limit.
    E \* log entry count.

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
        electionTimeout = [l \in Leaders |-> l = 1],

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
                \/ LastLog.term < vote.lastLogTerm
                \/ Len(logs[pid]) <= vote.lastLogIndex

        \* send an AppendEntries request to followers.
        AppendEntries(msg) ==
            [l \in Leaders |->
                IF l = msg.src \/ \E i \in 1..Len(msgs[l]): msgs[l][i] = msg
                THEN msgs[l]
                ELSE Append(msgs[l], msg)
            ]

        \* append a log entry, commit logs up to the max index.
        AppendLog(ls, log, commitIndex) ==
            Append([i \in 1..Len(ls) |-> [
                src       |-> ls[i].src,
                term      |-> ls[i].term,
                cmd       |-> ls[i].cmd,
                committed |-> i <= commitIndex
            ]], log)


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
        LeaderCompleteness ==
            \A a \in Leaders:
                \A b \in {l \in Leaders: currentTerm[l] > currentTerm[a] /\ states[l] = "leader"}:
                    \A i \in {i \in 1..Len(logs[a]): logs[a][i].committed}:
                        \E j \in 1..Len(logs[b]): logs[a][i].cmd = logs[b][j].cmd

        \* "if a server has applied a log entry at a given index to its state machine, no other server
        \* will ever apply a different log entry for the same index"
        StateMachineSafety ==
            \A a, b \in Leaders: (a # b) =>
                \A i \in {i \in 1..Len(logs[a]): i <= Len(logs[b])}:
                    (logs[a][i].committed /\ logs[b][i].committed) => logs[a][i].cmd = logs[b][i].cmd

        \* check that at some point the entries are committed. E-1 because the commitIndex is sent in a request that follows
        \* the one where followers learn of a log entry.
        BaitInvariant ==
            ~\A l \in Leaders:
                \A i \in 1..E-1: Len(logs[l]) >= E /\ logs[l][i].committed /\ logs[l][i].cmd = i
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

    \* leader process.
    fair process (l \in Leaders)
    variables
        pid          = self,
        cmd          = 0, \* current client request index. Goes up to E.
        prevLogIndex = 0, \* "index of log entry immediately preceding new ones"
        prevLogTerm  = 0, 
        commitIndex  = 0; \* "index of highest log entry known to be committed"
    {
        leader_loop:
        while (currentTerm[pid] < T /\ states[pid] /= "shutdown") {
            leader_election:
            while (states[pid] /= "leader") {
                \* when heartbeat timer times out, start election as candidate.
                RequestVote(pid);

                \* check if this leader won.
                check_votes:
                CheckVotes(pid);
            };

            prevLogIndex := Len(logs[pid]);
            prevLogTerm  := IF prevLogIndex > 0 THEN logs[pid][prevLogIndex].term ELSE 0;
            cmd          := IF prevLogIndex > 0 THEN logs[pid][prevLogIndex].cmd + 1 ELSE 1;

            \* "A log entry is committed once the leader that created the entry has replicated it on a majority of
            \* the servers (e.g., entry 7 in Figure 6). This also commits all preceding entries in the leader’s log,
            \* including entries created by previous leaders."
            \* skipping the message received here and looking into their logs.
            commitIndex := MaxInSet({  \* get the max log entry
                i \in 1..prevLogIndex: \* of all those in this leader's log
                    Cardinality({      \* if the majority
                        l \in Leaders: \* of servers
                            /\ i <= Len(logs[l]) \* have it
                            /\ logs[l][i].src  = pid
                            /\ logs[l][i].cmd  = i
                            /\ logs[l][i].term = prevLogTerm
                    }) >= M
            } \union {0});

            \* commit all entries in the majority of followers, add new one. 
            logs[pid] := AppendLog(
                logs[pid],
                [
                    src       |-> pid,
                    term      |-> currentTerm[pid],
                    cmd       |-> cmd,
                    committed |-> FALSE
                ],
                commitIndex
            );

            \* send entry and commitIndex to followers.
            msgs := AppendEntries([
                src          |-> pid,
                cmd          |-> cmd,
                term         |-> currentTerm[pid],
                prevLogIndex |-> prevLogIndex,
                prevLogTerm  |-> prevLogTerm,
                commitIndex  |-> commitIndex
            ]);

            if (cmd > E) {
                \* Shutdown.
                states := [l \in Leaders |-> "shutdown"];
            };
        };
    };

    \* voter process. This is only for voting for other candidates, not self.
    fair process (v \in Voters)
    variables
        pid     = self - N,
        voteReq = {};
    {
        voter_loop:
        while (currentTerm[pid] < T /\ states[pid] /= "shutdown") {
            await
                LET
                    \* "Reply false if term < currentTerm"
                    Votes == ToSet(votes[currentTerm[pid]+1])
                IN
                    \* "If votedFor is null or candidateId" (check we did not already vote).
                    /\ ~voted[currentTerm[pid]+1][pid]
                    \* "candidate’s log is at least as up-to-date as receiver’s log, grant vote"
                    /\ \E v \in Votes: UpToDate(pid, v);

            voteReq  := Head(SelectSeq(votes[currentTerm[pid]+1], LAMBDA v: UpToDate(pid, v)));
            votes[currentTerm[pid]+1] := Append(votes[currentTerm[pid]+1], [
                candidateId  |-> voteReq.candidateId,
                lastLogTerm  |-> voteReq.lastLogTerm,
                lastLogIndex |-> voteReq.lastLogIndex
            ]);
            voted[currentTerm[pid]+1][pid] := TRUE;

            \* "Current terms are exchanged whenever servers communicate; if one server’s current
            \* term is smaller than the other’s, then it updates its current term to the larger value. "
            currentTerm[pid] := currentTerm[pid]+1;

            \* "If a candidate or leader discovers that its term is out of date, it immediately reverts to follower state"
            states[pid] := "follower";
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
            await Len(msgs[pid]) > 0;

            msg       := Head(msgs[pid]);
            msgs[pid] := Tail(msgs[pid]);

            \* "Reply false if term < currentTerm".
            if (msg.term >= currentTerm[pid] /\ states[pid] /= "shutdown") {
                either {
                    \* "If the leader’s term (included in its RPC) is at least
                    \* as large as the candidate’s current term, then the candidate
                    \* recognizes the leader as legitimate and returns to follower
                    \* state."
                    states[pid]          := "follower";
                    currentTerm[pid]     := msg.term;
                    electionTimeout[pid] := FALSE;

                    \* "Reply false if log doesn’t contain an entry at prevLogIndex whose term matches prevLogTerm"
                    if ((msg.prevLogIndex = 0 /\ Len(logs[pid]) = 0) \/
                        (msg.prevLogIndex > 0 /\ msg.prevLogIndex <= Len(logs[pid]) /\ msg.prevLogTerm = logs[pid][msg.prevLogIndex].term)) {
                        \* "If an existing entry conflicts with a new one (same index but different terms),
                        \* delete the existing entry and all that follow it"
                        if (msg.prevLogIndex+1 <= Len(logs[pid]) /\ logs[pid][msg.prevLogIndex+1].term /= msg.term) {
                            logs[pid] := AppendLog(
                                SubSeq(logs[pid], 1, msg.prevLogIndex),
                                [
                                    src       |-> msg.src,
                                    term      |-> msg.term,
                                    cmd       |-> msg.cmd,
                                    committed |-> FALSE
                                ],
                                msg.commitIndex
                            );
                        } else {
                            logs[pid] := AppendLog(
                                logs[pid],
                                [
                                    src       |-> msg.src,
                                    term      |-> msg.term,
                                    cmd       |-> msg.cmd,
                                    committed |-> FALSE
                                ],
                                msg.commitIndex
                            );
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
\* BEGIN TRANSLATION (chksum(pcal) = "e87437a7" /\ chksum(tla) = "e94ceb4e")
\* Process variable pid of process l at line 167 col 9 changed to pid_
\* Process variable pid of process v at line 236 col 9 changed to pid_v
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
        \/ LastLog.term < vote.lastLogTerm
        \/ Len(logs[pid]) <= vote.lastLogIndex


AppendEntries(msg) ==
    [l \in Leaders |->
        IF l = msg.src \/ \E i \in 1..Len(msgs[l]): msgs[l][i] = msg
        THEN msgs[l]
        ELSE Append(msgs[l], msg)
    ]


AppendLog(ls, log, commitIndex) ==
    Append([i \in 1..Len(ls) |-> [
        src       |-> ls[i].src,
        term      |-> ls[i].term,
        cmd       |-> ls[i].cmd,
        committed |-> i <= commitIndex
    ]], log)





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
        \A b \in {l \in Leaders: currentTerm[l] > currentTerm[a] /\ states[l] = "leader"}:
            \A i \in {i \in 1..Len(logs[a]): logs[a][i].committed}:
                \E j \in 1..Len(logs[b]): logs[a][i].cmd = logs[b][j].cmd



StateMachineSafety ==
    \A a, b \in Leaders: (a # b) =>
        \A i \in {i \in 1..Len(logs[a]): i <= Len(logs[b])}:
            (logs[a][i].committed /\ logs[b][i].committed) => logs[a][i].cmd = logs[b][i].cmd



BaitInvariant ==
    ~\A l \in Leaders:
        \A i \in 1..E-1: Len(logs[l]) >= E /\ logs[l][i].committed /\ logs[l][i].cmd = i

VARIABLES pid_, cmd, prevLogIndex, prevLogTerm, commitIndex, pid_v, voteReq, 
          pid, msg

vars == << states, currentTerm, electionTimeout, votes, voted, msgs, logs, pc, 
           pid_, cmd, prevLogIndex, prevLogTerm, commitIndex, pid_v, voteReq, 
           pid, msg >>

ProcSet == (Leaders) \cup (Voters) \cup (Followers)

Init == (* Global variables *)
        /\ states = [l \in Leaders |-> "follower"]
        /\ currentTerm = [l \in Leaders |-> 0]
        /\ electionTimeout = [l \in Leaders |-> l = 1]
        /\ votes = [t \in 1..T |-> << >>]
        /\ voted = [t \in 1..T |-> [l \in Leaders |-> FALSE]]
        /\ msgs = [l \in Leaders |-> << >>]
        /\ logs = [l \in Leaders |-> << >>]
        (* Process l *)
        /\ pid_ = [self \in Leaders |-> self]
        /\ cmd = [self \in Leaders |-> 0]
        /\ prevLogIndex = [self \in Leaders |-> 0]
        /\ prevLogTerm = [self \in Leaders |-> 0]
        /\ commitIndex = [self \in Leaders |-> 0]
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
                     /\ IF currentTerm[pid_[self]] < T /\ states[pid_[self]] /= "shutdown"
                           THEN /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << states, currentTerm, electionTimeout, 
                                     votes, voted, msgs, logs, pid_, cmd, 
                                     prevLogIndex, prevLogTerm, commitIndex, 
                                     pid_v, voteReq, pid, msg >>

leader_election(self) == /\ pc[self] = "leader_election"
                         /\ IF states[pid_[self]] /= "leader"
                               THEN /\ electionTimeout[pid_[self]] /\ currentTerm[pid_[self]] < T /\ ~voted[currentTerm[pid_[self]]+1][pid_[self]]
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
                                    /\ UNCHANGED << msgs, logs, cmd, 
                                                    prevLogIndex, prevLogTerm, 
                                                    commitIndex >>
                               ELSE /\ prevLogIndex' = [prevLogIndex EXCEPT ![self] = Len(logs[pid_[self]])]
                                    /\ prevLogTerm' = [prevLogTerm EXCEPT ![self] = IF prevLogIndex'[self] > 0 THEN logs[pid_[self]][prevLogIndex'[self]].term ELSE 0]
                                    /\ cmd' = [cmd EXCEPT ![self] = IF prevLogIndex'[self] > 0 THEN logs[pid_[self]][prevLogIndex'[self]].cmd + 1 ELSE 1]
                                    /\ commitIndex' = [commitIndex EXCEPT ![self] =                MaxInSet({
                                                                                        i \in 1..prevLogIndex'[self]:
                                                                                            Cardinality({
                                                                                                l \in Leaders:
                                                                                                    /\ i <= Len(logs[l])
                                                                                                    /\ logs[l][i].src  = pid_[self]
                                                                                                    /\ logs[l][i].cmd  = i
                                                                                                    /\ logs[l][i].term = prevLogTerm'[self]
                                                                                            }) >= M
                                                                                    } \union {0})]
                                    /\ logs' = [logs EXCEPT ![pid_[self]] =              AppendLog(
                                                                                logs[pid_[self]],
                                                                                [
                                                                                    src       |-> pid_[self],
                                                                                    term      |-> currentTerm[pid_[self]],
                                                                                    cmd       |-> cmd'[self],
                                                                                    committed |-> FALSE
                                                                                ],
                                                                                commitIndex'[self]
                                                                            )]
                                    /\ msgs' =         AppendEntries([
                                                   src          |-> pid_[self],
                                                   cmd          |-> cmd'[self],
                                                   term         |-> currentTerm[pid_[self]],
                                                   prevLogIndex |-> prevLogIndex'[self],
                                                   prevLogTerm  |-> prevLogTerm'[self],
                                                   commitIndex  |-> commitIndex'[self]
                                               ])
                                    /\ IF cmd'[self] > E
                                          THEN /\ states' = [l \in Leaders |-> "shutdown"]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED states
                                    /\ pc' = [pc EXCEPT ![self] = "leader_loop"]
                                    /\ UNCHANGED << currentTerm, 
                                                    electionTimeout, votes, 
                                                    voted >>
                         /\ UNCHANGED << pid_, pid_v, voteReq, pid, msg >>

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
                                     prevLogIndex, prevLogTerm, commitIndex, 
                                     pid_v, voteReq, pid, msg >>

l(self) == leader_loop(self) \/ leader_election(self) \/ check_votes(self)

voter_loop(self) == /\ pc[self] = "voter_loop"
                    /\ IF currentTerm[pid_v[self]] < T /\ states[pid_v[self]] /= "shutdown"
                          THEN /\ LET
                                  
                                      Votes == ToSet(votes[currentTerm[pid_v[self]]+1])
                                  IN
                                  
                                      /\ ~voted[currentTerm[pid_v[self]]+1][pid_v[self]]
                                  
                                      /\ \E v \in Votes: UpToDate(pid_v[self], v)
                               /\ voteReq' = [voteReq EXCEPT ![self] = Head(SelectSeq(votes[currentTerm[pid_v[self]]+1], LAMBDA v: UpToDate(pid_v[self], v)))]
                               /\ votes' = [votes EXCEPT ![currentTerm[pid_v[self]]+1] =                              Append(votes[currentTerm[pid_v[self]]+1], [
                                                                                             candidateId  |-> voteReq'[self].candidateId,
                                                                                             lastLogTerm  |-> voteReq'[self].lastLogTerm,
                                                                                             lastLogIndex |-> voteReq'[self].lastLogIndex
                                                                                         ])]
                               /\ voted' = [voted EXCEPT ![currentTerm[pid_v[self]]+1][pid_v[self]] = TRUE]
                               /\ currentTerm' = [currentTerm EXCEPT ![pid_v[self]] = currentTerm[pid_v[self]]+1]
                               /\ states' = [states EXCEPT ![pid_v[self]] = "follower"]
                               /\ pc' = [pc EXCEPT ![self] = "voter_loop"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << states, currentTerm, votes, 
                                               voted, voteReq >>
                    /\ UNCHANGED << electionTimeout, msgs, logs, pid_, cmd, 
                                    prevLogIndex, prevLogTerm, commitIndex, 
                                    pid_v, pid, msg >>

v(self) == voter_loop(self)

follower_loop(self) == /\ pc[self] = "follower_loop"
                       /\ Len(msgs[pid[self]]) > 0
                       /\ msg' = [msg EXCEPT ![self] = Head(msgs[pid[self]])]
                       /\ msgs' = [msgs EXCEPT ![pid[self]] = Tail(msgs[pid[self]])]
                       /\ IF msg'[self].term >= currentTerm[pid[self]] /\ states[pid[self]] /= "shutdown"
                             THEN /\ \/ /\ states' = [states EXCEPT ![pid[self]] = "follower"]
                                        /\ currentTerm' = [currentTerm EXCEPT ![pid[self]] = msg'[self].term]
                                        /\ electionTimeout' = [electionTimeout EXCEPT ![pid[self]] = FALSE]
                                        /\ IF (msg'[self].prevLogIndex = 0 /\ Len(logs[pid[self]]) = 0) \/
                                              (msg'[self].prevLogIndex > 0 /\ msg'[self].prevLogIndex <= Len(logs[pid[self]]) /\ msg'[self].prevLogTerm = logs[pid[self]][msg'[self].prevLogIndex].term)
                                              THEN /\ IF msg'[self].prevLogIndex+1 <= Len(logs[pid[self]]) /\ logs[pid[self]][msg'[self].prevLogIndex+1].term /= msg'[self].term
                                                         THEN /\ logs' = [logs EXCEPT ![pid[self]] =              AppendLog(
                                                                                                         SubSeq(logs[pid[self]], 1, msg'[self].prevLogIndex),
                                                                                                         [
                                                                                                             src       |-> msg'[self].src,
                                                                                                             term      |-> msg'[self].term,
                                                                                                             cmd       |-> msg'[self].cmd,
                                                                                                             committed |-> FALSE
                                                                                                         ],
                                                                                                         msg'[self].commitIndex
                                                                                                     )]
                                                         ELSE /\ logs' = [logs EXCEPT ![pid[self]] =              AppendLog(
                                                                                                         logs[pid[self]],
                                                                                                         [
                                                                                                             src       |-> msg'[self].src,
                                                                                                             term      |-> msg'[self].term,
                                                                                                             cmd       |-> msg'[self].cmd,
                                                                                                             committed |-> FALSE
                                                                                                         ],
                                                                                                         msg'[self].commitIndex
                                                                                                     )]
                                              ELSE /\ TRUE
                                                   /\ logs' = logs
                                     \/ /\ electionTimeout' = [electionTimeout EXCEPT ![pid[self]] = TRUE]
                                        /\ UNCHANGED <<states, currentTerm, logs>>
                             ELSE /\ TRUE
                                  /\ UNCHANGED << states, currentTerm, 
                                                  electionTimeout, logs >>
                       /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                       /\ UNCHANGED << votes, voted, pid_, cmd, prevLogIndex, 
                                       prevLogTerm, commitIndex, pid_v, 
                                       voteReq, pid >>

f(self) == follower_loop(self)

Next == (\E self \in Leaders: l(self))
           \/ (\E self \in Voters: v(self))
           \/ (\E self \in Followers: f(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Leaders : WF_vars(l(self))
        /\ \A self \in Voters : WF_vars(v(self))
        /\ \A self \in Followers : WF_vars(f(self))

\* END TRANSLATION 


=======================
