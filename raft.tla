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
        states = [l \in Servers |-> "follower"],

        \* servers submit votes during an election.
        votes = [l \in Servers |-> << >>],

        \* servers send followers heartbeats.
        heartbeats = [l \in Servers |-> << >>],

        \* whether the last heartbeat was dropped.
        heartbeat_dropped = [l \in Servers |-> FALSE],

        \* each server's current term. Unique to gaurantee at least server wins election.
        terms = [l \in Servers |-> 0];

    define {
        \* all the servers.
        Servers == 1..N

        \* all the voters.
        Voters == N+1..N*2

        \* all the followers.
        Followers == N*2+1..N*3
        
        \* set a message to all the server queues.
        Send(queues, msg) == [i \in 1..Len(queues) |-> Append(queues[i], msg)]

        \* overall invariant.
        TypeOK ==
            \* at most one leader at a time.
            Len(SelectSeq(states, LAMBDA s: s = "leader")) <= 1
    }

    \* send a heartbeat to all servers with the latest term.
    macro Heartbeat(pid) {
        terms[pid] := terms[pid] + 1;
        heartbeats := Send(heartbeats, [
            src  |-> pid,
            term |-> terms[pid]
        ]);
    }

    \* increment own term and set self as candidate.
    macro RequestVote(pid) {
        \* wait for a "dropped" heartbeat, ie a period where we have not heard from a leader.
        await heartbeat_dropped[pid];

        states[pid] := "candidate";
        terms[pid]  := terms[pid] + 1;
        votes       := Send(votes, [
            for  |-> pid, \* recipient of vote
            from |-> pid, \* debugging
            term |-> terms[pid]
        ]);

        heartbeat_dropped[pid] := FALSE;
    }

    \* check votes from the election. This server wins if a majority of
    \* other servers voted for it in the same term.
    macro CheckVotes(pid) {
        await
            \* we won the election with a majority of votes.
            \/ Len(SelectSeq(votes[pid], LAMBDA v: v.for = pid /\ v.term = terms[pid])) >= M
            \* another leader sent an equal or greater vote for a different server.
            \/ Len(SelectSeq(votes[pid], LAMBDA v: v.for /= pid /\ v.term >= terms[pid])) > 0;

        \* revert to being a follower.
        if (Len(SelectSeq(votes[pid], LAMBDA v: v.for /= pid /\ v.term >= terms[pid])) > 0) {
            states[pid] := "follower";
        } else {
            \* become leader and assert leadership.
            states[pid] := "leader";
            terms[pid]  := terms[pid] + 1;
        };
    }

    \* leader process.
    fair process (l \in Servers)
    variables pid = self;
    {
        leader_loop:
        while (terms[pid] < TermLimit) {
            leader_election:
            while (states[pid] /= "leader") {
                \* when heartbeats reaches zero, start election as candidate.
                request_vote:
                RequestVote(pid);

                \* check if this server won.
                check_votes:
                CheckVotes(pid);
            };

            heartbeat:
            Heartbeat(pid);
        };
    };

    \* voter process.
    fair process (v \in Voters)
    variables vote_index = 1, pid = self - N;
    {
        voter_loop:
        while (terms[pid] < TermLimit) {
            \* wait for a new vote or heartbeat to arrive.
            await Len(votes[pid]) = vote_index;

            \* if a candidate has a higher term than us, vote for them.
            if (votes[pid][vote_index].term > terms[pid] /\
                \* do not submit duplicate votes in the same term, first one wins.
                Len(SelectSeq(votes[pid], LAMBDA v: v.term = votes[pid][vote_index].term /\ v.from = pid)) = 0) {
                votes := Send(votes, [
                    for  |-> votes[pid][vote_index].for, \* recipient of vote
                    from |-> pid, \* debugging
                    term |-> votes[pid][vote_index].term
                ]);
            };

            vote_index := vote_index + 1;
        };
    };

    \* follower process.
    fair process (f \in Followers)
    variables heartbeat_index = 1, pid = self - N*2;
    {
        follower_loop:
        while (terms[pid] < TermLimit) {
            either {
                \* wait for a new heartbeat to arrive.
                follower_recv_heartbeat:
                await Len(heartbeats[pid]) = heartbeat_index;

                if (heartbeats[pid][heartbeat_index].term >= terms[pid]) {
                    states[pid] := "follower";
                    terms[pid]  := heartbeats[pid][heartbeat_index].term;
                };

                heartbeat_index        := heartbeat_index + 1;
                heartbeat_dropped[pid] := FALSE;
            } or {
                follower_drop_heartbeat:
                heartbeat_dropped[pid] := TRUE;
            };
        };
    };
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "696496f5" /\ chksum(tla) = "eea29a1e")
\* Process variable pid of process l at line 97 col 15 changed to pid_
\* Process variable pid of process v at line 119 col 31 changed to pid_v
VARIABLES states, votes, heartbeats, heartbeat_dropped, terms, pc

(* define statement *)
Servers == 1..N


Voters == N+1..N*2


Followers == N*2+1..N*3


Send(queues, msg) == [i \in 1..Len(queues) |-> Append(queues[i], msg)]


TypeOK ==

    Len(SelectSeq(states, LAMBDA s: s = "leader")) <= 1

VARIABLES pid_, vote_index, pid_v, heartbeat_index, pid

vars == << states, votes, heartbeats, heartbeat_dropped, terms, pc, pid_, 
           vote_index, pid_v, heartbeat_index, pid >>

ProcSet == (Servers) \cup (Voters) \cup (Followers)

Init == (* Global variables *)
        /\ states = [l \in Servers |-> "follower"]
        /\ votes = [l \in Servers |-> << >>]
        /\ heartbeats = [l \in Servers |-> << >>]
        /\ heartbeat_dropped = [l \in Servers |-> FALSE]
        /\ terms = [l \in Servers |-> 0]
        (* Process l *)
        /\ pid_ = [self \in Servers |-> self]
        (* Process v *)
        /\ vote_index = [self \in Voters |-> 1]
        /\ pid_v = [self \in Voters |-> self - N]
        (* Process f *)
        /\ heartbeat_index = [self \in Followers |-> 1]
        /\ pid = [self \in Followers |-> self - N*2]
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "leader_loop"
                                        [] self \in Voters -> "voter_loop"
                                        [] self \in Followers -> "follower_loop"]

leader_loop(self) == /\ pc[self] = "leader_loop"
                     /\ IF terms[pid_[self]] < TermLimit
                           THEN /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << states, votes, heartbeats, 
                                     heartbeat_dropped, terms, pid_, 
                                     vote_index, pid_v, heartbeat_index, pid >>

leader_election(self) == /\ pc[self] = "leader_election"
                         /\ IF states[pid_[self]] /= "leader"
                               THEN /\ pc' = [pc EXCEPT ![self] = "request_vote"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "heartbeat"]
                         /\ UNCHANGED << states, votes, heartbeats, 
                                         heartbeat_dropped, terms, pid_, 
                                         vote_index, pid_v, heartbeat_index, 
                                         pid >>

request_vote(self) == /\ pc[self] = "request_vote"
                      /\ heartbeat_dropped[pid_[self]]
                      /\ states' = [states EXCEPT ![pid_[self]] = "candidate"]
                      /\ terms' = [terms EXCEPT ![pid_[self]] = terms[pid_[self]] + 1]
                      /\ votes' =                Send(votes, [
                                      for  |-> pid_[self],
                                      from |-> pid_[self],
                                      term |-> terms'[pid_[self]]
                                  ])
                      /\ heartbeat_dropped' = [heartbeat_dropped EXCEPT ![pid_[self]] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "check_votes"]
                      /\ UNCHANGED << heartbeats, pid_, vote_index, pid_v, 
                                      heartbeat_index, pid >>

check_votes(self) == /\ pc[self] = "check_votes"
                     /\ \/ Len(SelectSeq(votes[pid_[self]], LAMBDA v: v.for = pid_[self] /\ v.term = terms[pid_[self]])) >= M
                        
                        \/ Len(SelectSeq(votes[pid_[self]], LAMBDA v: v.for /= pid_[self] /\ v.term >= terms[pid_[self]])) > 0
                     /\ IF Len(SelectSeq(votes[pid_[self]], LAMBDA v: v.for /= pid_[self] /\ v.term >= terms[pid_[self]])) > 0
                           THEN /\ states' = [states EXCEPT ![pid_[self]] = "follower"]
                                /\ terms' = terms
                           ELSE /\ states' = [states EXCEPT ![pid_[self]] = "leader"]
                                /\ terms' = [terms EXCEPT ![pid_[self]] = terms[pid_[self]] + 1]
                     /\ pc' = [pc EXCEPT ![self] = "leader_election"]
                     /\ UNCHANGED << votes, heartbeats, heartbeat_dropped, 
                                     pid_, vote_index, pid_v, heartbeat_index, 
                                     pid >>

heartbeat(self) == /\ pc[self] = "heartbeat"
                   /\ terms' = [terms EXCEPT ![pid_[self]] = terms[pid_[self]] + 1]
                   /\ heartbeats' =               Send(heartbeats, [
                                        src  |-> pid_[self],
                                        term |-> terms'[pid_[self]]
                                    ])
                   /\ pc' = [pc EXCEPT ![self] = "leader_loop"]
                   /\ UNCHANGED << states, votes, heartbeat_dropped, pid_, 
                                   vote_index, pid_v, heartbeat_index, pid >>

l(self) == leader_loop(self) \/ leader_election(self) \/ request_vote(self)
              \/ check_votes(self) \/ heartbeat(self)

voter_loop(self) == /\ pc[self] = "voter_loop"
                    /\ IF terms[pid_v[self]] < TermLimit
                          THEN /\ Len(votes[pid_v[self]]) = vote_index[self]
                               /\ IF votes[pid_v[self]][vote_index[self]].term > terms[pid_v[self]] /\
                                     
                                     Len(SelectSeq(votes[pid_v[self]], LAMBDA v: v.term = votes[pid_v[self]][vote_index[self]].term /\ v.from = pid_v[self])) = 0
                                     THEN /\ votes' =          Send(votes, [
                                                          for  |-> votes[pid_v[self]][vote_index[self]].for,
                                                          from |-> pid_v[self],
                                                          term |-> votes[pid_v[self]][vote_index[self]].term
                                                      ])
                                     ELSE /\ TRUE
                                          /\ votes' = votes
                               /\ vote_index' = [vote_index EXCEPT ![self] = vote_index[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "voter_loop"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << votes, vote_index >>
                    /\ UNCHANGED << states, heartbeats, heartbeat_dropped, 
                                    terms, pid_, pid_v, heartbeat_index, pid >>

v(self) == voter_loop(self)

follower_loop(self) == /\ pc[self] = "follower_loop"
                       /\ IF terms[pid[self]] < TermLimit
                             THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "follower_recv_heartbeat"]
                                     \/ /\ pc' = [pc EXCEPT ![self] = "follower_drop_heartbeat"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << states, votes, heartbeats, 
                                       heartbeat_dropped, terms, pid_, 
                                       vote_index, pid_v, heartbeat_index, pid >>

follower_recv_heartbeat(self) == /\ pc[self] = "follower_recv_heartbeat"
                                 /\ Len(heartbeats[pid[self]]) = heartbeat_index[self]
                                 /\ IF heartbeats[pid[self]][heartbeat_index[self]].term >= terms[pid[self]]
                                       THEN /\ states' = [states EXCEPT ![pid[self]] = "follower"]
                                            /\ terms' = [terms EXCEPT ![pid[self]] = heartbeats[pid[self]][heartbeat_index[self]].term]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << states, terms >>
                                 /\ heartbeat_index' = [heartbeat_index EXCEPT ![self] = heartbeat_index[self] + 1]
                                 /\ heartbeat_dropped' = [heartbeat_dropped EXCEPT ![pid[self]] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                                 /\ UNCHANGED << votes, heartbeats, pid_, 
                                                 vote_index, pid_v, pid >>

follower_drop_heartbeat(self) == /\ pc[self] = "follower_drop_heartbeat"
                                 /\ heartbeat_dropped' = [heartbeat_dropped EXCEPT ![pid[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "follower_loop"]
                                 /\ UNCHANGED << states, votes, heartbeats, 
                                                 terms, pid_, vote_index, 
                                                 pid_v, heartbeat_index, pid >>

f(self) == follower_loop(self) \/ follower_recv_heartbeat(self)
              \/ follower_drop_heartbeat(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Servers: l(self))
           \/ (\E self \in Voters: v(self))
           \/ (\E self \in Followers: f(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(l(self))
        /\ \A self \in Voters : WF_vars(v(self))
        /\ \A self \in Followers : WF_vars(f(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=======================
