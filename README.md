# TLA+

This is a dumping ground for specs I'm using to learn TLA+, PlusCal, and some distributed systems algorithms.

## Overview

Before making this repo, I wanted to learn [TLA+](https://en.wikipedia.org/wiki/TLA%2B) for awhile. It comes up regularly in tweets and blog [posts](https://brooker.co.za/blog/2024/04/17/formal.html) espousing its power. I got the chance during a week-long hackathon at MongoDB. On its first day, two MongoDB researchers, Murat Demirbas -- professor, principal engineer, and author of the hugely popular [muratbuffalo.blogspot.com](https://muratbuffalo.blogspot.com/) blog -- and Jesse Davis, senior staff engineer (https://emptysqua.re/blog/), gave a day-long seminar on TLA+, TLC, and PlusCal.

This has some specs from the first day of the hackathon ([beans.tla](./beans.tla), [beans3.tla](./beans3.tla)), the rest of that week ([raft.tla](./raft.tla)), and hopefully more from later (TBD).

> TLA+ is a high-level language for modeling programs and systems--especially concurrent and distributed ones. It's based on the idea that the best way to describe things precisely is with simple mathematics. TLA+ and its tools are useful for eliminating fundamental design errors, which are hard to find and expensive to correct in code.

[https://lamport.azurewebsites.net/tla](https://lamport.azurewebsites.net/tla/tla.html)

## Contents

### Raft

> Raft is a consensus algorithm for managing a replicated log. It produces a result equivalent to (multi-) Paxos, and it is as efficient as Paxos, but its structure is different from Paxos; this makes Raft more understandable than Paxos and also provides a better foundation for building practical systems.

_Ongaro, Diego, and John Ousterhout. "In search of an understandable consensus algorithm." 2014 USENIX annual technical conference (USENIX ATC 14). 2014._

[https://raft.github.io/raft.pdf](https://raft.github.io/raft.pdf)

#### Used In

- [Consul](https://www.datocms-assets.com/2885/1597077859-consul-life-of-a-packet-service-mesh-v11-digital.pdf)
- [Vault](https://developer.hashicorp.com/vault/docs/configuration/storage/raft)
- [etcd](https://github.com/etcd-io/raft)
- [MongoDB](https://www.usenix.org/conference/nsdi21/presentation/zhou) (modified pull-based version)
