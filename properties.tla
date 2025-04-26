---- MODULE properties ----
EXTENDS protocol

\*=========================
\* Invariants
\*=========================

\* Invariant: finalizedHeight is the height of a block that is finalized, and no higher block is marked final.
\* (Follows from Assured Finality — finalized chain is prefix-consistent)
FinalizedHeightConsistent ==
    ∃ i ∈ 1..Len(blocks): blocks[i].height = finalizedHeight ∧ blocks[i].finalized = TRUE
    ∧ ∀ j ∈ 1..Len(blocks): blocks[j].finalized = TRUE ⇒ blocks[j].height ≤ finalizedHeight

\* Invariant: all blocks up to finalizedHeight are finalized (no gap in final prefix).
\* (Security Analysis: "LOG_fin is prefix-consistent" - prefix property of finalized chain)
ContiguousFinality ==
    ∀ i ∈ 1..Len(blocks): (blocks[i].height < finalizedHeight) ⇒ blocks[i].finalized = TRUE

\* Invariant: context_bft is non-decreasing along the chain (no block has context lower than its parent).
ContextMonotonic ==
    ∀ k ∈ 2..Len(blocks): blocks[k].context_bft ≥ blocks[k-1].context_bft

\* Stalled mode invariant: the stalled flag correctly reflects the chain gap
\* (Construction: Bounded-Availability Argument)
StalledCorrect == stalled = (currentHeight - finalizedHeight > L)

\* Progress requirement: to avoid deadlock, L must not be smaller than Sigma
\* (Construction Q&A: discussion of choosing L significantly larger than σ)
LNonDeadlock == L ≥ Sigma

\* You can’t require more votes than there are validators.
\* (Security Analysis: Definition "One-third bound on non-honest voting")
VoteThresholdBound == VoteThreshold ≤ Cardinality(Validators)

\* Every time votingHeight = 0, the map must be fully reset.
\* (Implicit in π_bft spec’s per-round reset - votes reset at round start)
VoteMapReset == votingHeight = 0 ⇒ votes = [ v ∈ Validators |-> FALSE ]

\* No one may vote unless a round is in progress.
\* (Implicit in π_bft spec — votes only valid during proposal phase)
VotesOnlyDuringVoting == ∃ v ∈ Validators: votes[v] = TRUE ⇒ votingHeight ≠ 0

\* σ‑Finality: every finalized block must have been ≥ Sigma deep when finalized.
\* (Construction: Tail Confirmation Rule - a block is only finalized if it is σ-deep)
SigmaFinality == ∀ i ∈ 2..Len(blocks) :
    blocks[i].finalized = TRUE ⇒ blocks[i].height + Sigma ≤ currentHeight

\* No rollback past final: once a block is finalized, it never disappears from the chain.
\* (Security Analysis: Theorem "LOG_{ba} does not roll back past the agreed LOG_{fin}")
NoRollbackPastFinal == ∀ i ∈ 1..Len(blocks) :
    blocks[i].finalized = TRUE ⇒ ∀ j ∈ i..Len(blocks) : blocks[j].height ≥ i

\* Assured Finality (trivial in single‐chain model, but for extension to multiple nodes
\* we would require the same finalized prefix across all honest replicas).
\* (Security Analysis: Theorem "LOG_{fin} Safety (from Prefix Agreement of Π_bc)"
\* and "LOG_{fin} Safety (from Final Agreement of Π_bft)")
AssuredFinality == TRUE

\*=========================
\* Temporal properties
\*=========================

\* Eventual Finality:
\* Every PoW block that gets mined will eventually be finalized by the BFT layer.
\* (Liveness of Finality - BFT makes progress under honest conditions; see
\* Questions About Crosslink §3.3.5)
EventualFinality == ∀ h ∈ 2..MaxHeight : □ ( (currentHeight ≥ h) ⇒
    ◇ (∃ i ∈ 1..Len(blocks) : blocks[i].height = h ∧ blocks[i].finalized = TRUE) )

\* No Permanent Stall (Bounded Availability):
\* If the chain falls too far behind finality (gap > L), it will eventually
\* catch back up or stop growing, rather than remain stalled forever.
\* (Bounded-Availability Argument; see Arguments for Bounded Availability §3.3.1)
NoPermanentStall == □ ( (currentHeight - finalizedHeight > L) ⇒
    ◇ (currentHeight - finalizedHeight ≤ L) )

====
