---- MODULE properties ----
EXTENDS protocol

\*=========================
\* Type checker
\*=========================

\* Constants
ConstantsTC ==
    Sigma ∈ Nat ∧
    MaxHeight ∈ Nat ∧
    L ∈ Nat ∧
    VoteThreshold ∈ Nat ∧
    Miners ∈ SUBSET STRING ∧
    Validators ∈ SUBSET STRING

\* Variables
VariablesTC ==
    blocks ∈ Seq([height: Nat, context_bft: Nat, finalized: BOOLEAN]) ∧
    currentHeight ∈ Nat ∧
    finalizedHeight ∈ Nat ∧
    stalled ∈ BOOLEAN ∧
    votingHeight ∈ Nat

\*=========================
\* Invariants
\*=========================

\* `finalizedHeight` is the height of a block that is finalized, no higher block can be marked final.
FinalizedHeightConsistent ==
    ∃ i ∈ 1..Len(blocks): blocks[i].height = finalizedHeight ∧ blocks[i].finalized = TRUE ∧
        ∀ j ∈ 1..Len(blocks): blocks[j].finalized = TRUE ⇒ blocks[j].height ≤ finalizedHeight

\* All blocks up to `finalizedHeight` are finalized (no gap in final prefix).
ContiguousFinality ==
    ∀ i ∈ 1..Len(blocks): (blocks[i].height < finalizedHeight) ⇒ blocks[i].finalized = TRUE

\* `context_bft` is non-decreasing along the chain (no block has context lower than its parent).
ContextMonotonic ==
    ∀ k ∈ 2..Len(blocks): blocks[k].context_bft ≥ blocks[k-1].context_bft

\* Stalled mode: The stalled flag correctly reflects the chain gap.
StalledCorrect == stalled = (currentHeight - finalizedHeight > L)

\* Progress requirement: to avoid deadlock, L must not be smaller than Sigma
LNonDeadlock == L ≥ Sigma

\* You can’t require more votes than there are validators.
VoteThresholdBound == VoteThreshold ≤ Cardinality(Validators)

\* Every time votingHeight = 0, the map must be fully reset.
VoteMapReset == votingHeight = 0 ⇒ votes = [ v ∈ Validators |-> FALSE ]

\* No one may vote unless a round is in progress.
VotesOnlyDuringVoting == ∃ v ∈ Validators: votes[v] = TRUE ⇒ votingHeight ≠ 0

\* σ‑Finality: every finalized block must have been ≥ Sigma deep when finalized.
SigmaFinality == ∀ i ∈ 2..Len(blocks) :
    blocks[i].finalized = TRUE ⇒ blocks[i].height + Sigma ≤ currentHeight

\* No rollback past final: once a block is finalized, it never disappears from the chain.
NoRollbackPastFinal == ∀ i ∈ 1..Len(blocks) :
    blocks[i].finalized = TRUE ⇒ ∀ j ∈ i..Len(blocks) : blocks[j].height ≥ i

(* Assured Finality (trivial in single‐chain model, but for extension to multiple nodes
we would require the same finalized prefix across all honest replicas).
Security Analysis: Theorem "LOG_{fin} Safety (from Prefix Agreement of Π_bc)"
and "LOG_{fin} Safety (from Final Agreement of Π_bft)" *)
AssuredFinality == TRUE

\*=========================
\* Temporal properties
\*=========================

(* Eventual Finality:
Every PoW block that gets mined will eventually be finalized by the BFT layer.
Liveness of Finality - BFT makes progress under honest conditions *)
EventualFinality == ∀ h ∈ 2..MaxHeight : □ ( (currentHeight ≥ h) ⇒
    ◇ (∃ i ∈ 1..Len(blocks) : blocks[i].height = h ∧ blocks[i].finalized = TRUE) )

(* No Permanent Stall (Bounded Availability):
If the chain falls too far behind finality (gap > L), it will eventually
catch back up or stop growing, rather than remain stalled forever. *)
NoPermanentStall == □ ( (currentHeight - finalizedHeight > L) ⇒
    ◇ (currentHeight - finalizedHeight ≤ L) )

====
