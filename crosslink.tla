---- MODULE crosslink ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

\* Constants

\* Sigma = confirmation depth required for finality
CONSTANT Sigma
\* MaxHeight = maximum block height to mine (for bounded simulation)
CONSTANT MaxHeight
\* The set of miners.
CONSTANT Miners
\* The set of validators.
CONSTANT Validators
\* L = maximum allowable gap between chain tip and finalized block before stalling
CONSTANT L
\* Number of votes required to finalize a block
CONSTANT VoteThreshold

(*--algorithm crosslink

variables 
    \* Initialize blockchain with genesis block at height 1.
    \* We consider genesis finalized by default (finalized = TRUE) and its context_bft = 1.
    \* TODO: In this simplified model, all nodes share the same blockchain state,
    \* which is not the case in practice. In practice, each node has its own state.
    blocks = << [height |-> 1, parent |-> 0, context_bft |-> 1, finalized |-> TRUE] >>,
    \* Height of the current tip of the chain (initially 1 at genesis).
    currentHeight = 1,
    \* Height of the latest finalized block (genesis is finalized at 1).
    finalizedHeight = 1,
    \* Stalled mode flag: TRUE if chain-gap > L
    stalled = FALSE,
    \* Height of block currently under vote (0 = none)
    votingHeight = 0,
    \* Map of validators' votes
    votes = [v ∈ Validators |-> FALSE]

\* Miner processes
process Miner ∈ Miners
variables
    newHeight,
    newParentHeight,
    newContext
begin
    MineAndCommit:
        while currentHeight < MaxHeight do
            \* Pause mining when stalled
            if stalled then
                await stalled = FALSE;
            end if;
            \* Determine new block properties
            newHeight := currentHeight + 1;
            \* parent is the tip's height
            newParentHeight := currentHeight;
            \* BFT context = last finalized height at time of mining
            newContext := finalizedHeight;
            \* Create and append the new block
            blocks := Append(blocks, [
                height      |-> newHeight, 
                parent      |-> newParentHeight, 
                context_bft |-> newContext, 
                finalized   |-> FALSE
            ]);
            currentHeight := newHeight;
        end while;
end process;

\* Finality Validator processes
process Validator ∈ Validators
variables
    \* Height of the block to be finalized
    targetHeight,
    voteCount,
begin
    Finalizer:
        while (TRUE) do
            \* Pause finalization when stalled
            if stalled then
                await stalled = FALSE;
            end if;

            \* Tally number of votes
            voteCount := Cardinality({ v ∈ Validators : votes[v] = TRUE });

            \* 1) If no round in progress and block is σ‐deep, start round
            if votingHeight = 0 ∧ currentHeight - (finalizedHeight + 1) ≥ Sigma then
                votingHeight := finalizedHeight + 1;
                \* Create round map and vote for the proposed block in a single step
                votes := [ v ∈ Validators |-> IF v = self THEN TRUE ELSE FALSE ];
            \* 2) If we already hit the threshold, finalize *before* any more votes
            elsif votingHeight ≠ 0 ∧ voteCount ≥ VoteThreshold then
                blocks         := [ blocks EXCEPT ![votingHeight].finalized = TRUE ];
                finalizedHeight:= votingHeight;
                votingHeight   := 0;
                votes          := [ v ∈ Validators |-> FALSE ];
            \* 3) Otherwise, if this validator hasn’t voted yet *and* we’re still below threshold, cast one vote
            elsif votingHeight ≠ 0 ∧ votes[self] = FALSE ∧ voteCount < VoteThreshold then
                votes[self] := TRUE;
            end if;

            \* Update stalled mode based on gap
            stalled := (currentHeight - finalizedHeight) > L;
            \* Termination condition
            if currentHeight = MaxHeight ∧ (currentHeight - finalizedHeight) ≤ Sigma then
                \* Chain stopped growing and no further finalization possible (tail not deep enough)
                goto Ending;
            end if;
        end while;
    Ending:
        assert currentHeight = MaxHeight;
        assert finalizedHeight = MaxHeight - Sigma;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "49ca6a16" /\ chksum(tla) = "f25e437")
CONSTANT defaultInitValue
VARIABLES pc, blocks, currentHeight, finalizedHeight, stalled, votingHeight, 
          votes, newHeight, newParentHeight, newContext, targetHeight, 
          voteCount

vars == << pc, blocks, currentHeight, finalizedHeight, stalled, votingHeight, 
           votes, newHeight, newParentHeight, newContext, targetHeight, 
           voteCount >>

ProcSet == (Miners) \cup (Validators)

Init == (* Global variables *)
        /\ blocks = << [height |-> 1, parent |-> 0, context_bft |-> 1, finalized |-> TRUE] >>
        /\ currentHeight = 1
        /\ finalizedHeight = 1
        /\ stalled = FALSE
        /\ votingHeight = 0
        /\ votes = [v ∈ Validators |-> FALSE]
        (* Process Miner *)
        /\ newHeight = [self \in Miners |-> defaultInitValue]
        /\ newParentHeight = [self \in Miners |-> defaultInitValue]
        /\ newContext = [self \in Miners |-> defaultInitValue]
        (* Process Validator *)
        /\ targetHeight = [self \in Validators |-> defaultInitValue]
        /\ voteCount = [self \in Validators |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Miners -> "MineAndCommit"
                                        [] self \in Validators -> "Finalizer"]

MineAndCommit(self) == /\ pc[self] = "MineAndCommit"
                       /\ IF currentHeight < MaxHeight
                             THEN /\ IF stalled
                                        THEN /\ stalled = FALSE
                                        ELSE /\ TRUE
                                  /\ newHeight' = [newHeight EXCEPT ![self] = currentHeight + 1]
                                  /\ newParentHeight' = [newParentHeight EXCEPT ![self] = currentHeight]
                                  /\ newContext' = [newContext EXCEPT ![self] = finalizedHeight]
                                  /\ blocks' =           Append(blocks, [
                                                   height      |-> newHeight'[self],
                                                   parent      |-> newParentHeight'[self],
                                                   context_bft |-> newContext'[self],
                                                   finalized   |-> FALSE
                                               ])
                                  /\ currentHeight' = newHeight'[self]
                                  /\ pc' = [pc EXCEPT ![self] = "MineAndCommit"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << blocks, currentHeight, 
                                                  newHeight, newParentHeight, 
                                                  newContext >>
                       /\ UNCHANGED << finalizedHeight, stalled, votingHeight, 
                                       votes, targetHeight, voteCount >>

Miner(self) == MineAndCommit(self)

Finalizer(self) == /\ pc[self] = "Finalizer"
                   /\ IF stalled
                         THEN /\ stalled = FALSE
                         ELSE /\ TRUE
                   /\ voteCount' = [voteCount EXCEPT ![self] = Cardinality({ v ∈ Validators : votes[v] = TRUE })]
                   /\ IF votingHeight = 0 ∧ currentHeight - (finalizedHeight + 1) ≥ Sigma
                         THEN /\ votingHeight' = finalizedHeight + 1
                              /\ votes' = [ v ∈ Validators |-> IF v = self THEN TRUE ELSE FALSE ]
                              /\ UNCHANGED << blocks, finalizedHeight >>
                         ELSE /\ IF votingHeight ≠ 0 ∧ voteCount'[self] ≥ VoteThreshold
                                    THEN /\ blocks' = [ blocks EXCEPT ![votingHeight].finalized = TRUE ]
                                         /\ finalizedHeight' = votingHeight
                                         /\ votingHeight' = 0
                                         /\ votes' = [ v ∈ Validators |-> FALSE ]
                                    ELSE /\ IF votingHeight ≠ 0 ∧ votes[self] = FALSE ∧ voteCount'[self] < VoteThreshold
                                               THEN /\ votes' = [votes EXCEPT ![self] = TRUE]
                                               ELSE /\ TRUE
                                                    /\ votes' = votes
                                         /\ UNCHANGED << blocks, 
                                                         finalizedHeight, 
                                                         votingHeight >>
                   /\ stalled' = ((currentHeight - finalizedHeight') > L)
                   /\ IF currentHeight = MaxHeight ∧ (currentHeight - finalizedHeight') ≤ Sigma
                         THEN /\ pc' = [pc EXCEPT ![self] = "Ending"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Finalizer"]
                   /\ UNCHANGED << currentHeight, newHeight, newParentHeight, 
                                   newContext, targetHeight >>

Ending(self) == /\ pc[self] = "Ending"
                /\ Assert(currentHeight = MaxHeight, 
                          "Failure of assertion at line 110, column 9.")
                /\ Assert(finalizedHeight = MaxHeight - Sigma, 
                          "Failure of assertion at line 111, column 9.")
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << blocks, currentHeight, finalizedHeight, 
                                stalled, votingHeight, votes, newHeight, 
                                newParentHeight, newContext, targetHeight, 
                                voteCount >>

Validator(self) == Finalizer(self) \/ Ending(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Miners: Miner(self))
           \/ (\E self \in Validators: Validator(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* INVARIANTS

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

\* TEMPORAL PROPERTIES

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
