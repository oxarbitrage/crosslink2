---- MODULE crosslink ----
EXTENDS TLC, Naturals, Sequences

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

(*--algorithm crosslink

variables 
    \* Initialize blockchain with genesis block at height 1.
    \* We consider genesis finalized by default (finalized = TRUE) and its context_bft = 1.
    blocks = << [height |-> 1, parent |-> 0, context_bft |-> 1, finalized |-> TRUE] >>,
    \* Height of the current tip of the chain (initially 1 at genesis).
    currentHeight = 1,
    \* Height of the latest finalized block (genesis is finalized at 1).
    finalizedHeight = 1,
    \* Stalled mode flag: TRUE if chain-gap > L
    stalled = FALSE
define
    Invariant_FinalizedHeightConsistent ==
        ∃ i ∈ 1..Len(blocks): blocks[i].height = finalizedHeight ∧ blocks[i].finalized = TRUE
        ∧ ∀ j ∈ 1..Len(blocks): blocks[j].finalized = TRUE ⇒ blocks[j].height ≤ finalizedHeight
    Invariant_ContiguousFinality ==
        ∀ i ∈ 1..Len(blocks): (blocks[i].height < finalizedHeight) ⇒ blocks[i].finalized = TRUE
    Invariant_ContextMonotonic ==
        ∀ k ∈ 2..Len(blocks): blocks[k].context_bft ≥ blocks[k-1].context_bft
    Invariant_StalledCorrect == stalled = (currentHeight - finalizedHeight > L)
    Invariant_LNonDeadlock == L ≥ Sigma
end define;

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
begin
    FinalizeLoop:
        while (TRUE) do
            \* Pause finalization when stalled
            if stalled then
                await stalled = FALSE;
            end if;
            \* Check if the next block to finalize (finalizedHeight+1) is Sigma-deep
            if currentHeight - (finalizedHeight + 1) ≥ Sigma then
                \* The block at height (finalizedHeight+1) exists and has >= Sigma confirmations.
                \* TODO: Voting logic to finalize the block, for now we just finalize it.
                targetHeight := finalizedHeight + 1;
                blocks[targetHeight].finalized := TRUE;
                finalizedHeight := targetHeight;
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
\* BEGIN TRANSLATION (chksum(pcal) = "8ae0788e" /\ chksum(tla) = "f94a3e92")
CONSTANT defaultInitValue
VARIABLES pc, blocks, currentHeight, finalizedHeight, stalled

(* define statement *)
Invariant_FinalizedHeightConsistent ==
    ∃ i ∈ 1..Len(blocks): blocks[i].height = finalizedHeight ∧ blocks[i].finalized = TRUE
    ∧ ∀ j ∈ 1..Len(blocks): blocks[j].finalized = TRUE ⇒ blocks[j].height ≤ finalizedHeight
Invariant_ContiguousFinality ==
    ∀ i ∈ 1..Len(blocks): (blocks[i].height < finalizedHeight) ⇒ blocks[i].finalized = TRUE
Invariant_ContextMonotonic ==
    ∀ k ∈ 2..Len(blocks): blocks[k].context_bft ≥ blocks[k-1].context_bft
Invariant_StalledCorrect == stalled = (currentHeight - finalizedHeight > L)
Invariant_LNonDeadlock == L ≥ Sigma

VARIABLES newHeight, newParentHeight, newContext, targetHeight

vars == << pc, blocks, currentHeight, finalizedHeight, stalled, newHeight, 
           newParentHeight, newContext, targetHeight >>

ProcSet == (Miners) \cup (Validators)

Init == (* Global variables *)
        /\ blocks = << [height |-> 1, parent |-> 0, context_bft |-> 1, finalized |-> TRUE] >>
        /\ currentHeight = 1
        /\ finalizedHeight = 1
        /\ stalled = FALSE
        (* Process Miner *)
        /\ newHeight = [self \in Miners |-> defaultInitValue]
        /\ newParentHeight = [self \in Miners |-> defaultInitValue]
        /\ newContext = [self \in Miners |-> defaultInitValue]
        (* Process Validator *)
        /\ targetHeight = [self \in Validators |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Miners -> "MineAndCommit"
                                        [] self \in Validators -> "FinalizeLoop"]

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
                       /\ UNCHANGED << finalizedHeight, stalled, targetHeight >>

Miner(self) == MineAndCommit(self)

FinalizeLoop(self) == /\ pc[self] = "FinalizeLoop"
                      /\ IF stalled
                            THEN /\ stalled = FALSE
                            ELSE /\ TRUE
                      /\ IF currentHeight - (finalizedHeight + 1) ≥ Sigma
                            THEN /\ targetHeight' = [targetHeight EXCEPT ![self] = finalizedHeight + 1]
                                 /\ blocks' = [blocks EXCEPT ![targetHeight'[self]].finalized = TRUE]
                                 /\ finalizedHeight' = targetHeight'[self]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << blocks, finalizedHeight, 
                                                 targetHeight >>
                      /\ stalled' = ((currentHeight - finalizedHeight') > L)
                      /\ IF currentHeight = MaxHeight ∧ (currentHeight - finalizedHeight') ≤ Sigma
                            THEN /\ pc' = [pc EXCEPT ![self] = "Ending"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "FinalizeLoop"]
                      /\ UNCHANGED << currentHeight, newHeight, 
                                      newParentHeight, newContext >>

Ending(self) == /\ pc[self] = "Ending"
                /\ Assert(currentHeight = MaxHeight, 
                          "Failure of assertion at line 100, column 9.")
                /\ Assert(finalizedHeight = MaxHeight - Sigma, 
                          "Failure of assertion at line 101, column 9.")
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << blocks, currentHeight, finalizedHeight, 
                                stalled, newHeight, newParentHeight, 
                                newContext, targetHeight >>

Validator(self) == FinalizeLoop(self) \/ Ending(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Miners: Miner(self))
           \/ (\E self \in Validators: Validator(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
