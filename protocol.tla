---- MODULE protocol ----
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
    \* Sequence of finalized and non-finalized blocks we have in the blockchain.
    blocks = << [height |-> 1, context_bft |-> 1, finalized |-> TRUE] >>,
    \* Height of the current tip of the chain.
    currentHeight = 1,
    \* Height of the latest finalized block.
    finalizedHeight = 1,
    \* Stalled mode flag: TRUE if chain-gap > L
    stalled = FALSE,
    \* Height of block currently under vote (0 = none)
    votingHeight = 0,
    \* Map of validators votes
    votes = [v ∈ Validators |-> FALSE]

define
    Tally == Cardinality({ v ∈ Validators : votes[v] = TRUE })
end define;

\* Miner processes
process Miner ∈ Miners
begin
    MineAndCommit:
        while currentHeight < MaxHeight do
            \* Pause mining when stalled
            if stalled then
                await stalled = FALSE;
            end if;
            \* Create and append the new block
            blocks := Append(blocks, [
                height      |-> currentHeight + 1, 
                context_bft |-> finalizedHeight, 
                finalized   |-> FALSE
            ]);
            currentHeight := currentHeight + 1;
        end while;
end process;

\* Finality Validator processes
process Validator ∈ Validators
begin
    Finalizer:
        while (TRUE) do
            \* Pause finalization when stalled
            if stalled then
                await stalled = FALSE;
            end if;

            \* 1) If no round in progress and block is σ‐deep, start round
            if votingHeight = 0 ∧ currentHeight - (finalizedHeight + 1) ≥ Sigma then
                votingHeight := finalizedHeight + 1;
                \* Create round map and vote for the proposed block in a single step
                votes := [ v ∈ Validators |-> IF v = self THEN TRUE ELSE FALSE ];
            \* 2) If we already hit the threshold, finalize *before* any more votes
            elsif votingHeight ≠ 0 ∧ Tally ≥ VoteThreshold then
                blocks         := [ blocks EXCEPT ![votingHeight].finalized = TRUE ];
                finalizedHeight:= votingHeight;
                votingHeight   := 0;
                votes          := [ v ∈ Validators |-> FALSE ];
            \* 3) Otherwise, if this validator hasn’t voted yet *and* we’re still below threshold, cast one vote
            elsif votingHeight ≠ 0 ∧ votes[self] = FALSE ∧ Tally < VoteThreshold then
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

\* BEGIN TRANSLATION (chksum(pcal) = "f091a0fe" /\ chksum(tla) = "d78ac1bf")
VARIABLES pc, blocks, currentHeight, finalizedHeight, stalled, votingHeight, 
          votes

(* define statement *)
Tally == Cardinality({ v ∈ Validators : votes[v] = TRUE })


vars == << pc, blocks, currentHeight, finalizedHeight, stalled, votingHeight, 
           votes >>

ProcSet == (Miners) \cup (Validators)

Init == (* Global variables *)
        /\ blocks = << [height |-> 1, context_bft |-> 1, finalized |-> TRUE] >>
        /\ currentHeight = 1
        /\ finalizedHeight = 1
        /\ stalled = FALSE
        /\ votingHeight = 0
        /\ votes = [v ∈ Validators |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Miners -> "MineAndCommit"
                                        [] self \in Validators -> "Finalizer"]

MineAndCommit(self) == /\ pc[self] = "MineAndCommit"
                       /\ IF currentHeight < MaxHeight
                             THEN /\ IF stalled
                                        THEN /\ stalled = FALSE
                                        ELSE /\ TRUE
                                  /\ blocks' =           Append(blocks, [
                                                   height      |-> currentHeight + 1,
                                                   context_bft |-> finalizedHeight,
                                                   finalized   |-> FALSE
                                               ])
                                  /\ currentHeight' = currentHeight + 1
                                  /\ pc' = [pc EXCEPT ![self] = "MineAndCommit"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << blocks, currentHeight >>
                       /\ UNCHANGED << finalizedHeight, stalled, votingHeight, 
                                       votes >>

Miner(self) == MineAndCommit(self)

Finalizer(self) == /\ pc[self] = "Finalizer"
                   /\ IF stalled
                         THEN /\ stalled = FALSE
                         ELSE /\ TRUE
                   /\ IF votingHeight = 0 ∧ currentHeight - (finalizedHeight + 1) ≥ Sigma
                         THEN /\ votingHeight' = finalizedHeight + 1
                              /\ votes' = [ v ∈ Validators |-> IF v = self THEN TRUE ELSE FALSE ]
                              /\ UNCHANGED << blocks, finalizedHeight >>
                         ELSE /\ IF votingHeight ≠ 0 ∧ Tally ≥ VoteThreshold
                                    THEN /\ blocks' = [ blocks EXCEPT ![votingHeight].finalized = TRUE ]
                                         /\ finalizedHeight' = votingHeight
                                         /\ votingHeight' = 0
                                         /\ votes' = [ v ∈ Validators |-> FALSE ]
                                    ELSE /\ IF votingHeight ≠ 0 ∧ votes[self] = FALSE ∧ Tally < VoteThreshold
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
                   /\ UNCHANGED currentHeight

Ending(self) == /\ pc[self] = "Ending"
                /\ Assert(currentHeight = MaxHeight, 
                          "Failure of assertion at line 93, column 9.")
                /\ Assert(finalizedHeight = MaxHeight - Sigma, 
                          "Failure of assertion at line 94, column 9.")
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << blocks, currentHeight, finalizedHeight, 
                                stalled, votingHeight, votes >>

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

====
