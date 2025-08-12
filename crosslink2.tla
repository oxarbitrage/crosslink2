---- MODULE crosslink2 ----
EXTENDS TLC, Naturals, Sequences, utils

CONSTANTS BcNodes, BftNodes, CrossLink2Nodes
CONSTANTS Sigma, L

VARIABLES bc_chains, bft_chains, crosslink2_chains

INSTANCE definitions

----

Init == 
    ∧ bc_chains = [i ∈ 1..BcNodes |-> <<BcGenesisBlock>>]
    ∧ bft_chains = [i ∈ 1..BftNodes |-> <<BftGenesisBlock>>]
    ∧ crosslink2_chains = [i ∈ 1..CrossLink2Nodes |-> CrossLink2GenesisBlock]

Next == 
    ∨ ∃ n ∈ 1..BcNodes:
        ∧ bc_chains' = [bc_chains EXCEPT ![n] = Append(bc_chains[ChooseBestBcChain], [
            context_bft |-> ChooseContextBft,
            hash |-> ChooseBestBcTip + 1])]
        ∧ UNCHANGED <<bft_chains, crosslink2_chains>>
    ∨ ∃ m ∈ 1..BftNodes:
        ∧ bft_chains' = [bft_chains EXCEPT ![m] = Append(bft_chains[ChooseBestBftChain], [
            headers_bc |-> PruneLasts(ChooseBcView, Sigma),
            hash |-> ChooseBestBftTip + 1])]
        ∧ UNCHANGED <<bc_chains, crosslink2_chains>>
    ∨ ∃ c ∈ 1..CrossLink2Nodes:
        ∧ crosslink2_chains' = [crosslink2_chains EXCEPT ![c] = [
            fin |-> bc_chains[ChooseBestBcChain] ]]
        ∧ UNCHANGED <<bc_chains, bft_chains>>

Spec == Init ∧ □[Next]_<< bc_chains, bft_chains, crosslink2_chains >>

----

BcChainsTypeCheck == bc_chains ∈ Seq(Seq([context_bft: Nat, hash: Nat]))
BftChainsTypeCheck == bft_chains ∈ Seq(Seq([headers_bc: Seq([context_bft: Nat, hash: Nat]), hash: Nat]))
CrossLink2ChainsTypeCheck == crosslink2_chains ∈ Seq([fin: Seq([context_bft: Nat, hash: Nat])])

(* Lemma: Linear Prefix

If A ⪯∗​ C and B ⪯∗ ​C then A ⪯⪰∗ ​B.

*)
BcLinearPrefix ==
    ∀ i ∈ 1..BcNodes:
        ∀ k ∈ 2..Len(bc_chains[i]): bc_chains[i][k].hash ≥ bc_chains[i][k-1].hash

BftLinearPrefix ==
    ∀ i ∈ 1..BftNodes:
        ∀ k ∈ 2..Len(bft_chains[i]): bft_chains[i][k].hash ≥ bft_chains[i][k-1].hash

(* Definition: Agreement on a view

An execution of Π has Agreement on the view V ⦂ Node × Time → ∗-chain iff
for all times t, u and all Π nodes i, j (potentially the same) such
that i is honest at time t and j is honest at time u, we have Vit ​⪯⪰∗ ​Vju​.

*)
BcViewAgreement ==
    ∀ i, j ∈ 1..BcNodes:
        ∨ IsPrefix(bc_chains[i], bc_chains[j])
        ∨ IsPrefix(bc_chains[j], bc_chains[i])

BftViewAgreement ==
    ∀ i, j ∈ 1..BftNodes:
        ∨ IsPrefix(bft_chains[i], bft_chains[j])
        ∨ IsPrefix(bft_chains[j], bft_chains[i])

(* Efficiently computable function

∗bft-last-final ⦂ ∗bft-block → ∗bft-block ∪ {⊥}

*)
BftLastFinal(n) == bft_chains[n]

(* Definition: Final agreement

An execution of Π∗bft​ has Final Agreement iff for all ∗bft‑valid blocks 
C in honest view at time t and C′ in honest view at time t′, we have
∗bft-last-final(C) ⪯⪰∗bft ​∗bft-last-final(C′).

*)
BftFinalAgreement ==
    ∀ i, j ∈ 1..BftNodes:
        ∨ IsPrefix(BftLastFinal(i), BftLastFinal(j))
        ∨ IsPrefix(BftLastFinal(j), BftLastFinal(i))

(* Definition: Prefix Consistency

An execution of Π∗bc​ has Prefix Consistency at confirmation depth σ,
iff for all times t ≤ u and all nodes i, j (potentially the same) such that
i is honest at time t and j is honest at time u, we have that 
chit​⌈∗bcσ ​⪯∗ bc​chju​.

*)
BcPrefixConsistency ==
    ∀ i, j ∈ 1..BcNodes:
        IsPrefix(PruneFirsts(bc_chains[i], Sigma), bc_chains[j])

(* Definition: Prefix Agreement

An execution of Π∗bc​ has Prefix Agreement at confirmation depth σ iff it
has Agreement on the view(i,t) ↦ chit​⌈∗bcσ​.

*)
BcPrefixAgreement ==
    ∀ i ∈ 1..BcNodes:
        IsPrefix(PruneFirsts(bc_chains[i], Sigma), bc_chains[i])

(* Definition: *-linear

A function S ⦂ I → ∗-block is ∗‑linear iff for every t,u ⦂ I where
t ≤ u we have S(t) ⪯∗ ​S(u)

*)
BcLinear(T, U) == IsPrefix(T, U)

(* Definition: Local finalization linearity

Node i has Local finalization linearity up to time t iff the time series
of bc‑blocks finir ≤ t​ is bc‑linear.

*)
\* temporal property
LocalFinalizationLinearity == [][
    ∀ i ∈ 1..CrossLink2Nodes:
        BcLinear(crosslink2_chains[i].fin, crosslink2_chains'[i].fin)]_crosslink2_chains

(* Lemma: Local fin‑depth

In any execution of Crosslink 2, for any node i that is honest at time t,
there exists a time r≤t such that finit​ ⪯ chir​⌈bcσ​.

*)
\* TODO: need sigma
LocalFinDepth ==
    ∀ i ∈ 1..CrossLink2Nodes:
        IsPrefix(crosslink2_chains[i].fin, bc_chains[ChooseBestBcChain])

(* Definition: Assured Finality

An execution of Crosslink 2 has Assured Finality iff for all times t, u
and all nodes i, j (potentially the same) such that i is honest at time t
and j is honest at time u, we have finit​ ⪯⪰bc ​finju​.

*)
AssuredFinality ==
    ∀ i, j ∈ 1..CrossLink2Nodes:
        ∨ IsPrefix(crosslink2_chains[i].fin, crosslink2_chains[j].fin)
        ∨ IsPrefix(crosslink2_chains[j].fin, crosslink2_chains[i].fin)

====
