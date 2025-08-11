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

\* lemma
BcLinearPrefix ==
    ∀ i ∈ 1..BcNodes:
        ∀ k ∈ 2..Len(bc_chains[i]): bc_chains[i][k].hash ≥ bc_chains[i][k-1].hash

\* lemma
BftLinearPrefix ==
    ∀ i ∈ 1..BftNodes:
        ∀ k ∈ 2..Len(bft_chains[i]): bft_chains[i][k].hash ≥ bft_chains[i][k-1].hash

\* definition
BcViewAgreement ==
    ∀ i, j ∈ 1..BcNodes:
        ∨ IsPrefix(bc_chains[i], bc_chains[j])
        ∨ IsPrefix(bc_chains[j], bc_chains[i])

\* definition
BftViewAgreement ==
    ∀ i, j ∈ 1..BftNodes:
        ∨ IsPrefix(bft_chains[i], bft_chains[j])
        ∨ IsPrefix(bft_chains[j], bft_chains[i])

\* definition
BftLastFinal(n) == bft_chains[n]

\* definition
BftFinalAgreement ==
    ∀ i, j ∈ 1..BftNodes:
        ∨ IsPrefix(BftLastFinal(i), BftLastFinal(j))
        ∨ IsPrefix(BftLastFinal(j), BftLastFinal(i))

\* definition
BcPrefixConsistency ==
    ∀ i, j ∈ 1..BcNodes:
        IsPrefix(PruneFirsts(bc_chains[i], Sigma), bc_chains[j])

\* definition
BcPrefixAgreement ==
    ∀ i ∈ 1..BcNodes:
        IsPrefix(PruneFirsts(bc_chains[i], Sigma), bc_chains[i])

\* definition
BcLinear(T, U) == IsPrefix(T, U)

\* definition
LocalFinalizationLinearity == [][
    ∀ i ∈ 1..CrossLink2Nodes:
        BcLinear(crosslink2_chains[i].fin, crosslink2_chains'[i].fin)]_crosslink2_chains

====
