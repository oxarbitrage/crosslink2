---- MODULE definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE utils

CONSTANTS BcNodes, BftNodes, CrossLink2Nodes
CONSTANTS ByzBft, ByzCl
CONSTANTS Sigma, L

VARIABLES bc_chains, bft_chains, crosslink2_chains

----

(*
The genesis blocks for the chains.
*)
BcGenesisBlock == [context_bft |-> 0, hash |-> 0]
BftGenesisBlock == [headers_bc |-> <<>>, hash |-> 0]
CrossLink2GenesisBlock == [fin |-> <<BcGenesisBlock>>]

----

(*
Choose the best BC chain (the longest one).
*)
BestBcChainIdx ==
    CHOOSE i \in 1..BcNodes: Len(bc_chains[i]) = Max({Len(bc_chains[j]) : j \in 1..BcNodes})

(*
The subset of honest BFT nodes.
*)
HonestBftNodes == 1..BftNodes \ ByzBft

(*
The set of all BFT nodes.
*)
BftAllNodes == 1..BftNodes

(*
The number of nodes supporting the same chain as node i.
*)
BftSupport(i) == Cardinality({ j \in BftAllNodes : bft_chains[j] = bft_chains[i] })

(*
BFT Assumptions
*)
BftThresholdOK == BftNodes >= 3 * Cardinality(ByzBft) + 1

(*
Choose the best BFT chain (the longest one with the most support).
*)
BestBftChainIdx ==
    LET
        \* The maximum length of all BFT chains
        Lmax   == Max({ Len(bft_chains[k]) : k \in BftAllNodes })
        \* The set of nodes having the longest chains
        S      == { i \in BftAllNodes : Len(bft_chains[i]) = Lmax }
        \* The maximum support among the longest chains
        supMax == Max({ BftSupport(k) : k \in S })
        \* The set of nodes having the longest chains with the maximum support
        T      == { i \in S : BftSupport(i) = supMax }
    IN
        CHOOSE i \in T : TRUE

(*
Choose the best Crosslink chain (the longest one).
*)
ChooseBestCrosslinkChain ==
    CHOOSE i \in 1..CrossLink2Nodes: Len(crosslink2_chains[i]) = 
        Max({Len(crosslink2_chains[j]) : j \in 1..CrossLink2Nodes})

(*
Definition: Computable efficiently function

`^ $\star\text{bftlastfinal} : \star\text{bftblock} \to \star\text{bftblock} \cup \{\bot\}$ ^'
*)
BftLastFinal(n) == bft_chains[n]

====
