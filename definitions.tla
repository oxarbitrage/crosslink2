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
Convenient sets
*)
HonestBftNodes == 1..BftNodes \ ByzBft
BftAllNodes == 1..BftNodes
BcAllNodes == 1..BcNodes

(*
Choose the best BC chain (the longest one).
*)
BestBcChainIdx ==
    CHOOSE i \in BcAllNodes: 
        Len(bc_chains[i]) = Max({Len(bc_chains[j]) : j \in BcAllNodes})



(*
The number of nodes supporting the same chain as node i.
*)
BftSupport(i) == Cardinality({ j \in BftAllNodes : bft_chains[j] = bft_chains[i] })

(*
Byzantine classic fault tolerance threshold condition
*)
BftThresholdOK == BftNodes >= 3 * Cardinality(ByzBft) + 1

(*
Choose the best BFT chain (the longest one with the most support).

- Lmax = maximum length of all BFT chains
- S = set of nodes having the longest chains
- supMax = maximum support among the longest chains
- T = set of nodes having the longest chains with the maximum support
*)
BestBftChainIdx ==
    LET
        Lmax   == Max({ Len(bft_chains[k]) : k \in BftAllNodes })
        S      == { i \in BftAllNodes : Len(bft_chains[i]) = Lmax }
        supMax == Max({ BftSupport(k) : k \in S })
        T      == { i \in S : BftSupport(i) = supMax }
    IN
        CHOOSE i \in T : TRUE

(*
Definition: Computable efficiently function

`^ $\star\text{bftlastfinal} : \star\text{bftblock} \to \star\text{bftblock} \cup \{\bot\}$ ^'
*)
BftLastFinal(n) == bft_chains[n]

====
