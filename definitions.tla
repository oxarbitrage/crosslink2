---- MODULE definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE utils

CONSTANTS BcNodes, BftNodes, CrossLink2Nodes
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
The views and tips for the chains.
*)
BcView(i) == bc_chains[i]
BcTip(i) == BcView(i)[Len(BcView(i))]

BftView(i) == bft_chains[i]
BftTip(i) == BftView(i)[Len(BftView(i))]

BcTips == { BcTip(i) : i \in 1..BcNodes }
BftTips == { BftTip(i) : i \in 1..BftNodes }

----

(*
The best chain selection functions.
*)
ChooseBestBcTip == Max({t.hash : t \in BcTips})
ChooseBestBftTip == Max({t.hash : t \in BftTips})

ChooseContextBft == Max({t.hash : t \in BcTips})

ChooseBestBcChain == 
    CHOOSE i \in 1..BcNodes: Len(bc_chains[i]) = Max({Len(bc_chains[j]) : j \in 1..BcNodes})

ChooseBestBftChain == 
    CHOOSE i \in 1..BftNodes: Len(bft_chains[i]) = Max({Len(bft_chains[j]) : j \in 1..BftNodes})

ChooseBcView == BcView(CHOOSE i \in 1..BcNodes: TRUE)

ChooseBestCrosslinkChain ==
    CHOOSE i \in 1..CrossLink2Nodes: Len(crosslink2_chains[i]) = 
        Max({Len(crosslink2_chains[j]) : j \in 1..CrossLink2Nodes})

====
