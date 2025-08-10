---- MODULE definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE utils

CONSTANTS BcNodes, BftNodes, CrossLink2Nodes
CONSTANTS Sigma, L

VARIABLES bc_chains, bft_chains, crosslink2_chains

----

BcGenesisBlock == [context_bft |-> 0, hash |-> 0]
BftGenesisBlock == [headers_bc |-> <<>>, hash |-> 0]
CrossLink2GenesisBlock == [fin |-> BcGenesisBlock]

BcView(i) == bc_chains[i]
BcTip(i) == BcView(i)[Len(BcView(i))]

BftView(i) == bft_chains[i]
BftTip(i) == BftView(i)[Len(BftView(i))]

BcTips == { BcTip(i) : i ∈ 1..BcNodes }
BftTips == { BftTip(i) : i ∈ 1..BftNodes }

ChooseContextBft == Max({t.hash : t \in BcTips})

ChooseBestBcChain == 
    CHOOSE i ∈ 1..BcNodes: Len(bc_chains[i]) = Max({Len(bc_chains[j]) : j ∈ 1..BcNodes})

ChooseBestBftChain == 
    CHOOSE i ∈ 1..BftNodes: Len(bft_chains[i]) = Max({Len(bft_chains[j]) : j ∈ 1..BftNodes})

ChooseBcView == BcView(CHOOSE i ∈ 1..BcNodes: TRUE) 

====
