---- MODULE crosslink2 ----
EXTENDS TLC, Naturals, Sequences, utils

CONSTANTS BcNodes, BftNodes, CrossLink2Nodes
CONSTANTS Sigma, L

VARIABLES bc_chains, bft_chains, crosslink2_chains

INSTANCE definitions

----

Init == 
    /\ bc_chains = [i \in 1..BcNodes |-> <<BcGenesisBlock>>]
    /\ bft_chains = [i \in 1..BftNodes |-> <<BftGenesisBlock>>]
    /\ crosslink2_chains = [i \in 1..CrossLink2Nodes |-> CrossLink2GenesisBlock]

Next == 
    \/ \E n \in 1..BcNodes:
        /\ bc_chains' = [bc_chains EXCEPT ![n] = Append(
            bc_chains[ChooseBestBcChain], [
                context_bft |-> ChooseContextBft,
                hash |-> ChooseBestBcTip + 1])]
        /\ UNCHANGED <<bft_chains, crosslink2_chains>>
    \/ \E m \in 1..BftNodes:
        /\ bft_chains' = [bft_chains EXCEPT ![m] = Append(
            bft_chains[ChooseBestBftChain], [
                headers_bc |-> PruneLasts(ChooseBcView, Sigma),
                hash |-> ChooseBestBftTip + 1])]
        /\ UNCHANGED <<bc_chains, crosslink2_chains>>
    \/ \E c \in 1..CrossLink2Nodes:
        /\ crosslink2_chains' = [crosslink2_chains EXCEPT ![c] = [
            fin |-> PruneFirsts(bc_chains[ChooseBestBcChain], Sigma) ]]
        /\ UNCHANGED <<bc_chains, bft_chains>>

Spec == Init /\ [][Next]_<< bc_chains, bft_chains, crosslink2_chains >>

----

(*
Type checking
*)

BcChainsTypeCheck == bc_chains \in Seq(Seq([context_bft: Nat, hash: Nat]))
BftChainsTypeCheck == bft_chains \in 
    Seq(Seq([headers_bc: Seq([context_bft: Nat, hash: Nat]), hash: Nat]))
CrossLink2ChainsTypeCheck == crosslink2_chains \in 
    Seq([fin: Seq([context_bft: Nat, hash: Nat])])

----

(*
Lemma: Linear Prefix

`^ If $A \preceq_{\star} C$ and $B \preceq_{\star} C$ then $A \preceq\hspace{-0.5em}\succeq_{\star} B$. ^'
*)

BcLinearPrefix ==
    \A a, b, c \in 1..BcNodes:
        LET A == bc_chains[a]
            B == bc_chains[b]
            C == bc_chains[c]
        IN IsPrefix(A, C) /\ IsPrefix(B, C) =>
            IsPrefix(A, B) \/ IsPrefix(B, A)

BftLinearPrefix ==
    \A a, b, c \in 1..BftNodes:
        LET A == bft_chains[a]
            B == bft_chains[b]
            C == bft_chains[c]
        IN IsPrefix(A, C) /\ IsPrefix(B, C) =>
            IsPrefix(A, B) \/ IsPrefix(B, A)

(*
Definition: Agreement on a view

`^ An execution of $\Pi$ has Agreement on the view $V : \typecolon Node \times Time \rightarrow \star\text{chain}$ iff
for all times $t, u$ and all $\Pi$ nodes $i, j$ (potentially the same) such
that $i$ is honest at time $t$ and $j$ is honest at time $u$, we have $V_i^t\, \preceq\hspace{-0.5em}\succeq_{\star} V_j^u$. ^'
*)
BcViewAgreement ==
    \A i, j \in 1..BcNodes:
        \/ IsPrefix(bc_chains[i], bc_chains[j])
        \/ IsPrefix(bc_chains[j], bc_chains[i])

BftViewAgreement ==
    \A i, j \in 1..BftNodes:
        \/ IsPrefix(bft_chains[i], bft_chains[j])
        \/ IsPrefix(bft_chains[j], bft_chains[i])

(* 
Definition: Final agreement

`^ An execution of $\Pi_{\star\text{bft}}$​ has Final Agreement iff for all $\start\text{bftvalid}$ blocks 
$C$ in honest view at time $t$ and $C\prime$ in honest view at time $t\prime$, we have
$\start\text{bftlastfinal}(C) \preceq\hspace{-0.5em}\succeq_{\start\text{bft}} \star\text{bftlastfinal}(C\prime)$. ^'
*)
BftFinalAgreement ==
    \A i, j \in 1..BftNodes:
        \/ IsPrefix(BftLastFinal(i), BftLastFinal(j))
        \/ IsPrefix(BftLastFinal(j), BftLastFinal(i))

(* 
Definition: Prefix Consistency

`^ An execution of $\Pi_{\star\text{bc}}$​ has Prefix Consistency at confirmation depth $\sigma$,
iff for all times $t \le u$ and all nodes $i, j$ (potentially the same) such that
$i$ is honest at time $t$ and $j$ is honest at time $u$, we have that
$\text{ch}_i^t \lceil_{\star\text{bc}}^\sigma\, \preceq_{\star\text{bc}} \text{ch}_j^u$​. ^'
*)
BcPrefixConsistency ==
    \A i, j \in 1..BcNodes:
        Len(bc_chains[i]) <= Len(bc_chains[j]) =>
            IsPrefix(PruneFirsts(bc_chains[i], Sigma), bc_chains[j])

(*
Definition: Prefix Agreement

`^ An execution of $\Pi_{\star\text{bc}}$​ has Prefix Agreement at confirmation depth $\sigma$ iff it
has Agreement on the view $(i,t) \mapsto \text{ch}_i^t \lceil_{\star\text{bc}}^\sigma$.
*)
BcPrefixAgreement ==
    \A i \in 1..BcNodes:
        IsPrefix(PruneFirsts(bc_chains[i], Sigma), bc_chains[i])

(*
Definition: *-linear

`^ A function $S : I \to \star\text{block}$ is *-linear iff for every $t, u \in I$ where
$t \le u$ we have $S(t) \preceq_{\star} S(u)$ ^'
*)
BcLinear(T, U) == IsPrefix(T, U)

(*
Definition: Local finalization linearity

`^ Node $i$ has Local finalization linearity up to time $t$ iff the time series
of $\star\text{bc}$-blocks $\text{fin}_i^{r \le t}$ is $\star\text{bc}$-linear. ^'
*)
LocalFinalizationLinearity == [][
    \A i \in 1..CrossLink2Nodes:
        BcLinear(crosslink2_chains[i].fin, crosslink2_chains'[i].fin)]_crosslink2_chains

(*
Lemma: Local fin‑depth

`^ In any execution of Crosslink 2, for any node $i$ that is honest at time $t$,
there exists a time $r \le t$ such that $\text{fin}_i \preceq \text{ch}_i^r\lceil_{\star\text{bc}}^\sigma$ ^'
*)
LocalFinDepth ==
    \A i \in 1..CrossLink2Nodes:
        IsPrefix(crosslink2_chains[i].fin, bc_chains[ChooseBestBcChain])

(*
Definition: Assured Finality

`^ An execution of Crosslink 2 has Assured Finality iff for all times $t, u$
and all nodes $i, j$ (potentially the same) such that $i$ is honest at time $t$
and $j$ is honest at time $u$, we have $\text{fin}_i^t \preceq\hspace{-0.5em}\succeq_{bc} \text{fin}_j^u$. ^'
*)
AssuredFinality ==
    \A i, j \in 1..CrossLink2Nodes:
        \/ IsPrefix(crosslink2_chains[i].fin, crosslink2_chains[j].fin)
        \/ IsPrefix(crosslink2_chains[j].fin, crosslink2_chains[i].fin)

====
