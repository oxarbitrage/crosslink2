---- MODULE utils ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences

----

Max(S) ==
    IF S = {} THEN 0
    ELSE CHOOSE m ∈ S: ∀ x ∈ S: m ≥ x

PruneLasts(seq, n) ==
    IF n < 1 THEN <<>>
    ELSE IF n >= Len(seq) THEN seq
    ELSE SubSeq(seq, Len(seq) - n + 1, Len(seq))

PruneFirsts(seq, n) ==
    IF n < 1 THEN <<>>
    ELSE IF n >= Len(seq) THEN seq
    ELSE SubSeq(seq, 1, Len(seq) - n)

IsPrefix(p, s) ==
    ∧ Len(p) <= Len(s)
    ∧ ∀ i ∈ 1..Len(p): p[i] = s[i]

====
