---- MODULE utils ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences

----

Max(S) ==
    IF S = {} THEN 0
    ELSE CHOOSE m \in S: \A x \in S: m >= x

PruneLasts(seq, n) ==
    IF n < 1 THEN <<>>
    ELSE IF n >= Len(seq) THEN seq
    ELSE SubSeq(seq, Len(seq) - n + 1, Len(seq))

PruneFirsts(seq, n) ==
    IF n < 1 THEN <<>>
    ELSE IF n >= Len(seq) THEN seq
    ELSE SubSeq(seq, 1, Len(seq) - n)

IsPrefix(p, s) ==
    /\ Len(p) <= Len(s)
    /\ \A i \in 1..Len(p): p[i] = s[i]

====
