------------------- MODULE POPL24_HerlihyWingQueuePrelude -------------------
(****************************************************************************
Author: Uğur Y. Yavuz
Date: 2023-10-02

This module contains some lemmas that are used in the proofs in
POPL24_HerlihyWingQueue.tla.
****************************************************************************)
EXTENDS Integers, FiniteSetTheorems, Functions, FunctionTheorems, TLAPS

\* The set of all permutations of items of S
Perm(S) == {f \in [1..Cardinality(S) -> S] : \A w \in S : \E q \in 1..Cardinality(S) : f[q] = w}

\* The length of a sequence
Len(s) == CHOOSE n \in Nat : DOMAIN s = 1..n

\* The length of a permutation is the same as the cardinality of the set it permutes
LEMMA PermLength == \A S : IsFiniteSet(S) => (\A pi \in Perm(S) : Cardinality(S) = Len(pi))
  BY FS_CardinalityType DEF Perm, Len

\* Permutation of a set has different elements at different indices
LEMMA PermDistinct == \A S : IsFiniteSet(S) => (\A pi \in Perm(S) : \A k, m \in DOMAIN pi : k # m => pi[k] # pi[m])
  <1> SUFFICES ASSUME NEW S, IsFiniteSet(S),
                      NEW pi \in Perm(S),
                      NEW k \in DOMAIN pi, NEW m \in DOMAIN pi,
                      k # m, pi[k] = pi[m]
               PROVE  FALSE
    BY Zenon
  <1> DEFINE pi_pred == [s \in (1..Cardinality(S)) \ {m} |-> pi[s]]
  <1>1. pi_pred \in Surjection(1..Cardinality(S) \ {m}, S)
    BY Fun_IsSurj, Zenon DEF Perm
  <1>2. IsFiniteSet(1..Cardinality(S))
    BY FS_CardinalityType, FS_Interval
  <1>3. IsFiniteSet(1..Cardinality(S) \ {m})
    BY <1>2, FS_RemoveElement, Zenon
  <1>4. m \in 1..Cardinality(S)
    BY DEF Perm
  <1>5. Cardinality(1..Cardinality(S)) = Cardinality(S)
    BY FS_CardinalityType, FS_Interval
  <1>6. Cardinality(1..Cardinality(S) \ {m}) = Cardinality(S)-1
    BY <1>2, <1>4, <1>5, FS_RemoveElement, Zenon
  <1>7. Cardinality(S) <= Cardinality(S)-1
    BY <1>1, <1>3, <1>6, FS_Surjection
  <1> QED
    BY <1>7, FS_CardinalityType

\* Every set of integers has a maximum element
LEMMA MaxElement == \A S : (S \in SUBSET Int /\ S # {} /\ IsFiniteSet(S)) => \E s \in S : (\A y \in S : y <= s)
  <1> SUFFICES ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
               PROVE  \E s \in S : (\A y \in S : y <= s)
    OBVIOUS
  <1> DEFINE P(A) == (A \in SUBSET Int /\ A # {} /\ IsFiniteSet(A)) => \E s \in A : (\A y \in A : y <= s)
  <1>1. P({})
    OBVIOUS
  <1>2. ASSUME NEW A, NEW s, P(A), s \notin A
               PROVE P(A \union {s})
    <2> SUFFICES ASSUME A \union {s} \in SUBSET Int,
                        A \union {s} # {}, IsFiniteSet(A \union {s})
                 PROVE P(A \union {s})
      OBVIOUS
    <2>1. CASE \A y \in A : y <= s
      BY <2>1
    <2>2. CASE \E y \in A : ~(y <= s)
      <3>1. A # {}
        BY <2>2
      <3>2. IsFiniteSet(A)
        BY FS_Subset
      <3>3. PICK y \in A : \A z \in A : z <= y
        BY <1>2, <3>1, <3>2
      <3>4. s < y
        BY <2>2, <3>3
      <3> QED
        BY <3>3, <3>4
    <2> QED
      BY <2>1, <2>2
  <1> HIDE DEF P
  <1>3. P(S)
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
  <1> QED
    BY <1>3, Zenon DEF P

\* There exists an ordering f (a bijection 1..Card(S) -> S that monotonically increases) 
\* of every finite set S of integers.
LEMMA WellOrderingPrinciple == \A S : (S \in SUBSET Int /\ IsFiniteSet(S)) => \E f \in Bijection(1..Cardinality(S), S) : (\A m, n \in 1..Cardinality(S) : m < n => f[m] < f[n])
  <1> SUFFICES ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
               PROVE  \E f \in Bijection(1..Cardinality(S), S) : (\A m, n \in 1..Cardinality(S) : m < n => f[m] < f[n])
    OBVIOUS
  <1> DEFINE P(A) == (A \in SUBSET Int /\ IsFiniteSet(A)) => \E f \in Bijection(1..Cardinality(A), A) : (\A m, n \in 1..Cardinality(A) : m < n => f[m] < f[n])
  <1>1. P({})
    <2> USE FS_EmptySet
    <2>1. {} \in SUBSET Int /\ IsFiniteSet({})
      OBVIOUS
    <2> DEFINE f == [z \in {} |-> z]
    <2>2. f \in Bijection(1..Cardinality({}), {})
      BY DEF Bijection, Injection, Surjection
    <2> QED BY <2>2
  <1>2. ASSUME NEW A, NEW s, P(A), s \notin A
               PROVE P(A \union {s})
    <2> SUFFICES ASSUME A \union {s} \in SUBSET Int,
                        IsFiniteSet(A \union {s})
                 PROVE  P(A \union {s})
      BY Zenon
    <2>1. A \in SUBSET Int /\ IsFiniteSet(A)
      BY FS_Subset
    <2>2. Cardinality(A \union {s}) = Cardinality(A)+1
      BY <1>2, <2>1, FS_AddElement
    <2>3. PICK f \in Bijection(1..Cardinality(A), A) : (\A m, n \in 1..Cardinality(A) : m < n => f[m] < f[n])
      BY <1>2, <2>1
    <2>4. DOMAIN f = 1..Cardinality(A)
      BY <2>3 DEF Bijection, Injection, Surjection
    <2>5. f \in Perm(A)
      BY DEF Perm, Bijection, Surjection
    <2>6. \A y \in A : y # s
      BY <1>2
    <2>7. CASE \A y \in A : y < s
      <3> DEFINE g == [k \in 1..(Cardinality(A)+1) |-> IF k = Cardinality(A)+1 THEN s ELSE f[k]]
      <3>1. \A m, n \in 1..(Cardinality(A)+1) : m < n => g[m] < g[n]
        <4> SUFFICES ASSUME NEW m \in 1..(Cardinality(A)+1), 
                            NEW n \in 1..(Cardinality(A)+1), m < n
                     PROVE  g[m] < g[n]
          OBVIOUS
        <4>1. CASE n = Cardinality(A)+1
          <5>1. g[n] = s
            BY <4>1
          <5>2. m \in 1..Cardinality(A)
            BY <2>1, <4>1, FS_CardinalityType
          <5>3. g[m] \in A
            BY <2>3, <5>2 DEF Bijection, Injection, Surjection
          <5> QED
            BY <2>7, <5>1, <5>3
        <4>2. CASE n < Cardinality(A)+1
          <5>1. n \in 1..Cardinality(A) /\ m \in 1..Cardinality(A)
            BY <2>1, <4>2, FS_CardinalityType
          <5>2. g[m] = f[m] /\ g[n] = f[n]
            BY <2>1, <4>2, <5>1, FS_CardinalityType
          <5> QED
            BY <2>3, <5>1, <5>2
        <4> QED
          BY <2>1, <4>1, <4>2, FS_CardinalityType
      
      <3>2. g \in [1..(Cardinality(A)+1) -> A \union {s}]
        BY <2>1, <2>3, FS_CardinalityType DEF Bijection, Injection, Surjection
      
      <3>3. g \in Injection(1..(Cardinality(A)+1), A \union {s})
        <4> SUFFICES ASSUME NEW a \in 1..(Cardinality(A)+1),
                            NEW b \in 1..(Cardinality(A)+1),
                            g[a] = g[b]
                     PROVE  a = b
          BY <3>2, Fun_IsInj, Zenon
        <4>1. CASE a = Cardinality(A)+1 /\ b < Cardinality(A)+1
          <5>1. g[a] = s /\ g[b] = f[b]
            BY <2>1, <4>1, FS_CardinalityType
          <5>2. f[b] \in A
            BY <2>1, <2>3, <4>1, FS_CardinalityType DEF Bijection, Injection, Surjection
          <5> QED
            BY <1>2, <5>1, <5>2
        <4>2. CASE a < Cardinality(A)+1 /\ b = Cardinality(A)+1
          <5>1. g[a] = f[a] /\ g[b] = s
            BY <2>1, <4>2, FS_CardinalityType
          <5>2. f[a] \in A
            BY <2>1, <2>3, <4>2, FS_CardinalityType DEF Bijection, Injection, Surjection
          <5> QED
            BY <1>2, <5>1, <5>2
        <4>3. CASE a < Cardinality(A)+1 /\ b < Cardinality(A)+1
          <5>1. g[a] = f[a] /\ g[b] = f[b]
            BY <2>1, <4>3, FS_CardinalityType
          <5>2. a \in 1..Cardinality(A) /\ b \in 1..Cardinality(A)
            BY <2>1, <4>3, FS_CardinalityType
          <5> QED
            BY <2>1, <2>5, <2>4, <5>1, <5>2, PermDistinct, Zenon
        <4> QED
          BY <2>1, <4>1, <4>2, <4>3, FS_CardinalityType
      <3>4. g \in Surjection(1..(Cardinality(A)+1), A \union {s})
        <4> SUFFICES ASSUME NEW b \in A \union {s}
                     PROVE  \E a \in 1..(Cardinality(A)+1) : g[a] = b
          BY <3>2, Fun_IsSurj, Zenon
        <4>1. CASE b = s
          BY <2>1, <4>1, FS_CardinalityType
        <4>2. CASE b \in A
          <5>1. PICK a \in 1..Cardinality(A) : f[a] = b
            BY <2>3, <4>2 DEF Bijection, Surjection
          <5>2. g[a] = f[a]
            BY <2>1, <5>1, FS_CardinalityType
          <5> QED
            BY <2>1, <5>1, <5>2, FS_CardinalityType
        <4> QED
          BY <4>1, <4>2
      <3>5. g \in Bijection(1..(Cardinality(A)+1), A \union {s})
        BY <3>3, <3>4 DEF Bijection
      <3> QED
        BY <1>2, <2>2, <3>1, <3>5, Zenon
    <2>8. CASE \A y \in A : s < y
      <3> DEFINE g == [k \in 1..(Cardinality(A)+1) |-> IF k = 1 THEN s ELSE f[k-1]]
      <3>1. \A m, n \in 1..(Cardinality(A)+1) : m < n => g[m] < g[n]
        <4> SUFFICES ASSUME NEW m \in 1..(Cardinality(A)+1), 
                            NEW n \in 1..(Cardinality(A)+1), m < n
                     PROVE  g[m] < g[n]
          OBVIOUS
        <4>1. CASE m = 1
          <5>1. g[m] = s
            BY <4>1
          <5>2. n \in 2..(Cardinality(A)+1)
            BY <2>1, <4>1, FS_CardinalityType
          <5>3. n-1 \in 1..(Cardinality(A))
            BY <2>1, <5>2, FS_CardinalityType
          <5>4. g[n] \in A
            BY <2>3, <5>3 DEF Bijection, Injection, Surjection
          <5> QED
            BY <2>8, <5>1, <5>4
        <4>2. CASE m > 1
          <5>1. m \in 2..(Cardinality(A)+1) /\ n \in 2..(Cardinality(A)+1)
            BY <2>1, <4>2, FS_CardinalityType
          <5>2. m-1 \in 1..Cardinality(A) /\ n-1 \in 1..Cardinality(A)
            BY <2>1, <5>1, FS_CardinalityType
          <5>3. g[m] = f[m-1] /\ g[n] = f[n-1]
            BY <2>1, <4>2, <5>1, FS_CardinalityType
          <5> QED
            BY <2>3, <5>2, <5>3
        <4> QED
          BY <2>1, <4>1, <4>2, FS_CardinalityType
      <3>2. g \in [1..(Cardinality(A)+1) -> A \union {s}]
        BY <2>1, <2>3, FS_CardinalityType DEF Bijection, Injection, Surjection
      <3>3. g \in Injection(1..(Cardinality(A)+1), A \union {s})
        <4> SUFFICES ASSUME NEW a \in 1..(Cardinality(A)+1),
                            NEW b \in 1..(Cardinality(A)+1),
                            g[a] = g[b]
                     PROVE  a = b
          BY <3>2, Fun_IsInj, Zenon
        <4>1. CASE a = 1 /\ b > 1
          <5>1. g[a] = s /\ g[b] = f[b-1]
            BY <2>1, <4>1, FS_CardinalityType
          <5>2. f[b-1] \in A
            BY <2>1, <2>3, <4>1, FS_CardinalityType DEF Bijection, Injection, Surjection
          <5> QED
            BY <1>2, <5>1, <5>2
        <4>2. CASE a > 1 /\ b = 1
          <5>1. g[a] = f[a-1] /\ g[b] = s
            BY <2>1, <4>2, FS_CardinalityType
          <5>2. f[a-1] \in A
            BY <2>1, <2>3, <4>2, FS_CardinalityType DEF Bijection, Injection, Surjection
          <5> QED
            BY <1>2, <5>1, <5>2
        <4>3. CASE a > 1 /\ b > 1
          <5>1. g[a] = f[a-1] /\ g[b] = f[b-1]
            BY <2>1, <4>3, FS_CardinalityType
          <5>2. a-1 \in 1..Cardinality(A) /\ b-1 \in 1..Cardinality(A)
            BY <2>1, <4>3, FS_CardinalityType
          <5>3. \A h, d \in DOMAIN f : h # d => f[h] # f[d]
            BY <2>1, <2>4, <2>5, PermDistinct, Zenon
          <5>4. a-1 = b-1
            BY <2>4, <5>2, <5>3
          <5> QED
            BY <5>1, <5>4
        <4> QED
          BY <2>1, <4>1, <4>2, <4>3, FS_CardinalityType
      <3>4. g \in Surjection(1..(Cardinality(A)+1), A \union {s})
        <4> SUFFICES ASSUME NEW b \in A \union {s}
                     PROVE  \E a \in 1..(Cardinality(A)+1) : g[a] = b
          BY <3>2, Fun_IsSurj, Zenon
        <4>1. CASE b = s
          BY <2>1, <4>1, FS_CardinalityType
        <4>2. CASE b \in A
          <5>1. PICK a \in 1..Cardinality(A) : f[a] = b
            BY <2>3, <4>2 DEF Bijection, Surjection
          <5>2. g[a+1] = f[a]
            BY <2>1, <5>1, FS_CardinalityType
          <5> QED
            BY <2>1, <5>1, <5>2, FS_CardinalityType
        <4> QED
          BY <4>1, <4>2
      <3>5. g \in Bijection(1..(Cardinality(A)+1), A \union {s})
        BY <3>3, <3>4 DEF Bijection
      <3> QED
        BY <1>2, <2>2, <3>1, <3>5, Zenon
    <2>9. CASE ~(\A y \in A : y < s) /\ ~(\A y \in A : s < y)
      <3>1. \E y \in A : s < y
        BY <2>6, <2>9
      <3>2. \E z \in A : z < s
        BY <2>6, <2>9
      <3> DEFINE pred_cands == {z \in A : z < s}
      <3>3. (pred_cands \in SUBSET Int /\ IsFiniteSet(pred_cands) /\ pred_cands # {})
        BY <2>1, <3>1, <3>2, FS_Subset
      <3>4. PICK pred \in pred_cands : \A y \in pred_cands : y <= pred
        BY <3>3, MaxElement, Zenon
      <3>5. PICK pred_k \in 1..Cardinality(A) : f[pred_k] = pred
        BY <2>3 DEF Bijection, Surjection
      <3>6. \A k \in 1..pred_k : f[k] < s 
        <4> SUFFICES ASSUME NEW k \in 1..pred_k, ~(f[k] < s), k # pred_k
                     PROVE  FALSE
          BY <3>4, <3>5
        <4>1. \A m, n \in 1..Cardinality(A) : m < n => f[m] < f[n]
          BY <2>3
        <4>2. k \in 1..Cardinality(A) /\ pred_k \in 1..Cardinality(A)
          BY <2>1, <3>5, FS_CardinalityType
        <4>3. f[k] > f[pred_k]
          BY <2>1, <3>5, FS_CardinalityType DEF Bijection, Surjection
        <4>4. ~(f[k] < f[pred_k])
          BY <4>3, <2>1, <3>5, FS_CardinalityType DEF Bijection, Surjection
        <4>5. k < pred_k => f[k] < f[pred_k]
          BY <2>3, <4>2, <4>3
        <4>6. (k > pred_k)
          BY <4>4, <4>5, <2>1, <3>5, FS_CardinalityType DEF Bijection, Surjection
        <4> QED
          BY <4>6
      <3>7. \A y \in A : y \notin pred_cands => s < y
        BY <1>2, <2>1
      <3>8. \A k \in (pred_k+1)..Cardinality(A) : s < f[k]
        <4> SUFFICES ASSUME NEW k \in (pred_k+1)..Cardinality(A)
                     PROVE  s < f[k]
          OBVIOUS
        <4>1. f[k] \in Int /\ f[k] \in A
          BY <1>2, <2>1, FS_CardinalityType DEF Bijection, Surjection
        <4>2. \A y \in pred_cands : y < f[k]
          BY <2>3, <3>4, <3>5 DEF Bijection, Surjection
        <4>3. f[k] \notin pred_cands
          BY <4>2
        <4> QED
          BY <3>7, <4>1, <4>3
      <3> DEFINE g == [k \in 1..(Cardinality(A)+1) |-> CASE k \in 1..pred_k                      -> f[k]
                                                         [] k = pred_k+1                         -> s
                                                         [] k \in (pred_k+2)..(Cardinality(A)+1) -> f[k-1]]                   
      <3>9. \A m, n \in 1..(Cardinality(A)+1) : m < n => g[m] < g[n]
        BY <2>1, <2>3, <3>5, <3>6, <3>8, FS_CardinalityType
      <3>10. g \in [1..(Cardinality(A)+1) -> A \union {s}]
        BY <2>1, <2>3, FS_CardinalityType DEF Bijection, Injection, Surjection
      <3>11. g \in Injection(1..(Cardinality(A)+1), A \union {s})
        BY <1>2, <2>1, FS_CardinalityType DEF Bijection, Injection
      <3>12. g \in Surjection(1..(Cardinality(A)+1), A \union {s})
        <4> SUFFICES ASSUME NEW b \in A \union {s}
                     PROVE  \E a \in 1..(Cardinality(A)+1) : g[a] = b
          BY <3>10, Fun_IsSurj, Zenon
        <4>1. CASE b = s
          BY <2>1, <4>1, FS_CardinalityType
        <4>2. CASE b \in A
          <5>1. PICK a \in 1..Cardinality(A) : f[a] = b
            BY <2>3, <4>2 DEF Bijection, Surjection
          <5>2. g[a+1] = f[a] \/ g[a] = f[a]
            BY <2>1, <5>1, FS_CardinalityType
          <5> QED
            BY <2>1, <5>1, <5>2, FS_CardinalityType
        <4> QED
          BY <4>1, <4>2
      <3>13. g \in Bijection(1..(Cardinality(A)+1), A \union {s})
        BY <3>11, <3>12, Zenon DEF Bijection
      <3> QED
        BY <1>2, <2>2, <3>9, <3>13, Zenon
    <2> QED
      BY <2>7, <2>8, <2>9, Zenon
  <1> HIDE DEF P
  <1>3. P(S)
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
  <1> QED
    BY <1>3, Zenon DEF P

=============================================================================
\* Modification History
\* Last modified Fri Oct 06 10:20:55 EDT 2023 by uguryavuz
\* Created Mon Oct 02 00:38:56 EDT 2023 by uguryavuz
