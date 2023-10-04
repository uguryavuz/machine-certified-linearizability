------------------------------------- MODULE HerlihyWingQueue -------------------------------------
EXTENDS Integers, Sequences, FiniteSets, FiniteSetTheorems, Functions, FunctionTheorems, TLC, TLAPS

CONSTANTS ACK, BOT
VARIABLES pc, L, Q, i, j, l, x, v, M
vars == <<pc, L, Q, i, j, l, x, v, M>>

ASSUME AckBotDef == /\ ACK \notin Nat
                    /\ BOT \notin Nat
                    /\ ACK /= BOT

\* Useful definitions

PosInts == Nat \ {0}
ProcSet == Nat \ {0}

\* Set of all permutations of items of S.
Perm(S) == {f \in [1..Cardinality(S) -> S] : \A w \in S : \E q \in 1..Cardinality(S) : f[q] = w}

\* Lemmas useful for proof of correctness

\* Used at many places in the proof.
LEMMA PermLength == \A S : IsFiniteSet(S) => (\A pi \in Perm(S) : Cardinality(S) = Len(pi))
  BY FS_CardinalityType DEF Perm, Len

\* Needed at many places in the proof.
LEMMA PermDistinct == \A S : IsFiniteSet(S) => (\A pi \in Perm(S) : \A k, m \in DOMAIN pi : k # m => pi[k] # pi[m])
  <1> SUFFICES ASSUME NEW S, IsFiniteSet(S),
                      NEW pi \in Perm(S),
                      NEW k \in DOMAIN pi, NEW m \in DOMAIN pi,
                      k # m, pi[k] = pi[m]
               PROVE  FALSE
    BY Zenon
  <1> DEFINE pi_ == [s \in (1..Cardinality(S)) \ {m} |-> pi[s]]
  <1>1. pi_ \in Surjection(1..Cardinality(S) \ {m}, S)
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

\* Needed for the well ordering principle
LEMMA MaxElement == \A S : (S \in SUBSET Int /\ S # {} /\ IsFiniteSet(S)) => \E s \in S : (\A y \in S : y <= s)
  <1> SUFFICES ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
               PROVE  \E s \in S : (\A y \in S : y <= s)
    OBVIOUS
  <1> DEFINE P(A) == (A \in SUBSET Int /\ A # {} /\ IsFiniteSet(A)) => \E s \in A : (\A y \in A : y <= s)
  <1>1. P({})
    OBVIOUS
  <1>2. ASSUME NEW A, NEW s, P(A), s \notin A
               PROVE P(A \cup {s})
    <2> SUFFICES ASSUME A \cup {s} \in SUBSET Int,
                        A \cup {s} # {}, IsFiniteSet(A \cup {s})
                 PROVE P(A \cup {s})
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
    
\* Needed to prove Inv => (M # {})
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
               PROVE P(A \cup {s})
    <2> SUFFICES ASSUME A \cup {s} \in SUBSET Int,
                        IsFiniteSet(A \cup {s})
                 PROVE  P(A \cup {s})
      BY Zenon
    <2>1. A \in SUBSET Int /\ IsFiniteSet(A)
      BY FS_Subset
    <2>2. Cardinality(A \cup {s}) = Cardinality(A)+1
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
      
      <3>2. g \in [1..(Cardinality(A)+1) -> A \cup {s}]
        BY <2>1, <2>3, FS_CardinalityType DEF Bijection, Injection, Surjection
      
      <3>3. g \in Injection(1..(Cardinality(A)+1), A \cup {s})
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
          
      <3>4. g \in Surjection(1..(Cardinality(A)+1), A \cup {s})
        <4> SUFFICES ASSUME NEW b \in A \cup {s}
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
        
      <3>5. g \in Bijection(1..(Cardinality(A)+1), A \cup {s})
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
      
      <3>2. g \in [1..(Cardinality(A)+1) -> A \cup {s}]
        BY <2>1, <2>3, FS_CardinalityType DEF Bijection, Injection, Surjection
        
      <3>3. g \in Injection(1..(Cardinality(A)+1), A \cup {s})
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
          
      <3>4. g \in Surjection(1..(Cardinality(A)+1), A \cup {s})
        <4> SUFFICES ASSUME NEW b \in A \cup {s}
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
      
      <3>5. g \in Bijection(1..(Cardinality(A)+1), A \cup {s})
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
\*        <4> SUFFICES ASSUME NEW m \in 1..(Cardinality(A)+1), 
\*                            NEW n \in 1..(Cardinality(A)+1), m < n
\*                     PROVE  g[m] < g[n]
\*          OBVIOUS
\*        <4>1. CASE m \in 1..pred_k /\ n \in 1..pred_k
\*          BY <2>1, <2>3, <3>5, <4>1, FS_CardinalityType
\*        <4>2. CASE m \in 1..pred_k /\ n = pred_k+1
\*          BY <2>1, <3>6, <4>2, FS_CardinalityType
\*        <4>3. CASE m \in 1..pred_k /\ n \in (pred_k+2)..(Cardinality(A)+1)
\*          BY <2>1, <2>3, <3>5, <4>3, FS_CardinalityType
\*        <4>4. CASE m = pred_k+1 /\ n \in (pred_k+2)..(Cardinality(A)+1)
\*          BY <2>1, <3>8, <4>4, FS_CardinalityType
\*        <4>5. CASE m \in (pred_k+2)..(Cardinality(A)+1) /\ n \in (pred_k+2)..(Cardinality(A)+1)
\*          BY <2>1, <2>3, <3>5, <4>5, FS_CardinalityType
\*        <4> QED
\*          BY <2>1, <3>5, <4>1, <4>2, <4>3, <4>4, <4>5, FS_CardinalityType

      <3>10. g \in [1..(Cardinality(A)+1) -> A \cup {s}]
        BY <2>1, <2>3, FS_CardinalityType DEF Bijection, Injection, Surjection
        
      <3>11. g \in Injection(1..(Cardinality(A)+1), A \cup {s})
        BY <1>2, <2>1, FS_CardinalityType DEF Bijection, Injection
\*        <4> SUFFICES ASSUME NEW a \in 1..(Cardinality(A)+1),
\*                            NEW b \in 1..(Cardinality(A)+1),
\*                            g[a] = g[b]
\*                     PROVE  a = b
\*          BY <3>10, Fun_IsInj, Zenon
\*        <4>1. CASE a \in 1..pred_k /\ b \in 1..pred_k
\*          BY <2>1, <4>1, FS_CardinalityType DEF Bijection, Injection
\*        <4>2. CASE a \in 1..pred_k /\ b = pred_k+1
\*          BY <1>2, <2>1, <4>2, FS_CardinalityType DEF Bijection, Injection
\*        <4>3. CASE a \in 1..pred_k /\ b \in (pred_k+2)..(Cardinality(A)+1)
\*          BY <2>1, <4>3, FS_CardinalityType DEF Bijection, Injection
\*        <4>4. CASE a = pred_k+1 /\ b \in 1..pred_k
\*          BY <1>2, <2>1, <4>4, FS_CardinalityType DEF Bijection, Injection
\*        <4>6. CASE a = pred_k+1 /\ b \in (pred_k+2)..(Cardinality(A)+1)
\*          BY <1>2, <2>1, <4>6, FS_CardinalityType DEF Bijection, Injection
\*        <4>7. CASE a \in (pred_k+2)..(Cardinality(A)+1) /\ b \in 1..pred_k
\*          BY <2>1, <4>7, FS_CardinalityType DEF Bijection, Injection
\*        <4>8. CASE a \in (pred_k+2)..(Cardinality(A)+1) /\ b = pred_k+1
\*          BY <1>2, <2>1, <4>8, FS_CardinalityType DEF Bijection, Injection
\*        <4>9. CASE a \in (pred_k+2)..(Cardinality(A)+1) /\ b \in (pred_k+2)..(Cardinality(A)+1)
\*          BY <2>1, <4>9, FS_CardinalityType DEF Bijection, Injection
\*        <4> QED
\*          BY <2>1, <3>5, <4>1, <4>2, <4>3, <4>4, <4>6, <4>7, <4>8, <4>9, FS_CardinalityType
        
          
      <3>12. g \in Surjection(1..(Cardinality(A)+1), A \cup {s})
        <4> SUFFICES ASSUME NEW b \in A \cup {s}
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
      
      <3>13. g \in Bijection(1..(Cardinality(A)+1), A \cup {s})
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
  
\* Set of all sequences containing items from S.
\* Originally implemented in Sequences.
Seqs(S) == UNION {[1..n -> S] : n \in Nat}

\* Redefined Tail and Head
Hd(s) == IF s # << >> THEN s[1] ELSE BOT
Tl(s) == [k \in 1..(Len(s)-1) |-> s[k+1]]

\* Domain of all tuples: state is a sequence of naturals, 
\*                       response is a natural, ACK, or BOT for each process.
TupleDomain == [state : Seqs(Nat), 
                res   : [ProcSet -> Nat \union {ACK, BOT}]]

\* Set of unlinearized enqueues (i.e. no response at line 2, 3) given a linearization tuple t.
UnlinearizedEnqs(t) == {q \in ProcSet : pc[q] \in {2, 3} /\ t.res[q] = BOT}

\* Set of linearization tuples after process p returns r. 
\* (Filter non-r responses, and reset the response field).
Filter(p, r) == {u \in TupleDomain : \E t \in M : /\ t.res[p] = r
                                                  /\ u.state = t.state
                                                  /\ u.res[p] = BOT
                                                  /\ \A q \in ProcSet : q /= p =>  u.res[q] = t.res[q]}

\* Concatenation to sequence
Concat(s1, s2) == [k \in 1..(Len(s1)+Len(s2)) |-> IF k \leq Len(s1) 
                                                     THEN s1[k] 
                                                     ELSE s2[k-Len(s1)]]

\* Algorithm and invariants

\* Define a (response-wise) well-formed tuple
tTypeOK(t) == /\ \A p \in ProcSet : /\ pc[p] \in {0, 1, 4, 5, 6}  => t.res[p] = BOT
                                    /\ pc[p] \in {2, 3}           => t.res[p] \in {ACK, BOT}
                                    /\ pc[p] = 7                  => t.res[p] \in Nat \union {BOT}

TypeOK == /\ pc \in [ProcSet -> 0..7]
          /\ L  \in PosInts
          /\ Q  \in [PosInts -> PosInts \union {BOT}]
          \* Q must be empty starting at and past L
          /\ \A k \in PosInts : k > L - 1 => Q[k] = BOT
          /\ i  \in [ProcSet -> PosInts] 
          /\ j  \in [ProcSet -> PosInts]
          /\ l  \in [ProcSet -> PosInts]
          /\ x  \in [ProcSet -> PosInts \union {BOT}]
          /\ v  \in [ProcSet -> PosInts]
          /\ M  \in SUBSET {t \in TupleDomain : tTypeOK(t)}
          
Init   == /\ pc = [p \in ProcSet |-> 0]
          /\ L  = 1
          /\ Q  = [idx \in PosInts |-> BOT]
          /\ i  \in [ProcSet -> PosInts]
          /\ j  \in [ProcSet -> PosInts]
          /\ l  \in [ProcSet -> PosInts]
          /\ x  \in [ProcSet -> PosInts \union {BOT}]
          /\ v  \in [ProcSet -> PosInts]
          /\ M  = {[state |-> <<>>,
                    res   |-> [p \in ProcSet |-> BOT]]}
                    
L00(p) == /\ pc[p] = 0
          /\ \E new_ln \in {1, 4} : /\ pc' = [pc EXCEPT ![p] = new_ln]
                                    /\ CASE new_ln = 1 -> \E new_v \in PosInts : v' = [v EXCEPT ![p] = new_v]
                                         [] new_ln = 4 -> v' = v
          /\ UNCHANGED <<L, Q, i, j, l, x, M>>
          
L01(p) == /\ pc[p] = 1
          /\ pc' = [pc EXCEPT ![p] = 2]
          /\ i'  = [i  EXCEPT ![p] = L]
          /\ L'  = L + 1
          /\ UNCHANGED <<Q, j, l, x, v>>
          /\ M'  = {u \in TupleDomain : 
                      /\ tTypeOK(u)'
                      /\ \E t \in M : 
                            \E S \in SUBSET UnlinearizedEnqs(t)' : 
                               \E seq \in Perm(S) : 
                                  /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                                  /\ \A q \in ProcSet : IF q \in S 
                                                           THEN u.res[q] = ACK
                                                           ELSE u.res[q] = t.res[q]}
                                                        
L02(p) == /\ pc[p] = 2
          /\ pc' = [pc EXCEPT ![p] = 3]
          /\ Q'  = [Q  EXCEPT ![i[p]] = v[p]]
          /\ UNCHANGED <<L, i, j, l, x, v, M>>
          
L03(p) == /\ pc[p] = 3
          /\ pc' = [pc EXCEPT ![p] = 0]
          /\ M'  = Filter(p, ACK)
          /\ UNCHANGED <<L, Q, i, j, l, x, v>>
          
L04(p) == /\ pc[p] = 4
          /\ pc' = [pc EXCEPT ![p] = 5]
          /\ l'  = [l  EXCEPT ![p] = L]
          /\ UNCHANGED <<L, Q, i, j, x, v, M>>
          
L05(p) == /\ pc[p] = 5
          /\ IF l[p] = 1
                THEN /\ pc' = [pc EXCEPT ![p] = 4]
                     /\ j'  = j
                ELSE /\ pc' = [pc EXCEPT ![p] = 6]
                     /\ j'  = [j  EXCEPT ![p] = 1]
          /\ UNCHANGED <<L, Q, i, l, x, v, M>>
          
L06(p) == /\ pc[p] = 6
          /\ x' = [x EXCEPT ![p] = Q[j[p]]]
          /\ Q' = [Q EXCEPT ![j[p]] = BOT]
          /\ IF Q[j[p]] = BOT
                THEN IF j[p] = l[p] - 1
                        THEN /\ pc' = [pc EXCEPT ![p] = 4]
                             /\ UNCHANGED <<j, M>>
                        ELSE /\ j' = [j EXCEPT ![p] = j[p] + 1]
                             /\ UNCHANGED <<pc, M>>
                ELSE /\ pc' = [pc EXCEPT ![p] = 7]
                     /\ M' = {u \in TupleDomain :
                                 /\ tTypeOK(u)'
                                 /\ \E t \in M :
                                    /\ u.state  = Tl(t.state)
                                    /\ u.res[p] = Hd(t.state)
                                    /\ \A q \in ProcSet : q /= p => u.res[q] = t.res[q]}
                     /\ j' = j
          /\ UNCHANGED <<L, i, l, v>>

L07(p) == /\ pc[p] = 7
          /\ pc' = [pc EXCEPT ![p] = 0]
          /\ M'  = Filter(p, x[p])
          /\ UNCHANGED <<L, Q, i, j, l, x, v>>


Next == \E p \in ProcSet : \/ L00(p) 
                           \/ L01(p)
                           \/ L02(p)
                           \/ L03(p)
                           \/ L04(p)
                           \/ L05(p)
                           \/ L06(p)
                           \/ L07(p)
                           
Spec == /\ Init
        /\ [][Next]_vars
          
\* Invariants
InvL0 == \A p \in ProcSet : pc[p] = 0 => \A t \in M : t.res[p] = BOT

InvL1 == \A p \in ProcSet : pc[p] = 1 => \A t \in M : t.res[p] = BOT

InvL2 == \A p \in ProcSet : pc[p] = 2 => /\ 1 <= i[p] 
                                         /\ i[p] < L
                                         /\ Q[i[p]] = BOT
                                         /\ \A q \in ProcSet : (pc[q] \in {2, 3} /\ q /= p) => i[q] /= i[p]

InvL3 == \A p \in ProcSet : pc[p] = 3 => /\ 1 <= i[p]
                                         /\ i[p] < L
                                         /\ \A q \in ProcSet : (pc[q] \in {2, 3} /\ q /= p) => i[q] /= i[p]

InvL4 == \A p \in ProcSet : pc[p] = 4 => \A t \in M : t.res[p] = BOT

InvL5 == \A p \in ProcSet : pc[p] = 5 => /\ \A t \in M : t.res[p] = BOT
                                         /\ 1 <= l[p]
                                         /\ l[p] <= L

InvL6 == \A p \in ProcSet : pc[p] = 6 => /\ \A t \in M : t.res[p] = BOT
                                         /\ 1 <= j[p]
                                         /\ j[p] < l[p]
                                         /\ l[p] <= L
                                         
\* Necessary predicates                                        
GoodEnqSet(A) == \A k \in 1..(L-1) : /\ Q[k] /= BOT => k \in A
                                     /\ (k \in A /\ Q[k] = BOT) => \E q \in ProcSet : /\ pc[q] = 2 
                                                                                      /\ i[q] = k

ValuesMatchInds(seq, state) == state = [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                               [] OTHER            -> v[CHOOSE q \in ProcSet : /\ pc[q] = 2 
                                                                                                               /\ i[q] = seq[k]]]

GoodRes(A, res) == \A q \in ProcSet : res[q] = CASE (pc[q] = 2 /\ i[q] \in A) -> ACK
                                                 [] (pc[q] = 3)               -> ACK
                                                 [] (pc[q] = 7)               -> x[q]
                                                 [] OTHER                     -> BOT
                        
JInvSeq(seq) == \A m, n \in 1..Len(seq) : (/\ n < m
                                           /\ seq[n] > seq[m]
                                           /\ Q[seq[m]] # BOT)
                                              => \E p \in ProcSet : /\ pc[p] = 6
                                                                    /\ seq[n] < l[p]
                                                                    /\ seq[m] < j[p]
                                                                    
InvS1 == \A A \in SUBSET (1..(L-1)) : GoodEnqSet(A) => \A seq \in Perm(A) : (JInvSeq(seq) => (\E t \in M : /\ ValuesMatchInds(seq, t.state)
                                                                                                           /\ GoodRes(A, t.res)))
             
\* Inductive inv
Inv == /\ TypeOK
       /\ InvL0
       /\ InvL1
       /\ InvL2
       /\ InvL3
       /\ InvL4
       /\ InvL5
       /\ InvL6
       /\ InvS1

\* The proof                     
THEOREM InductiveInvariance == Spec => []Inv
<1> USE DEF PosInts, ProcSet
<1> SUFFICES /\ (Init => Inv)
             /\ (Inv /\ [Next]_vars => Inv')
  BY PTL DEF Spec
<1>1. Init => Inv
  <2> USE DEF Init
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    <3>1. M  \in SUBSET {t \in TupleDomain : tTypeOK(t)}
      <4> DEFINE t == [state |-> <<>>, res |-> [p \in ProcSet |-> BOT]]
      <4>1. t.state \in [1..0 -> Nat]
        OBVIOUS
      <4>2. t.state \in Seqs(Nat)
        BY <4>1, Zenon DEF Seqs
      <4> QED
        BY <4>2 DEF TupleDomain, tTypeOK
    <3>11. QED
      BY <3>1 DEF TypeOK
  <2>2. InvS1
    <3> SUFFICES ASSUME NEW A \in SUBSET (1..(L-1)),
                        GoodEnqSet(A),
                        NEW seq \in Perm(A),
                        JInvSeq(seq)
                 PROVE  \E t \in M : /\ ValuesMatchInds(seq, t.state)
                                     /\ GoodRes(A, t.res)
      BY DEF InvS1
    <3>1. A = {}
      BY DEF GoodEnqSet
    <3>2. Cardinality(A) = 0
      BY <3>1, Zenon DEF Cardinality
    <3>3. seq = <<>>
      BY <3>1, <3>2 DEF Perm, JInvSeq
    <3> QED
      BY <3>1, <3>3 DEF ValuesMatchInds, GoodRes
  <2>3. QED
    BY <2>1, <2>2 DEF Inv, InvL0, InvL1, InvL2, InvL3, InvL4, InvL5, InvL6
<1>2. Inv /\ [Next]_vars => Inv'
  <2> USE DEF Next, vars, Inv
  <2> SUFFICES ASSUME Inv /\ [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. TypeOK'
    <3> USE DEF TypeOK, TupleDomain, tTypeOK, Seqs 
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  TypeOK'
      <4> USE <3>1 DEF L00
      <4>1. (v \in [ProcSet -> PosInts])'
        <5> SUFFICES ASSUME NEW new_ln \in {1, 4},
                            pc' = [pc EXCEPT ![p] = new_ln]
                     PROVE  (v  \in [ProcSet -> PosInts])'
          BY Zenon
        <5>1. CASE new_ln = 1
          BY <5>1
        <5>2. CASE new_ln = 4
          BY <5>2
        <5>3. QED
          BY <5>1, <5>2
      <4>2. (M \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        <5>1. TupleDomain = TupleDomain'
          OBVIOUS
        <5>2. \A t \in TupleDomain : tTypeOK(t) = tTypeOK(t)'
          OBVIOUS
        <5>3. QED
          BY <5>1, <5>2, Zenon
      <4> QED
        BY <4>1, <4>2
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  TypeOK'
      <4> USE <3>2 DEF L01
      <4>1. (pc \in [ProcSet -> 0..7])'
        OBVIOUS
      <4>2. (L  \in PosInts)'
        OBVIOUS
      <4>3. (Q  \in [PosInts -> PosInts \union {BOT}])'
        OBVIOUS
      <4>4. (\A k \in PosInts : k > L - 1 => Q[k] = BOT)'
        OBVIOUS
      <4>5. (i  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>6. (j  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>7. (l  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>8. (x  \in [ProcSet -> PosInts \union {BOT}])'
        OBVIOUS
      <4>9. (v  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>10. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        OBVIOUS
      <4> QED
        BY Isa, <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  TypeOK'
      <4> USE <3>3 DEF L02
      <4>1. (pc \in [ProcSet -> 0..7])'
        OBVIOUS
      <4>2. (L  \in PosInts)'
        OBVIOUS
      <4>3. (Q  \in [PosInts -> PosInts \union {BOT}])'
        OBVIOUS
      <4>4. (\A k \in PosInts : k > L - 1 => Q[k] = BOT)'
        BY DEF InvL2
      <4>5. (i  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>6. (j  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>7. (l  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>8. (x  \in [ProcSet -> PosInts \union {BOT}])'
        OBVIOUS
      <4>9. (v  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>10. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        OBVIOUS
      <4> QED
        BY Isa, <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9
    <3>4. ASSUME NEW p \in ProcSet,
                 L03(p)
          PROVE  TypeOK'
      <4> USE <3>4 DEF L03
      <4>1. (pc \in [ProcSet -> 0..7])'
        OBVIOUS
      <4>2. (\A k \in PosInts : k > L - 1 => Q[k] = BOT)'
        BY DEF InvL3
      <4>3. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        <5> SUFFICES ASSUME NEW u \in M'
            PROVE  /\ u \in TupleDomain'
                   /\ tTypeOK(u)'
          BY Zenon
        <5> USE DEF Filter
        <5>1. u \in TupleDomain'
          BY Zenon
        <5>2. PICK t \in M : /\ t.res[p] = ACK /\ u.state = t.state /\ u.res[p] = BOT
                             /\ \A q \in ProcSet : q /= p =>  u.res[q] = t.res[q]
          OBVIOUS
        <5>3. tTypeOK(t)
          OBVIOUS
        <5>4. tTypeOK(u)'
          BY <5>2, <5>3
        <5>5. QED
          BY <5>1, <5>4
      <4> QED
        BY <4>1, <4>2, <4>3, Zenon
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  TypeOK'
      <4> USE <3>5 DEF L04
      <4>1. (pc \in [ProcSet -> 0..7])'
        OBVIOUS
      <4>2. (l  \in [ProcSet -> PosInts])'
        OBVIOUS
      <4>3. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        BY Zenon
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  TypeOK'
      <4> USE <3>6 DEF L05
      <4>1. (pc \in [ProcSet -> 0..7])'
        <5>1. CASE l[p] = 1
          BY <5>1
        <5>2. CASE l[p] # 1
          BY <5>2
        <5> QED
          BY <5>1, <5>2
      <4>2. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        <5>1. TupleDomain = TupleDomain'
          OBVIOUS
        <5>2. \A t \in TupleDomain : tTypeOK(t) = tTypeOK(t)'
          <6> USE Zenon
          <6>1. CASE l[p] = 1
            BY <6>1
          <6>2. CASE l[p] # 1
            BY <6>2
          <6>3. QED
            BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>2      
      <4> QED
        BY Isa, <4>1, <4>2
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  TypeOK'
      <4> USE <3>7 DEF L06
      <4>1. (pc \in [ProcSet -> 0..7])'
        <5>1. CASE Q[j[p]] = BOT /\ j[p] = l[p] - 1
          OBVIOUS
        <5>2. CASE Q[j[p]] = BOT /\ j[p] # l[p] - 1
          OBVIOUS
        <5>3. CASE Q[j[p]] # BOT
          OBVIOUS
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4>2. (j  \in [ProcSet -> PosInts])'
        <5>1. CASE Q[j[p]] = BOT /\ j[p] = l[p] - 1
          OBVIOUS
        <5>2. CASE Q[j[p]] = BOT /\ j[p] # l[p] - 1
          OBVIOUS
        <5>3. CASE Q[j[p]] # BOT
          OBVIOUS
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4>3. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        <5>1. CASE Q[j[p]] = BOT /\ j[p] = l[p] - 1
          OBVIOUS
        <5>2. CASE Q[j[p]] = BOT /\ j[p] # l[p] - 1
          OBVIOUS
        <5>3. CASE Q[j[p]] # BOT
          OBVIOUS
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>8. ASSUME NEW p \in ProcSet,
                 L07(p)
          PROVE  TypeOK'
      <4> USE <3>8 DEF L07
      <4>1. (pc \in [ProcSet -> 0..7])'
        OBVIOUS
      <4>2. (\A k \in PosInts : k > L - 1 => Q[k] = BOT)'
        BY DEF InvL3
      <4>3. (M  \in SUBSET {t \in TupleDomain : tTypeOK(t)})'
        <5> SUFFICES ASSUME NEW u \in M'
            PROVE  /\ u \in TupleDomain'
                   /\ tTypeOK(u)'
          BY Zenon
        <5> USE DEF Filter
        <5>1. u \in TupleDomain'
          BY Zenon
        <5>2. PICK t \in M : /\ t.res[p] = x[p] /\ u.state = t.state /\ u.res[p] = BOT
                             /\ \A q \in ProcSet : q /= p =>  u.res[q] = t.res[q]
          OBVIOUS
        <5>3. tTypeOK(t)
          OBVIOUS
        <5>4. tTypeOK(u)'
          BY <5>2, <5>3
        <5>5. QED
          BY <5>1, <5>4
      <4> QED
        BY <4>1, <4>2, <4>3, Zenon
    <3>9. CASE UNCHANGED vars
      BY <3>9 
    <3>10. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
  <2>2. InvL0'
    <3> USE DEF InvL0
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL0'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL0'
      <4> USE <3>2 DEF L01, TypeOK
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 0,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        OBVIOUS
      <4>1. PICK t \in M : 
                   \E S \in SUBSET UnlinearizedEnqs(t)' : 
                      \E seq \in Perm(S) : 
                         /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                         /\ \A r \in ProcSet : IF r \in S 
                                                  THEN u.res[r] = ACK
                                                  ELSE u.res[r] = t.res[r]
        BY Zenon
      <4>2. PICK S \in SUBSET UnlinearizedEnqs(t)' : 
                    \E seq \in Perm(S) : 
                       /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                       /\ \A r \in ProcSet : IF r \in S 
                                                THEN u.res[r] = ACK
                                                ELSE u.res[r] = t.res[r]
        BY <4>1, Zenon
      <4>3. q \notin S
        BY <4>2 DEF UnlinearizedEnqs
      <4> QED
        BY <4>2, <4>3
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL0'
      BY <3>3 DEF L02
    <3>4. ASSUME NEW p \in ProcSet,
                 \/ L03(p)
                 \/ L07(p)
          PROVE  InvL0'
      <4> USE <3>4 DEF L03, L07
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 0,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        OBVIOUS
      <4>1. PICK t \in M : /\ u.state = t.state
                           /\ u.res[p] = BOT
                           /\ \A r \in ProcSet : r /= p => u.res[r] = t.res[r]
        BY DEF Filter
      <4> QED
        <5>1. CASE pc[p] = 3
          BY <4>1, <5>1 DEF TypeOK, tTypeOK
        <5>2. CASE pc[p] = 7
          BY <4>1, <5>2 DEF TypeOK, tTypeOK
        <5> QED
          BY <5>1, <5>2
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL0'
      BY <3>5 DEF L04, TypeOK
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL0'
      <4> USE <3>6 DEF L05
      <4>1. \A q \in ProcSet : p /= q => pc'[q] = pc[q]
        BY Zenon DEF TypeOK
      <4>2. pc'[p] /= 0
        BY Isa DEF TypeOK
      <4> QED
        BY <4>1, <4>2
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL0'
      <4> USE <3>7 DEF L06
      <4>1. \A q \in ProcSet : p /= q => pc'[q] = pc[q]
        BY DEF TypeOK
      <4>2. pc'[p] /= 0
        BY Isa DEF TypeOK
      <4> QED
        BY <4>1, <4>2
    <3>9. CASE UNCHANGED vars
      BY <3>9
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>9
  <2>3. InvL1'
    <3> USE DEF InvL1
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL1'
      BY <3>1 DEF L00, InvL0
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL1'
      <4> USE <3>2 DEF L01, TypeOK
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 1,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        BY Zenon
      <4>1. PICK t \in M : 
                   \E S \in SUBSET UnlinearizedEnqs(t)' : 
                      \E seq \in Perm(S) : 
                         /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                         /\ \A r \in ProcSet : IF r \in S 
                                                  THEN u.res[r] = ACK
                                                  ELSE u.res[r] = t.res[r]
        BY Zenon
      <4>2. PICK S \in SUBSET UnlinearizedEnqs(t)' : 
                    \E seq \in Perm(S) : 
                       /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                       /\ \A r \in ProcSet : IF r \in S 
                                                THEN u.res[r] = ACK
                                                ELSE u.res[r] = t.res[r]
        BY <4>1, Zenon
      <4>3. q \notin S
        BY <4>2 DEF UnlinearizedEnqs
      <4> QED
        BY <4>2, <4>3
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL1'
      BY <3>3 DEF L02
    <3>4. ASSUME NEW p \in ProcSet,
                 \/ L03(p)
                 \/ L07(p)
          PROVE  InvL1'
      <4> USE <3>4 DEF L03, L07
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 1,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        OBVIOUS
      <4>1. PICK t \in M : /\ u.state = t.state
                           /\ u.res[p] = BOT
                           /\ \A r \in ProcSet : r /= p => u.res[r] = t.res[r]
        BY DEF Filter
      <4> QED
        <5>1. CASE pc[p] = 3
          BY <4>1, <5>1 DEF TypeOK, tTypeOK
        <5>2. CASE pc[p] = 7
          BY <4>1, <5>2 DEF TypeOK, tTypeOK
        <5> QED
          BY <5>1, <5>2
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL1'
      BY <3>5 DEF L04
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL1'
      <4> USE <3>6 DEF L05
      <4>1. \A q \in ProcSet : p /= q => pc'[q] = pc[q]
        BY Zenon DEF TypeOK
      <4>2. pc'[p] /= 1
        BY Isa DEF TypeOK
      <4> QED
        BY <4>1, <4>2
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL1'
      <4> USE <3>7 DEF L06
      <4>1. \A q \in ProcSet : p /= q => pc'[q] = pc[q]
        BY Zenon DEF TypeOK
      <4>2. pc'[p] /= 1
        BY Isa DEF TypeOK
      <4> QED
        BY <4>1, <4>2
    <3>9. CASE UNCHANGED vars
      BY <3>9
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>9
  <2>4. InvL2'
    <3> USE DEF InvL2
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL2'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL2'
      <4> USE <3>2 DEF L01
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 2
                   PROVE  /\ 1 <= i'[q] /\ i'[q] < L' /\ Q'[i'[q]] = BOT
                          /\ \A r \in ProcSet : pc'[r] \in {2, 3} /\ r /= q => i'[r] /= i'[q]
          OBVIOUS
      <4>1. 1 <= i'[q]
        BY DEF TypeOK
      <4>2. i'[q] < L'
        BY DEF TypeOK
      <4>3. Q'[i'[q]] = BOT
        BY DEF TypeOK
      <4>4. \A r \in ProcSet : pc'[r] \in {2, 3} /\ r /= q => i'[r] /= i'[q]
        <5> SUFFICES ASSUME NEW r \in ProcSet,
                            pc'[r] \in {2, 3} /\ r /= q
                     PROVE  i'[r] /= i'[q]
          OBVIOUS
        <5>1. CASE q /= p /\ r /= p
          BY <5>1 DEF TypeOK
        <5>2. CASE q = p \/ r = p
          <6> USE <5>2
          <6>1. PICK s \in {q, r} : s /= p
            OBVIOUS
          <6>2. i[s] < L
            BY <6>1 DEF TypeOK, InvL3  
          <6>3. QED
            BY <6>1, <6>2 DEF TypeOK
        <5> QED
          BY <5>1, <5>2
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL2'
      BY <3>3 DEF L02, TypeOK
    <3>4. ASSUME NEW p \in ProcSet,
                 L03(p)
          PROVE  InvL2'
      BY <3>4 DEF L03
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL2'
      BY <3>5 DEF L04
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL2'
      <4> USE <3>6 DEF L05
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 2
                   PROVE  /\ 1 <= i'[q] /\ i'[q] < L' /\ Q'[i'[q]] = BOT
                          /\ \A r \in ProcSet : pc'[r] \in {2, 3} /\ r /= q => i'[r] /= i'[q]
        OBVIOUS
      <4>1. q /= p
        BY Isa DEF TypeOK
      <4> USE <4>1
      <4>2. 1 <= i'[q]
        BY DEF TypeOK
      <4>3. i'[q] < L'
        BY Zenon DEF TypeOK
      <4>4. Q'[i'[q]] = BOT
        BY Zenon DEF TypeOK
      <4>5. \A r \in ProcSet : pc'[r] \in {2, 3} /\ r /= q => i'[r] /= i'[q]
        <5> SUFFICES ASSUME NEW r \in ProcSet,
                            pc'[r] \in {2, 3} /\ r /= q
                     PROVE  i'[r] /= i'[q]
          OBVIOUS
        <5>1. i'[r] = i[r]
          OBVIOUS
        <5>2. i'[q] = i[q]
          OBVIOUS
        <5>3. r /= p
          BY Isa DEF TypeOK
        <5>4. pc'[r] = pc[r] /\ pc'[q] = pc[q]
          BY <5>3, Isa DEF TypeOK
        <5>5. i[r] /= i[q]
          BY <5>4 DEF TypeOK
        <5>6. QED
          BY <5>1, <5>2, <5>5
      <4>6. QED
        BY <4>2, <4>3, <4>4, <4>5
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL2'
      <4> USE <3>7 DEF L06
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 2
                   PROVE /\ 1 <= i'[q] /\ i'[q] < L' /\ Q'[i'[q]] = BOT
                         /\ \A r \in ProcSet : pc'[r] \in {2, 3} /\ r /= q => i'[r] /= i'[q]
        OBVIOUS
      <4>1. q /= p
        BY Isa DEF TypeOK
      <4> USE <4>1
      <4>2. 1 <= i'[q]
        BY DEF TypeOK
      <4>3. i'[q] < L'
        BY Zenon DEF TypeOK
      <4>4. Q'[i'[q]] = BOT
        BY Zenon DEF TypeOK
      <4>5. \A r \in ProcSet : pc'[r] \in {2, 3} /\ r /= q => i'[r] /= i'[q]
        <5> SUFFICES ASSUME NEW r \in ProcSet,
                            pc'[r] \in {2, 3} /\ r /= q
                     PROVE  i'[r] /= i'[q]
          OBVIOUS
        <5>1. i'[r] = i[r]
          OBVIOUS
        <5>2. i'[q] = i[q]
          OBVIOUS
        <5>3. r /= p
          BY Isa DEF TypeOK
        <5>4. pc'[r] = pc[r] /\ pc'[q] = pc[q]
          BY <5>3 DEF TypeOK
        <5>5. i[r] /= i[q]
          BY <5>4 DEF TypeOK
        <5>6. QED
          BY <5>1, <5>2, <5>5
      <4>6. QED
        BY <4>2, <4>3, <4>4, <4>5
    <3>8. ASSUME NEW p \in ProcSet,
                 L07(p)
          PROVE  InvL2'
      BY <3>8 DEF L07
    <3>9. CASE UNCHANGED vars
      BY <3>9
    <3>10. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
  <2>5. InvL3'
    <3> USE DEF InvL3
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL3'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL3'
      BY <3>2 DEF L01, TypeOK
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL3'
      BY <3>3 DEF L02, TypeOK, InvL2
    <3>4. ASSUME NEW p \in ProcSet,
                 L03(p)
          PROVE  InvL3'
      BY <3>4 DEF L03
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL3'
      BY <3>5 DEF L04
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL3'
      <4> USE <3>6 DEF L05
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 3
                   PROVE  /\ 1 <= i'[q] /\ i'[q] < L'
                          /\ \A r \in ProcSet : (pc'[r] \in {2, 3} /\ r /= q) => i'[r] /= i'[q]
        OBVIOUS
      <4>1. pc[q] = 3
        BY Isa DEF TypeOK
      <4>2. \A r \in ProcSet : pc'[r] \in {2, 3} => pc'[r] = pc[r]
        BY Isa DEF TypeOK
      <4> QED
        BY <4>1, <4>2
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL3'
      <4> USE <3>7 DEF L06
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 3
                   PROVE  /\ 1 <= i'[q] /\ i'[q] < L'
                          /\ \A r \in ProcSet : (pc'[r] \in {2, 3} /\ r /= q) => i'[r] /= i'[q]
        OBVIOUS
      <4>1. pc[q] = 3
        BY Isa DEF TypeOK
      <4>2. \A r \in ProcSet : pc'[r] \in {2, 3} => pc'[r] = pc[r]
        BY Isa DEF TypeOK
      <4> QED
        BY <4>1, <4>2
    <3>8. ASSUME NEW p \in ProcSet,
                 L07(p)
          PROVE  InvL3'
      BY <3>8 DEF L07
    <3>9. CASE UNCHANGED vars
      BY <3>9
    <3>10. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
  <2>6. InvL4'
    <3> USE DEF InvL4
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL4'
      BY <3>1 DEF L00, InvL0
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL4'
      <4> USE <3>2 DEF L01, TypeOK
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 4,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        BY Zenon
      <4>1. PICK t \in M : 
                   \E S \in SUBSET UnlinearizedEnqs(t)' : 
                      \E seq \in Perm(S) : 
                         /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                         /\ \A r \in ProcSet : IF r \in S 
                                                  THEN u.res[r] = ACK
                                                  ELSE u.res[r] = t.res[r]
        BY Zenon
      <4>2. PICK S \in SUBSET UnlinearizedEnqs(t)' : 
                    \E seq \in Perm(S) : 
                       /\ u.state = Concat(t.state, [k \in DOMAIN seq |-> v[seq[k]]])
                       /\ \A r \in ProcSet : IF r \in S 
                                                THEN u.res[r] = ACK
                                                ELSE u.res[r] = t.res[r]
        BY <4>1, Zenon
      <4>3. q \notin S
        BY <4>2 DEF UnlinearizedEnqs
      <4> QED
        BY <4>2, <4>3
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL4'
      BY <3>3 DEF L02
    <3>4. ASSUME NEW p \in ProcSet,
                 \/ L03(p)
                 \/ L07(p)
          PROVE  InvL4'
     <4> USE <3>4 DEF L03, L07
     <4> SUFFICES ASSUME NEW q \in ProcSet,
                         pc'[q] = 4,
                         NEW u \in M'
                  PROVE  u.res[q] = BOT
       OBVIOUS
     <4>1. PICK t \in M : /\ u.state = t.state
                          /\ u.res[p] = BOT
                          /\ \A r \in ProcSet : r /= p => u.res[r] = t.res[r]
       BY DEF Filter
     <4> QED
      <5>1. CASE pc[p] = 3
        BY <4>1, <5>1 DEF TypeOK, tTypeOK
      <5>2. CASE pc[p] = 7
        BY <4>1, <5>2 DEF TypeOK, tTypeOK
      <5> QED
        BY <5>1, <5>2
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL4'
      BY <3>5 DEF L04
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL4'
      BY <3>6, Zenon DEF L05, InvL5, TypeOK
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL4'
      <4> USE <3>7 DEF L06
      <4>1. CASE Q[j[p]] = BOT /\ j[p] = l[p] - 1
        BY <4>1 DEF InvL6, TypeOK
      <4>2. CASE Q[j[p]] = BOT /\ j[p] # l[p] - 1
        BY <4>2
      <4>3. CASE Q[j[p]] # BOT
        BY <4>3 DEF TypeOK
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>8. CASE UNCHANGED vars
      BY <3>8
    <3>9. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
  <2>7. InvL5'
    <3> USE DEF InvL5
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL5'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL5'
      BY <3>2 DEF L01, TypeOK, tTypeOK
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL5'
      BY <3>3 DEF L02
    <3>4. ASSUME NEW p \in ProcSet,
                 \/ L03(p)
                 \/ L07(p)
          PROVE  InvL5'
     <4> USE <3>4 DEF L03, L07
     <4>1. (\A q \in ProcSet : pc[q] = 5 => (1 <= l[q] /\ l[q] <= L))'
       <5>1. CASE pc[p] = 3
         BY <5>1 DEF TypeOK
       <5>2. CASE pc[p] = 7
         BY <5>2 DEF TypeOK
       <5> QED
         BY <5>1, <5>2
     <4> SUFFICES ASSUME NEW q \in ProcSet,
                         pc'[q] = 5,
                         NEW u \in M'
                  PROVE  u.res[q] = BOT
       BY <4>1
     <4>2. PICK t \in M : /\ u.state = t.state
                          /\ u.res[p] = BOT
                          /\ \A r \in ProcSet : r /= p => u.res[r] = t.res[r]
       BY DEF Filter
     <4> QED
       <5>1. CASE pc[p] = 3
         BY <4>2, <5>1 DEF TypeOK, tTypeOK
       <5>2. CASE pc[p] = 7
         BY <4>2, <5>2 DEF TypeOK, tTypeOK
       <5> QED
         BY <5>1, <5>2
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL5'
      BY <3>5 DEF L04, TypeOK, InvL4
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL5'
      BY <3>6, Zenon DEF L05, TypeOK
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL5'
      <4> USE <3>7 DEF L06, TypeOK
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 5
                   PROVE  /\ \A u \in M' : u.res[q] = BOT
                          /\ 1 <= l'[q]
                          /\ l'[q] <= L'
        OBVIOUS
      <4>1. p /= q /\ pc[q] = 5
        BY Isa DEF TypeOK
      <4> USE <4>1
      <4>2. 1 <= l'[q] /\ l'[q] <= L'
        OBVIOUS
      <4>3. \A u \in M' : u.res[q] = BOT
        BY DEF tTypeOK
      <4> QED
        BY <4>2, <4>3
    <3>8. CASE UNCHANGED vars
      BY <3>8
    <3>9. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
  <2>8. InvL6'
    <3> USE DEF InvL6
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvL6'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvL6'
      <4> SUFFICES ASSUME NEW q \in ProcSet',
                          (pc[q] = 6)'
                   PROVE  (/\ \A t \in M : t.res[q] = BOT
                           /\ 1 <= j[q]
                           /\ j[q] < l[q]
                           /\ l[q] <= L)'
        BY DEF InvL6
      <4>1. (\A t \in M : t.res[q] = BOT)'
        BY <3>2 DEF L01, InvL1, TypeOK, tTypeOK
      <4>2. (1 <= j[q])'
        BY <3>2 DEF L01, InvL1, TypeOK, tTypeOK
      <4>3. (j[q] < l[q])'
        BY <3>2 DEF L01, InvL1, TypeOK, tTypeOK
      <4>4. (l[q] <= L)'
        BY <3>2 DEF L01, InvL1, TypeOK, tTypeOK
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvL6'
      BY <3>3 DEF L02
    <3>4. ASSUME NEW p \in ProcSet,
                 \/ L03(p)
                 \/ L07(p)
          PROVE  InvL6'
      <4> USE <3>4 DEF L03, L07
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 6
                   PROVE  /\ \A t \in M' : t.res[q] = BOT
                          /\ (1 <= j[q] /\ j[q] < l[q] /\ l[q] <= L)'
        OBVIOUS
      <4>1. (1 <= j[q] /\ j[q] < l[q] /\ l[q] <= L)'
        <5>1. CASE pc[p] = 3
          BY <5>1 DEF TypeOK
        <5>2. CASE pc[p] = 7
          BY <5>2 DEF TypeOK
        <5> QED
          BY <5>1, <5>2
      <4>2. \A u \in M' : u.res[q] = BOT
        <5> SUFFICES ASSUME NEW u \in M'
                     PROVE  u.res[q] = BOT
          OBVIOUS
        <5>1. PICK t \in M : /\ u.state = t.state
                             /\ u.res[p] = BOT
                             /\ \A r \in ProcSet : r /= p => u.res[r] = t.res[r]
          BY DEF Filter
        <5> QED
          <6>1. CASE pc[p] = 3
            BY <5>1, <6>1 DEF TypeOK, tTypeOK
          <6>2. CASE pc[p] = 7
            BY <5>1, <6>2 DEF TypeOK, tTypeOK
          <6> QED
            BY <6>1, <6>2
      <4>3. QED
        BY <4>1, <4>2
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvL6'
      BY <3>5 DEF L04
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvL6'
      <4> SUFFICES ASSUME NEW q \in ProcSet',
                          (pc[q] = 6)'
                   PROVE  (/\ \A t \in M : t.res[q] = BOT
                           /\ 1 <= j[q]
                           /\ j[q] < l[q]
                           /\ l[q] <= L)'
        BY DEF InvL6
      <4>1. (\A t \in M : t.res[q] = BOT)'
        BY <3>6 DEF L05, InvL5, InvL6, TypeOK, tTypeOK
      <4>2. (1 <= j[q])'
        <5>1. CASE q = p
          BY <3>6, <5>1 DEF L05, InvL5, InvL6, TypeOK
        <5>2. CASE q # p
          BY <3>6, <5>2, Zenon DEF L05, InvL5, InvL6, TypeOK
        <5> QED
          BY <5>1, <5>2
      <4>3. (j[q] < l[q])'
        <5>1. CASE q = p
          BY <3>6, <5>1 DEF L05, InvL5, InvL6, TypeOK
        <5>2. CASE q # p
          BY <3>6, <5>2, Zenon DEF L05, InvL5, InvL6, TypeOK
        <5> QED
          BY <5>1, <5>2
      <4>4. (l[q] <= L)'
        BY <3>6 DEF L05, InvL5, InvL6, TypeOK, tTypeOK
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvL6'
      <4> USE <3>7 DEF L06, TypeOK
      <4> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] = 6
                   PROVE  /\ \A t \in M' : t.res[q] = BOT
                          /\ (1 <= j[q] /\ j[q] < l[q] /\ l[q] <= L)'
        OBVIOUS
      <4>0. CASE p # q
        <5> USE <4>0
        <5>1. CASE Q[j[p]] = BOT /\ j[p] = l[p] - 1
          BY <5>1
        <5>2. CASE Q[j[p]] = BOT /\ j[p] # l[p] - 1
          BY <5>2
        <5>3. CASE Q[j[p]] # BOT
          <6> USE <5>3
          <6>1. \A u \in M' : u.res[q] = BOT
            OBVIOUS
          <6>2. (1 <= j[q] /\ j[q] < l[q] /\ l[q] <= L)'
            OBVIOUS
          <6>3. QED
            BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>2, <5>3
      <4>1. CASE p = q
        <5> USE <4>1
        <5>1. CASE Q[j[p]] = BOT /\ j[p] = l[p] - 1
          BY <5>1
        <5>2. CASE Q[j[p]] = BOT /\ j[p] # l[p] - 1
          BY <5>2
        <5>3. CASE Q[j[p]] # BOT
          BY <5>3
        <5> QED
          BY <5>1, <5>2, <5>3
      <4> QED
        BY <4>0, <4>1
    <3>9. CASE UNCHANGED vars
      BY <3>9
    <3>10. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>9
  <2>9. InvS1'
    <3> USE DEF InvS1
    <3>1. ASSUME NEW p \in ProcSet,
                 L00(p)
          PROVE  InvS1'
      <4> USE <3>1 DEF L00
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. PICK t \in M : ValuesMatchInds(seq, t.state) /\ GoodRes(A, t.res)
        BY DEF GoodEnqSet, JInvSeq
      <4>2. GoodRes(A, t.res) = GoodRes(A, t.res)'
        BY DEF GoodRes
      <4>3. ValuesMatchInds(seq, t.state) = ValuesMatchInds(seq, t.state)'
        <5> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                    [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
        <5> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                    [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
        <5>1. vals1 = vals2
          <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                       PROVE  vals1[k] = vals2[k]
            BY Zenon
          <6>1. CASE Q[seq[k]] # BOT
            BY <6>1
          <6>2. CASE Q[seq[k]] = BOT
            <7> USE <6>2
            <7>1. seq[k] \in A
              BY DEF Perm
            <7>2. PICK r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]
              BY <7>1 DEF GoodEnqSet
            <7>3. \A r_ \in ProcSet : (pc[r_] = 2 /\ i[r_] = seq[k]) => r = r_
              BY <7>2 DEF InvL2
            <7>4. vals1[k] = v[r] /\ vals2[k] = v[r]'
              BY <7>2 DEF InvL2
            <7>5. r # p
              BY <7>2
            <7>6. v[r] = v[r]'
              BY <7>5, Isa DEF TypeOK
            <7>7. QED
              BY <7>4, <7>6
          <6>3. QED
            BY <6>1, <6>2
        <5>2. QED
          BY <5>1, Zenon DEF ValuesMatchInds
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>2. ASSUME NEW p \in ProcSet,
                 L01(p)
          PROVE  InvS1'
      <4> USE <3>2 DEF L01
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A)',
                          JInvSeq(seq)'
                   PROVE  \E u \in M' : /\ ValuesMatchInds(seq, u.state)'
                                        /\ GoodRes(A, u.res)'
        BY Zenon DEF TypeOK
      <4>1. i'[p] = L
        BY DEF TypeOK
      <4>2. CASE i'[p] \notin A
        <5> USE <4>2
        <5>1. pc'[p] = 2 /\ i'[p] \notin A
          BY DEF TypeOK
        <5>2. \A k \in 1..L : /\ Q[k] /= BOT => k \in A
                              /\ (k \in A /\ Q[k] = BOT) => \E r \in ProcSet : /\ pc'[r] = 2 
                                                                               /\ i'[r] = k
          BY DEF GoodEnqSet, TypeOK
        <5>3. GoodEnqSet(A)
          BY <5>1, <5>2 DEF TypeOK, GoodEnqSet
        <5>4. seq \in Perm(A)
          BY DEF Perm
        <5>5. JInvSeq(seq)
          BY DEF JInvSeq, TypeOK
        <5>6. A \in SUBSET 1..(L-1)
          BY DEF TypeOK
        <5>7. PICK t \in M : /\ ValuesMatchInds(seq, t.state)
                             /\ GoodRes(A, t.res)
          BY <5>3, <5>4, <5>5, <5>6
        <5> DEFINE S_ == {} 
        <5> DEFINE seq_ == << >>
        <5>8. t \in TupleDomain /\ tTypeOK(t)'
          BY <5>7 DEF TypeOK, TupleDomain, tTypeOK
        <5>9. S_ \in SUBSET UnlinearizedEnqs(t)' /\ seq_ \in Perm(S_)
          BY FS_EmptySet DEF Perm, UnlinearizedEnqs
        <5>10. t.state = Concat(t.state, [k \in DOMAIN seq_ |-> v[seq[k]]])
          <6> DEFINE s2 == [k \in DOMAIN seq_ |-> v[seq[k]]]
          <6>1. Concat(t.state, [k \in DOMAIN seq_ |-> v[seq[k]]]) = [k \in 1..Len(t.state) |-> t.state[k]]
            BY DEF Concat
          <6>2. DOMAIN t.state = 1..Len(t.state)
            BY <5>7 DEF TypeOK, TupleDomain, Seqs, Len
          <6>3. [k \in DOMAIN t.state |-> t.state[k]] = t.state
            BY DEF TypeOK, TupleDomain, Seqs
          <6>4. [k \in 1..Len(t.state) |-> t.state[k]] = t.state
            BY <6>2, <6>3
          <6> QED
            BY <6>1, <6>4
        <5>11. t \in M'
          BY <5>8, <5>9, <5>10
        <5>12. GoodRes(A, t.res)'
          BY <5>7 DEF GoodRes
        <5>13. ValuesMatchInds(seq, t.state) = ValuesMatchInds(seq, t.state)'
          <6> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                      [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
          <6> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                      [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
          <6>1. vals1 = vals2
            <7> HIDE <3>2
            <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE  vals1[k] = vals2[k]
              OBVIOUS
            <7> USE <3>2
            <7>1. CASE Q[seq[k]] = BOT
              <8> USE <7>1
              <8>1. seq[k] \in A
                BY DEF Perm
              <8>2. PICK r \in ProcSet : pc'[r] = 2 /\ i'[r] = seq[k]
                BY <8>1, Isa DEF GoodEnqSet
              <8>3. r # p
                BY <8>1, <8>2
              <8>4. \A q \in ProcSet : p # q => (pc[q] = pc'[q] /\ i[q] = i'[q])
                BY <3>2 DEF TypeOK
              <8>5. r \in ProcSet /\ pc[r] = 2 /\ i[r] = seq[k]
                BY <8>2, <8>3, <8>4
              <8>6. vals1[k] = v[r]
                BY <8>5 DEF InvL2
              <8>7. \A r_ \in ProcSet : (pc[r_] = 2 /\ i[r_] = seq[k]) <=> r = r_
                BY <8>5 DEF InvL2
              <8>8. \A r_ \in ProcSet : i'[r_] = seq[k] => r_ # p
                BY <5>1, <8>1 DEF TypeOK
              <8>9. \A r_ \in ProcSet : (i'[r_] = seq[k] /\ pc'[r_] = 2) <=> r = r_
                BY <8>8, <8>7
              <8>10. vals2[k] = v'[r]
                BY <8>2, <8>9
              <8> QED
                BY <8>6, <8>9 DEF TypeOK
            <7> QED
              BY <7>1
          <6> HIDE <3>2
          <6> QED
            BY <6>1, Zenon DEF ValuesMatchInds
        <5> HIDE <3>2 \* !!!!!!!!!!!!!!!!!!!!!
        <5> QED
          BY <5>7, <5>11, <5>12, <5>13
      <4>3. CASE i'[p] \in A
        <5> USE <4>3
        <5>1. IsFiniteSet(1..L)
          BY FS_Interval, Isa DEF TypeOK
        <5>2. IsFiniteSet(A)
          BY <5>1, FS_Subset, Isa DEF TypeOK
        <5>3. DOMAIN seq = 1..Cardinality(A)
          BY Isa DEF Perm
        <5>4. PICK k \in 1..Cardinality(A) : seq[k] = i'[p]
          BY <5>3, Isa DEF Perm
        <5>5. \A z \in k..Cardinality(A) : Q[seq[z]] = BOT
          <6>1. Q[i'[p]] = BOT
            BY DEF TypeOK
          <6> SUFFICES ASSUME \E z \in (k+1)..Cardinality(A) : Q[seq[z]] # BOT
                       PROVE  FALSE
            BY <5>4, <6>1
          <6>2. PICK z \in (k+1)..Cardinality(A) : Q[seq[z]] # BOT
            OBVIOUS
          <6>3. k < z
            OBVIOUS
          <6>4. seq[z] < seq[k]
            <7>1. seq \in Perm(A) /\ A \in SUBSET 1..L
              BY DEF TypeOK
            <7>2. seq[z] \in A
              BY DEF Perm
            <7>3. \A b \in A : b <= L
              BY <7>1
            <7>4. seq[z] <= L
              BY <7>2, <7>3, Isa
            <7>5. k # z
              BY <6>2
            <7>6. k \in DOMAIN seq /\ z \in DOMAIN seq
              BY <5>3, <5>4, <7>2
            <7>7. \A y, q \in DOMAIN seq : y # q => seq[y] # seq[q]
              BY PermDistinct, <5>2
            <7>8. seq[k] # seq[z]
              BY <7>6, <7>7, <5>2
            <7>11. L = seq[k]
              BY <5>4 DEF TypeOK
            <7> QED
              BY <7>4, <7>8, <7>11, Isa
          <6>5. Q'[seq[z]] # BOT
            BY <6>2
          <6>6. Cardinality(A) = Len(seq)
            BY <5>2, PermLength
          <6>7. PICK q \in ProcSet : pc'[q] = 6 /\ seq[k] < l'[q] /\ seq[z] < j'[q]
            BY <5>4, <6>2, <6>3, <6>4, <6>5, <6>6 DEF JInvSeq
          <6>8. l'[q] <= L
            BY <2>8, <6>7 DEF InvL6
          <6>9. seq[k] < L
            BY <5>4, <6>7, <6>8 DEF TypeOK
          <6> QED
            BY <5>4, <6>9 DEF TypeOK
        <5> DEFINE A_   == {seq[z] : z \in 1..(k-1)}    \* Set of indices
        <5> DEFINE seq_ == [z \in 1..(k-1) |-> seq[z]]  \* Sequence of indices
        <5>6. seq_ \in Perm(A_)
          <6>1. DOMAIN seq_ = 1..(k-1)
            OBVIOUS
          <6>2. Cardinality(A_) = k-1
            <7>1. seq_ \in Injection(1..(k-1), A_)
              <8> SUFFICES ASSUME NEW a \in 1..(k-1), NEW b \in 1..(k-1),
                                  seq_[a] = seq_[b]
                           PROVE  a = b
                BY DEF Injection
              <8>1. \A y \in 1..k-1 : y \in 1..Cardinality(A)
                BY <5>2, <5>4, FS_CardinalityType
              <8>2. a \in DOMAIN seq /\ b \in DOMAIN seq
                BY <5>3, <8>1
              <8>3. QED
                BY <5>2, <8>2, PermDistinct DEF Injection
            <7>2. seq_ \in Surjection(1..(k-1), A_)
              BY DEF Surjection
            <7>3. ExistsBijection(1..(k-1), A_)
              BY <7>1, <7>2 DEF Bijection, ExistsBijection
            <7> QED
              BY <5>4, <7>3, FS_CountingElements
          <6> QED
            BY <6>1, <6>2, Isa DEF Perm
        <5>7. GoodEnqSet(A_)
          <6> SUFFICES ASSUME NEW m \in 1..(L-1)
                       PROVE  /\ Q[m] # BOT => m \in A_
                              /\ (m \in A_ /\ Q[m] = BOT) => \E q \in ProcSet : (pc[q] = 2 /\ i[q] = m)
            BY DEF GoodEnqSet
          <6>1. CASE Q[m] # BOT
            <7> USE <6>1
            <7>1. m \in A
              BY DEF GoodEnqSet, TypeOK
            <7>2. PICK km \in 1..Cardinality(A) : seq[km] = m
              BY Isa, <7>1 DEF Perm
            <7>3. km \in 1..(k-1)
              BY <5>5, <7>2
            <7> QED
              BY <7>2, <7>3
          <6>2. CASE m \in A_ /\ Q[m] = BOT
            <7> USE <6>2
            <7>1. PICK km \in 1..(k-1) : seq[km] = m
              BY Isa DEF Perm
            <7>2. \A y \in 1..k-1 : y \in 1..Cardinality(A)
              BY <5>2, <5>4, FS_CardinalityType
            <7>3. km \in 1..Cardinality(A) => seq[km] \in A
              BY <7>1, Isa DEF Perm
            <7>4. m \in A
              BY <7>1, <7>2, <7>3, Isa
            <7>5. PICK q \in ProcSet : (pc'[q] = 2 /\ i'[q] = m)
              BY <7>4 DEF GoodEnqSet, TypeOK
            <7>6. p # q => pc[q] = 2 /\ i[q] = m
              BY <7>5 DEF TypeOK
            <7>7. k \in DOMAIN seq
              BY <5>3, <5>4
            <7>8. \A n \in DOMAIN seq : k # n => seq[k] # seq[n]
              BY <5>2, <7>7, PermDistinct
            <7>9. \A n \in 1..(k-1) : i'[p] # seq[n]
              BY <5>3, <5>4, <7>2, <7>8
            <7>10. i'[p] \notin A_
              BY <7>9
            <7>11. i'[p] # i'[q]
              BY <7>5, <7>10
            <7> QED
              BY <7>6, <7>11
          <6> QED
            BY <6>1, <6>2
        <5>8. JInvSeq(seq_)
          <6> SUFFICES ASSUME NEW m \in 1..Len(seq_), NEW n \in 1..Len(seq_),
                              /\ n < m
                              /\ seq_[n] > seq_[m]
                              /\ Q[seq_[m]] # BOT
                       PROVE  \E q \in ProcSet : (pc[q] = 6 /\ seq_[n] < l[q] /\ seq_[m] < j[q])
            BY DEF JInvSeq
          <6>1. \A a, b \in 1..Len(seq) : (b < a /\ seq[b] > seq[a] /\ Q'[seq[a]] # BOT)
                                             => (\E r \in ProcSet : (pc'[r] = 6 /\ seq[b] < l'[r] /\ seq[a] < j'[r]))
            BY DEF JInvSeq
          <6>2. \A y \in 1..Len(seq_) : y \in 1..Len(seq)
            BY <5>2, <5>4, FS_CardinalityType, PermLength
          <6>3. seq[n] > seq[m] /\ Q'[seq[m]] # BOT
            OBVIOUS
          <6>4. PICK r \in ProcSet : (pc[r] = 6 /\ seq[n] < l[r] /\ seq[m] < j[r])
            BY <6>1, <6>2, <6>3 DEF TypeOK
          <6> QED
            BY <6>4
        <5>9. A_ \in SUBSET 1..(L-1)
          <6> SUFFICES ASSUME NEW n \in A_
                       PROVE n \in 1..(L-1)
            OBVIOUS         
          <6>1. PICK kn \in 1..(k-1) : seq[kn] = n
            OBVIOUS
          <6>2. \A y \in 1..k-1 : y \in 1..Cardinality(A)
            BY <5>2, <5>4, FS_CardinalityType
          <6>3. kn \in 1..Cardinality(A)
            BY <6>1, <6>2, Isa DEF Perm
          <6>4. n \in A
            BY <6>1, <6>2, <6>3 DEF Perm
          <6>5. A \in SUBSET 1..L
            BY DEF TypeOK
          <6>6. n \in 1..L
            BY <6>4, <6>5
          <6>7. n # L => n \in 1..(L-1)
            BY <6>4, <6>5, <6>6 DEF TypeOK
          <6> SUFFICES ASSUME n = L
                       PROVE  FALSE
            BY <6>7
          <6>8. seq[kn] = L
            BY <6>1
          <6>9. seq[k] = L
            BY <5>4 DEF TypeOK
          <6>10. \A y, q \in DOMAIN seq : seq[y] = seq[q] => y = q
            BY PermDistinct, <5>2
          <6>11. kn = k
            BY <5>3, <5>4, <6>3, <6>8, <6>9, <6>10
          <6>12. seq[k] \notin A_
            <7> SUFFICES ASSUME seq[k] \in A_
                         PROVE FALSE
              OBVIOUS
            <7>1. PICK z \in 1..(k-1) : seq[z] = seq[k]
              OBVIOUS
            <7>2. \A y \in 1..k-1 : y \in 1..Cardinality(A)
              BY <5>2, <5>4, FS_CardinalityType
            <7>3. z = k
              BY <5>3, <6>10, <7>1, <7>2
            <7>4. k \notin 1..(k-1)
              OBVIOUS
            <7> QED
              BY <7>1, <7>3, <7>4
          <6> QED
            BY <6>1, <6>8, <6>11, <6>12
        <5> HIDE <3>2
        <5>10. PICK t \in M : /\ ValuesMatchInds(seq_, t.state)
                              /\ GoodRes(A_, t.res)
          BY <5>6, <5>7, <5>8, <5>9, Zenon
        <5> USE <3>2
        
        \* Set of indices to be linearized.
        <5> DEFINE Sk == {seq[z] : z \in k..Cardinality(A)} 
        
        \* Sequence of indices in the order they are to be linearized.
        <5> DEFINE seqk == [z \in 1..(Cardinality(A)-(k-1)) |-> seq[z+(k-1)]]
        
        \* Note that for every index appearing in seqk, corresponding process must exist and is unique.
        <5>11. \A z \in DOMAIN seqk : 
                  \E r \in ProcSet : /\ pc'[r] = 2 
                                     /\ i'[r] = seqk[z]
                                     /\ \A r_ \in ProcSet : ((pc'[r_] = pc'[r] /\ i'[r_] = i'[r]) => r = r_)
          <6> SUFFICES ASSUME NEW z \in DOMAIN seqk
                       PROVE  \E r \in ProcSet : /\ pc'[r] = 2 
                                                 /\ i'[r] = seqk[z]
                                                 /\ \A r_ \in ProcSet : ((pc'[r_] = pc'[r] /\ i'[r_] = i'[r]) => r = r_)
            OBVIOUS
          <6>1. z+(k-1) \in k..Cardinality(A)
            BY <5>2, <5>4, FS_CardinalityType
          <6>2. Q[seq[z+(k-1)]] = BOT
            BY <5>5, <6>1
          <6>3. seq[z+(k-1)] \in A
            BY <6>1 DEF Perm
          <6>4. PICK r \in ProcSet : pc'[r] = 2 /\ i'[r] = seq[z+(k-1)]
            BY <6>2, <6>3, Isa DEF GoodEnqSet
          <6> QED
            BY <2>4, <6>4 DEF InvL2
        
        <5>12. \A q \in ProcSet : pc'[q] = 2 <=> (q = p \/ pc[q] = 2)
          BY DEF TypeOK
          
        <5>13. \A q \in ProcSet : pc'[q] = 2 <=> (q = p /\ i'[q] = L) \/ (pc[q] = 2 /\ i'[q] = i[q])
          BY DEF TypeOK
              
        \* Sequence of "corresponding" processes in the order they are to be linearized.
        
        <5> DEFINE seqp == [z \in 1..(Cardinality(A)-(k-1)) |-> CHOOSE r \in ProcSet : ((r = p /\ L = seqk[z]) \/ (pc[r] = 2 /\ i[r] = seqk[z]))]

        \* The set of processes in the aforementioned sequence.
        <5> DEFINE Sp == {seqp[z] : z \in DOMAIN seqp}

        \* The sequence of to-be-written values in the order they are to be linearized.
        <5> DEFINE vseqp == [z \in DOMAIN seqp |-> v[seqp[z]]]
        
        \* The linearized tuple : append to t.state, and acknowledge processes in Sp.
        <5> DEFINE u == [state |-> Concat(t.state, vseqp),   
                         res |-> [q \in ProcSet |-> IF q \in Sp THEN ACK ELSE t.res[q]]]
                         
        \* Some ad hoc tricks to facilitate proof.
        <5> DEFINE P(w) == /\ tTypeOK(w)'
                           /\ \E y \in M : \E B \in SUBSET UnlinearizedEnqs(y)' : \E pi \in Perm(B) : 
                                  /\ w.state = Concat(y.state, [m \in DOMAIN pi |-> v[pi[m]]])
                                  /\ \A q \in ProcSet : IF q \in B THEN w.res[q] = ACK ELSE w.res[q] = y.res[q]
        
        <5>14. M'  = {w \in TupleDomain : P(w)}
          OBVIOUS
        
        <5> HIDE <3>2 DEF P
        <5>15. u \in M' <=> /\ u \in TupleDomain
                            /\ P(u)
          BY <5>14
                     
        <5>16. u \in M' <=> (/\ u \in TupleDomain 
                             /\ tTypeOK(u)'
                             /\ \E y \in M : (\E B \in SUBSET UnlinearizedEnqs(y)' : (\E pi \in Perm(B) : 
                                  (/\ u.state = Concat(y.state, [m \in DOMAIN pi |-> v[pi[m]]])
                                   /\ \A q \in ProcSet : IF q \in B THEN u.res[q] = ACK ELSE u.res[q] = y.res[q]))))
          BY <5>15, Zenon DEF P
        
        <5>17. u \in TupleDomain
          <6>1. u.state \in Seqs(Nat)
            <7>1. u.state = [z \in 1..(Len(t.state)+Len(vseqp)) |-> IF z \leq Len(t.state) THEN t.state[z] ELSE vseqp[z-Len(t.state)]]
              BY Zenon DEF Concat
            <7>2. Len(t.state) \in Nat
              OBVIOUS
            <7>3. Len(vseqp) \in Nat
              BY <5>2, <5>4, FS_CardinalityType
            <7>4. Len(t.state)+Len(vseqp) \in Nat
              BY <7>2, <7>3, Isa
            <7>5. \A z \in DOMAIN vseqp : vseqp[z] \in Nat
              <8> SUFFICES ASSUME NEW z \in DOMAIN vseqp
                           PROVE  vseqp[z] \in Nat
                BY Zenon
              <8>1. vseqp[z] = v[seqp[z]]
                OBVIOUS
              <8>2. PICK r \in ProcSet : r = seqp[z]
                OBVIOUS
              <8>3. v[r] \in Nat
                BY DEF TypeOK
              <8> QED
                BY <8>1, <8>2, <8>3
              
            <7>6. \A z \in 1..Len(t.state) : t.state[z] \in Nat
              BY <5>10 DEF TypeOK, TupleDomain, Seqs
            <7>7. \A z \in DOMAIN u.state : u.state[z] \in Nat
              <8> SUFFICES ASSUME NEW z \in DOMAIN u.state
                           PROVE  u.state[z] \in Nat
                OBVIOUS
              <8>1. u.state[z] = IF z \leq Len(t.state) THEN t.state[z] ELSE vseqp[z-Len(t.state)]
                BY <7>1, Zenon
              <8>2. z \in 1..(Len(t.state)+Len(vseqp))
                BY <7>1, Zenon
              <8>3. z \in Nat
                BY <7>1, <7>4, <8>2, SMT
              <8> USE <8>3
              <8>4. CASE z <= Len(t.state)
                <9> USE <8>4
                <9>1. u.state[z] = t.state[z]
                  BY <8>1
                <9>2. (1 <= z /\ z <= Len(t.state)) => z \in 1..Len(t.state)
                  BY <7>1
                <9>3. z \in 1..(Len(t.state)+Len(vseqp))
                  BY <7>1, Zenon
                <9>4. 1 <= z /\ z <= Len(t.state)
                  BY <7>4, <9>3
                <9>5. z \in 1..Len(t.state)
                  BY <9>2, <9>4
                <9>6. t.state[z] \in Nat
                  BY <7>1, <7>6, <8>1, <9>5
                <9> QED
                  BY <9>1, <9>6
              <8>5. CASE z > Len(t.state)
                <9> USE <8>5
                <9>1. u.state[z] = vseqp[z-Len(t.state)]
                  BY <8>1
                <9>2. z-Len(t.state) \in DOMAIN vseqp => vseqp[z-Len(t.state)] = v[seqp[z-Len(t.state)]]
                  BY Zenon
                <9>3. DOMAIN vseqp = 1..(Cardinality(A)-(k-1))
                  OBVIOUS
                <9>4. DOMAIN vseqp = DOMAIN seqp
                  OBVIOUS
                <9>5. z \in 1..(Len(t.state)+Len(vseqp)) /\ z > Len(t.state)
                  BY <7>1, Zenon
                <9>6. \A q, d, c \in Nat : (d \in 1..q /\ c \in 0..q /\ d > c) => d \in (c+1)..q
                  OBVIOUS
                <9>7. Len(t.state) \in 0..(Len(t.state)+Len(vseqp)) => z \in (Len(t.state)+1)..(Len(t.state)+Len(vseqp))
                  BY <7>1, <7>2, <7>3, <7>4, <9>6, Zenon
                <9>8. 0 <= Len(t.state) /\ Len(t.state) <= (Len(t.state) + Len(vseqp))
                  BY <7>2, <7>3, Isa
                <9> HIDE DEF vseqp
                <9>9. Len(t.state) \in 0..(Len(t.state)+Len(vseqp))
                  BY <7>3, <7>4, <9>8
                <9>10. z \in (Len(t.state)+1)..(Len(t.state)+Len(vseqp))
                  BY <9>7, <9>9
                <9>11. z-Len(t.state) \in 1..Len(vseqp)
                  BY <7>2, <7>3, <9>10
                <9>12. DOMAIN vseqp = 1..Len(vseqp)
                  OBVIOUS
                <9>13. vseqp[z-Len(t.state)] = v[seqp[z-Len(t.state)]]
                  BY <9>2, <9>11, <9>12
                <9>14. seqp[z-Len(t.state)] \in ProcSet => v[seqp[z-Len(t.state)]] \in PosInts
                  BY DEF TypeOK, Zenon
                <9>15. \A d \in DOMAIN seqp : seqp[d] \in ProcSet
                  <10> SUFFICES ASSUME NEW d \in DOMAIN seqp
                                PROVE  seqp[d] \in ProcSet
                    OBVIOUS
                  <10>1. PICK r \in ProcSet : r = seqp[d]
                    OBVIOUS
                  <10> QED
                    BY <10>1, Zenon
                <9>16. seqp[z-Len(t.state)] \in ProcSet
                  BY <9>15, <9>11, <9>12, <9>4, Zenon
                <9>17. v[seqp[z-Len(t.state)]] \in PosInts
                  BY <9>14, <9>16
                <9> QED
                  BY <9>1, <9>13, <9>17
              <8> QED
                BY <8>4, <8>5
            <7>8. DOMAIN u.state = 1..(Len(t.state)+Len(vseqp))
              BY <7>1
            <7>9. u.state \in [1..(Len(t.state)+Len(vseqp)) -> Nat]
              BY <7>1, <7>7, <7>8, Zenon
            <7> QED
              BY <7>4, <7>9 DEF Seqs
          <6> HIDE DEF seqp
          <6>2. u.res \in [ProcSet -> Nat \union {ACK, BOT}]
            BY Z3T(15) DEF TypeOK, tTypeOK
          <6> QED
            BY <6>1, <6>2 DEF TupleDomain
            
        <5>18. seqp = seqp'
          <6> SUFFICES ASSUME NEW z \in DOMAIN seqp
                       PROVE seqp[z] = seqp'[z]
            OBVIOUS
          <6>1. pc'[p] = 2 /\ i'[p] = L
            BY <3>2 DEF TypeOK
          <6>2. \A r \in ProcSet : (pc[r] = 2 /\ i[r] = seqk[z]) => (pc'[r] = 2 /\ i'[r] = seqk[z])
            BY <3>2 DEF TypeOK
          <6>3. \A r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seqk[z]) => (r = p /\ L = seqk[z]) \/ (pc[r] = 2 /\ i[r] = seqk[z])
            BY <3>2 DEF TypeOK
          <6>4. L+1 # seqk[z]
            <7>1. seqk[z] = seq[z+(k-1)]
              OBVIOUS
            <7>2. z+(k-1) \in DOMAIN seq => seqk[z] \in A
              BY DEF Perm
            <7>3. z \in 1..Cardinality(A)-(k-1)
              OBVIOUS
            <7>4. z+(k-1) \in k..Cardinality(A)
              BY <5>2, <7>3, FS_CardinalityType
            <7>5. z+(k-1) \in DOMAIN seq
              BY <5>3, <7>4
            <7>6. seqk[z] \in A
              BY <7>2, <7>5
            <7>7. L+1 \notin A
              BY <3>2 DEF TypeOK
            <7> QED
              BY <7>6, <7>7
          <6> QED
            BY <3>2, <6>1, <6>2, <6>3, <6>4 DEF TypeOK
        
        <5>19. u = u'
          <6>1. v = v'
            BY <3>2
          <6>2. seqp = seqp'
            BY <5>18
          <6> HIDE DEF seqp
          <6>3. u.state = u.state'
            BY <6>1, <6>2, Zenon
          <6>4. u.res = u.res'
            BY <6>2, Isa
          <6> QED
            BY <6>3, <6>4, Zenon
            
        <5>20. \A q \in Sp : /\ q \in ProcSet 
                             /\ (\E z \in DOMAIN seqp : (q = p /\ L = seqk[z]) \/ (pc[q] = 2 /\ i[q] = seqk[z]))
          <6> SUFFICES ASSUME NEW q \in Sp
                       PROVE  /\ q \in ProcSet 
                              /\ \E z \in DOMAIN seqp : (q = p /\ L = seqk[z]) \/ (pc[q] = 2 /\ i[q] = seqk[z])
            OBVIOUS
          <6>1. PICK z \in DOMAIN seqp : q = seqp[z]
            OBVIOUS
          <6>2. seqk[1] = L
            BY <4>1, <5>2, <5>4, FS_CardinalityType
          <6>3. seq[k] = L
            BY <5>2, <5>4, <6>2, FS_CardinalityType
          <6>4. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
            BY <5>2, PermDistinct
          <6>5. \A n \in DOMAIN seq : n # k => seq[n] # L
            BY <6>4, <5>2, <5>3, <6>3
          <6>6. \A n \in DOMAIN seqk : n # 1 => seqk[n] # L
            BY <6>5, <5>2, <5>3, <5>4, FS_CardinalityType
          <6>7. CASE z # 1
            <7> USE <6>7
            <7>1. seqp[z] = CHOOSE r \in ProcSet : (pc[r] = 2 /\ i[r] = seqk[z])
              BY <6>1, <6>6
            <7>2. PICK r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seqk[z])
              BY <5>11
            <7>3. (r = p /\ i'[r] = L) \/ (pc[r] = 2 /\ i'[r] = seqk[z])
              BY <7>2, <5>13
            <7>4. pc[r] = 2 /\ i'[r] = seqk[z]
              BY <6>6, <7>2, <7>3
            <7>5. pc[q] = 2 /\ i[q] = seqk[z]
              BY <3>2, <6>1, <7>1, <7>4 DEF TypeOK
            <7>6. \A d \in DOMAIN seqp : seqp[d] \in ProcSet
              <8> SUFFICES ASSUME NEW d \in DOMAIN seqp
                            PROVE  seqp[d] \in ProcSet
                OBVIOUS
              <8>1. PICK f \in ProcSet : f = seqp[d]
                OBVIOUS
              <8> QED
                BY <8>1, Zenon
            <7> QED
              BY <6>1, <7>5, <7>6
          <6>8. CASE z = 1
            <7> USE <6>8
            <7>1. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[z])
              BY <6>1, <6>6
            <7>2. PICK r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seqk[z])
              BY <5>11
            <7>3. (r = p /\ i'[r] = L) \/ (pc[r] = 2 /\ i'[r] = seqk[z])
              BY <7>2, <5>13
            <7>4. \A r_ \in ProcSet : pc[r_] = 2 => i'[r_] < L
              BY <3>2 DEF TypeOK, InvL2
            <7>5. r = p /\ L = seqk[z]
              BY <7>2, <7>3, <7>4, <6>2 DEF TypeOK
            <7>6. seqp[z] = r
              BY <7>1, <7>2, <7>5
            <7> QED
              BY <6>1, <7>5, <7>6
          <6> QED
            BY <6>7, <6>8
        
        \* Very underoptimized -- should be redone with previous step!! (which was added later)
        <5>21. tTypeOK(u)'
          <6> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ (pc'[q] \in {0, 1, 4, 5, 6}  => u.res[q] = BOT)
                              /\ (pc'[q] \in {2, 3}           => u.res[q] \in {ACK, BOT})
                              /\ (pc'[q] = 7                  => u.res[q] \in Nat \union {BOT})
            BY <5>19, Zenon DEF tTypeOK
          <6>1. CASE pc'[q] \in {0, 1, 4, 5, 6}
            <7> USE <6>1
            <7>1. q \notin Sp
              <8> SUFFICES ASSUME q \in Sp
                           PROVE FALSE
                OBVIOUS
              <8>1. PICK z \in DOMAIN seqp : q = seqp[z]
                OBVIOUS
              <8>2. seqk[1] = L
                BY <4>1, <5>2, <5>4, FS_CardinalityType
              <8>3. seq[k] = L
                BY <5>2, <5>4, <8>2, FS_CardinalityType
              <8>4. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
                BY <5>2, PermDistinct
              <8>5. \A n \in DOMAIN seq : n # k => seq[n] # L
                BY <8>4, <5>2, <5>3, <8>3
              <8>6. \A n \in DOMAIN seqk : n # 1 => seqk[n] # L
                BY <8>5, <5>2, <5>3, <5>4, FS_CardinalityType
              <8>7. CASE z # 1
                <9> USE <8>7
                <9>1. seqp[z] = CHOOSE r \in ProcSet : (pc[r] = 2 /\ i[r] = seqk[z])
                  BY <8>1, <8>6
                <9>2. \E r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seqk[z])
                  BY <5>11
                <9>3. \E r \in ProcSet : (r = p) \/ (pc[r] = 2 /\ i'[r] = seqk[z])
                  BY <9>2, <5>12
                <9>4. pc[q] = 2 /\ i[q] = seqk[z]
                  BY <3>2, <8>1, <9>1, <9>3 DEF TypeOK
                <9> QED
                  BY <3>2, <9>4 DEF TypeOK
              <8>8. CASE z = 1
                <9> USE <8>8
                <9>1. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[z])
                  BY <8>1, <8>6
                <9>2. seqp[z] = p
                  BY <8>2, <9>1
                <9> QED
                  BY <3>2, <8>1, <9>2 DEF TypeOK
              <8> QED
                BY <8>7, <8>8
            <7>2. t.res[q] = BOT
              BY <3>2 DEF TypeOK, tTypeOK
            <7> QED
              BY <7>1, <7>2
          <6>2. CASE pc'[q] = 2
            <7> USE <6>2
            <7>1. CASE q \in Sp
              BY <7>1
            <7>2. CASE q \notin Sp
              BY <3>2, <7>2 DEF TypeOK, tTypeOK
            <7> QED
              BY <7>1, <7>2
          <6>3. CASE pc'[q] = 3
            <7> USE <6>3
            <7>1. q \notin Sp
              <8> SUFFICES ASSUME q \in Sp
                           PROVE FALSE
                OBVIOUS
              <8>1. PICK z \in DOMAIN seqp : q = seqp[z]
                OBVIOUS
              <8>2. seqk[1] = L
                BY <4>1, <5>2, <5>4, FS_CardinalityType
              <8>3. seq[k] = L
                BY <5>2, <5>4, <8>2, FS_CardinalityType
              <8>4. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
                BY <5>2, PermDistinct
              <8>5. \A n \in DOMAIN seq : n # k => seq[n] # L
                BY <8>4, <5>2, <5>3, <8>3
              <8>6. \A n \in DOMAIN seqk : n # 1 => seqk[n] # L
                BY <8>5, <5>2, <5>3, <5>4, FS_CardinalityType
              <8>7. CASE z # 1
                <9> USE <8>7
                <9>1. seqp[z] = CHOOSE r \in ProcSet : (pc[r] = 2 /\ i[r] = seqk[z])
                  BY <8>1, <8>6
                <9>2. \E r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seqk[z])
                  BY <5>11
                <9>3. \E r \in ProcSet : (r = p) \/ (pc[r] = 2 /\ i'[r] = seqk[z])
                  BY <9>2, <5>12
                <9>4. pc[q] = 2 /\ i[q] = seqk[z]
                  BY <3>2, <8>1, <9>1, <9>3 DEF TypeOK
                <9> QED
                  BY <3>2, <9>4 DEF TypeOK
              <8>8. CASE z = 1
                <9> USE <8>8
                <9>1. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[z])
                  BY <8>1, <8>6
                <9>2. seqp[z] = p
                  BY <8>2, <9>1
                <9> QED
                  BY <3>2, <8>1, <9>2 DEF TypeOK
              <8> QED
                BY <8>7, <8>8
            <7>2. t.res[q] \in {ACK, BOT}
              BY <3>2 DEF TypeOK, tTypeOK
            <7> QED
              BY <7>1, <7>2 
          <6>4. CASE pc'[q] = 7
            <7> USE <6>4
            <7>1. q \notin Sp
              <8> SUFFICES ASSUME q \in Sp
                           PROVE FALSE
                OBVIOUS
              <8>1. PICK z \in DOMAIN seqp : q = seqp[z]
                OBVIOUS
              <8>2. seqk[1] = L
                BY <4>1, <5>2, <5>4, FS_CardinalityType
              <8>3. seq[k] = L
                BY <5>2, <5>4, <8>2, FS_CardinalityType
              <8>4. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
                BY <5>2, PermDistinct
              <8>5. \A n \in DOMAIN seq : n # k => seq[n] # L
                BY <8>4, <5>2, <5>3, <8>3
              <8>6. \A n \in DOMAIN seqk : n # 1 => seqk[n] # L
                BY <8>5, <5>2, <5>3, <5>4, FS_CardinalityType
              <8>7. CASE z # 1
                <9> USE <8>7
                <9>1. seqp[z] = CHOOSE r \in ProcSet : (pc[r] = 2 /\ i[r] = seqk[z])
                  BY <8>1, <8>6
                <9>2. \E r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seqk[z])
                  BY <5>11
                <9>3. \E r \in ProcSet : (r = p) \/ (pc[r] = 2 /\ i'[r] = seqk[z])
                  BY <9>2, <5>12
                <9>4. pc[q] = 2 /\ i[q] = seqk[z]
                  BY <3>2, <8>1, <9>1, <9>3 DEF TypeOK
                <9> QED
                  BY <3>2, <9>4 DEF TypeOK
              <8>8. CASE z = 1
                <9> USE <8>8
                <9>1. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[z])
                  BY <8>1, <8>6
                <9>2. seqp[z] = p
                  BY <8>2, <9>1
                <9> QED
                  BY <3>2, <8>1, <9>2 DEF TypeOK
              <8> QED
                BY <8>7, <8>8
            <7>2. t.res[q] \in Nat \union {BOT}
              BY <3>2 DEF TypeOK, tTypeOK
            <7> QED
              BY <7>1, <7>2 
          <6> QED
            BY <6>1, <6>2, <6>3, <6>4
        
        <5>22. (\E B \in SUBSET UnlinearizedEnqs(t)' : (\E pi \in Perm(B) : 
                   (/\ u.state = Concat(t.state, [m \in DOMAIN pi |-> v[pi[m]]])
                    /\ \A q \in ProcSet : IF q \in B THEN u.res[q] = ACK ELSE u.res[q] = t.res[q]))) => u \in M'
          BY <5>10, <5>16, <5>17, <5>21, Zenon
          
        <5>23. Sp \in SUBSET UnlinearizedEnqs(t)'
          <6> SUFFICES ASSUME NEW q \in Sp
                       PROVE  /\ q \in ProcSet
                              /\ pc'[q] = 2 \/ pc'[q] = 3
                              /\ t.res[q] = BOT
            BY DEF UnlinearizedEnqs
          <6>1. PICK z \in DOMAIN seqp : q = seqp[z]
            OBVIOUS
          <6>2. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[z]) \/ (pc[r] = 2 /\ i[r] = seqk[z])
            OBVIOUS
          <6>3. seqp[z] = q
            BY <6>1
          <6>4. (q = p /\ L = seqk[z]) \/ (pc[q] = 2 /\ i[q] = seqk[z])
            BY <5>20, <6>2, <6>1
          <6>5. q \in ProcSet
            BY <5>20
          <6>6. pc'[q] = 2
            BY <3>2, <6>4 DEF TypeOK
          <6> SUFFICES ASSUME TRUE
                       PROVE  t.res[q] = BOT
            BY <6>5, <6>6
          <6>7. q = p \/ pc[q] = 2
            BY <6>4
          <6>8. q = p => t.res[q] = BOT
            BY <3>2, <5>10 DEF GoodRes
          <6>9. (pc[q] = 2 /\ i[q] \notin A_) => t.res[q] = BOT
            BY <5>20, <5>10 DEF GoodRes
          <6> SUFFICES ASSUME pc[q] = 2
                       PROVE  i[q] \notin A_
            BY <6>7, <6>8, <6>9
          <6>10. i[q] = seq[z+(k-1)]
            BY <3>2, <6>1, <6>4
          <6>11. \A c \in A_ : \E n \in 1..(k-1) : c = seq[n]
            OBVIOUS
          <6>12. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
            BY <5>2, PermDistinct
          <6>13. \A c \in A_ : c # seq[z+(k-1)]
            <7> SUFFICES ASSUME NEW c \in A_,
                                NEW n \in 1..(k-1),
                                c = seq[n]
                         PROVE  c # seq[z+(k-1)]
              BY <6>11
            <7>1. z+(k-1) # n
              BY <6>1
            <7>2. \A y \in 1..k-1 : y \in 1..Cardinality(A)
              BY <5>2, <5>4, FS_CardinalityType
            <7>3. n \in DOMAIN seq
              BY <5>3, <7>2
            <7>4. z \in 1..Cardinality(A)-(k-1)
              BY <6>1
            <7>5. z+(k-1) \in k..Cardinality(A)
              BY <5>2, <7>4, FS_CardinalityType
            <7>6. z+(k-1) \in DOMAIN seq
              BY <5>3, <7>5
            <7>7. seq[n] # seq[z+(k-1)]
              BY <6>12, <7>1, <7>3, <7>6
            <7> QED 
              BY <7>7
          <6> QED
            BY <6>10, <6>13
        
        <5>24. seqp \in Perm(Sp)
          <6>1. DOMAIN seqp = 1..Cardinality(A)-(k-1)
            OBVIOUS
          <6>2. Cardinality(Sp) = Cardinality(A)-(k-1)
            <7>1. seqp \in Injection(1..Cardinality(A)-(k-1), Sp)
              <8> SUFFICES ASSUME NEW y \in 1..Cardinality(A)-(k-1), NEW z \in 1..Cardinality(A)-(k-1),
                                  seqp[y] = seqp[z]
                           PROVE  y = z
                BY Zenon DEF Injection
              <8>1. seqp[y] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[y]) \/ (pc[r] = 2 /\ i[r] = seqk[y])
                OBVIOUS
              <8>2. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ L = seqk[z]) \/ (pc[r] = 2 /\ i[r] = seqk[z])
                OBVIOUS
              <8>3. (seqp[y] = p /\ L = seqk[y]) \/ (pc[seqp[y]] = 2 /\ i[seqp[y]] = seqk[y])
                BY <8>1, <5>20, SMT
              <8>4. (seqp[z] = p /\ L = seqk[z]) \/ (pc[seqp[z]] = 2 /\ i[seqp[z]] = seqk[z])
                BY <8>2, <5>20, SMT
              <8>5. seqp[y] = p => (pc[seqp[y]] # 2 /\ pc[seqp[z]] # 2)
                BY <3>2, Isa DEF TypeOK
              <8>6. (seqp[y] = p /\ L = seqk[y]) <=> (seqp[z] = p /\ L = seqk[z])
                BY <8>4, <8>5
              <8>7. seq[k] = L
                BY <4>1, <5>2, <5>4, FS_CardinalityType
              <8>8. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
                BY <5>2, PermDistinct
              <8>9. \A n, m \in DOMAIN seq : seq[n] = seq[m] => n = m
                BY <8>8
              <8>10. \A n \in DOMAIN seq : n # k => seq[n] # L
                BY <8>8, <5>2, <5>3, <8>7
              <8>11. \A n \in DOMAIN seqk : n # 1 => seqk[n] # L
                BY <8>10, <5>2, <5>3, <5>4, FS_CardinalityType
              <8>12. CASE seqp[y] = p /\ L = seqk[y]
                <9> USE <8>12
                <9>0. seqp[z] = p /\ L = seqk[z]
                  BY <8>6
                <9> QED
                  BY <8>11, <9>0
              <8>13. CASE pc[seqp[y]] = 2 /\ i[seqp[y]] = seqk[y]
                <9> USE <8>13
                <9>1. seqp[y] # p /\ seqp[z] # p
                  BY <3>2, Isa DEF TypeOK
                <9>2. (pc[seqp[y]] = 2 /\ i[seqp[y]] = seqk[y]) /\ (pc[seqp[z]] = 2 /\ i[seqp[z]] = seqk[z])
                  BY <8>3, <8>4, <9>1
                <9>3. seqk[y] = seqk[z]
                  BY <9>2, <5>20, Zenon DEF InvL2
                <9> QED
                  BY <9>3, <8>9, <5>2, <5>3, <5>4, FS_CardinalityType
              <8>14. QED
                BY <8>3, <8>12, <8>13
            <7>2. seqp \in Surjection(1..Cardinality(A)-(k-1), Sp)
              BY Zenon DEF Surjection
            <7>3. ExistsBijection(1..Cardinality(A)-(k-1), Sp)
              BY <7>1, <7>2 DEF Bijection, ExistsBijection
            <7> QED
              BY <5>2, <5>4, <7>3, FS_CountingElements, FS_CardinalityType
          <6> QED
            BY <6>1, <6>2, Isa DEF Perm
        
        <5>25. (/\ u.state = Concat(t.state, [m \in DOMAIN seqp |-> v[seqp[m]]])
                /\ \A q \in ProcSet : IF q \in Sp THEN u.res[q] = ACK ELSE u.res[q] = t.res[q]) => u \in M'
          BY <5>22, <5>23, <5>24, Zenon
        
        <5>26. u.state = Concat(t.state, [m \in DOMAIN seqp |-> v[seqp[m]]])
          OBVIOUS
        
        <5>27. \A q \in ProcSet : IF q \in Sp THEN u.res[q] = ACK ELSE u.res[q] = t.res[q]
          OBVIOUS
        
        <5>28. u \in M'
          BY <5>25, <5>26, <5>27

        <5> HIDE DEF u
        <5>30. ValuesMatchInds(seq, u.state)' = (u.state = [m \in DOMAIN seq |-> CASE Q[seq[m]] # BOT -> Q[seq[m]]
                                                                                   [] OTHER           -> v[CHOOSE q \in ProcSet : (pc'[q] = 2  /\ i'[q] = seq[m])]])
           BY <3>2, <5>19 DEF ValuesMatchInds
        
        <5>31. ValuesMatchInds(seq, u.state)'
          <6> DEFINE vals == [m \in DOMAIN seq |-> CASE Q[seq[m]] # BOT -> Q[seq[m]]
                                                     [] OTHER           -> v[CHOOSE q \in ProcSet : (pc'[q] = 2  /\ i'[q] = seq[m])]]
          <6>1. u.state \in [DOMAIN seq -> Nat]
            <7>1. u.state = [z \in 1..(Len(t.state)+Len(vseqp)) |-> IF z \leq Len(t.state) THEN t.state[z] ELSE vseqp[z-Len(t.state)]]
              BY Zenon DEF Concat, u
            <7>2. Len(t.state)+Len(vseqp) = Cardinality(A)
              <8>1. Len(t.state) = k-1
                BY <5>10 DEF ValuesMatchInds
              <8>2. Len(vseqp) = Cardinality(A)-(k-1)
                BY <5>2, FS_CardinalityType
              <8> QED
                BY <8>1, <8>2, <5>2, FS_CardinalityType
            <7>3. DOMAIN u.state = 1..Cardinality(A)
              BY <7>1, <7>2, Zenon
            <7>4. \E n \in Nat : u.state \in [1..n -> Nat]
              BY <5>17 DEF TupleDomain, Seqs
            <7>5. u.state \in [1..Cardinality(A) -> Nat]
              BY <7>3, <7>4, <5>2, FS_CardinalityType
            <7> QED
              BY <5>3, <7>5
          <6>2. vals \in [DOMAIN seq -> Nat]
            <7>1. DOMAIN vals = DOMAIN seq
              OBVIOUS
            <7>2. \A m \in DOMAIN vals : vals[m] \in Nat
              <8> SUFFICES ASSUME NEW m \in DOMAIN vals 
                           PROVE  vals[m] \in Nat
                BY Zenon
              <8>1. CASE Q[seq[m]] # BOT
                BY <8>1 DEF Perm, TypeOK
              <8>2. CASE Q[seq[m]] = BOT
                <9> USE <8>2
                <9>1. vals[m] = v[CHOOSE q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m]]
                  OBVIOUS
                <9>2. \E q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m]
                  <10>1. CASE m < k
                    <11>1. seq[m] \in A_
                      BY <10>1, <5>3
                    <11>2. PICK q \in ProcSet : pc[q] = 2 /\ i[q] = seq[m]
                      BY <11>1, <5>7, <5>9 DEF GoodEnqSet
                    <11> QED
                      BY <3>2, <11>2 DEF TypeOK
                  <10>2. CASE m >= k
                    <11>1. m \in k..Cardinality(A)
                      BY <10>2, <5>3, FS_CardinalityType
                    <11>2. m-(k-1) \in 1..Cardinality(A)-(k-1)
                      BY <11>1, <5>2, <5>3, <5>4, FS_CardinalityType
                    <11>3. PICK q \in ProcSet : pc'[q] = 2 /\ i'[q] = seqk[m-(k-1)]
                      BY <11>2, <5>11
                    <11>4. seqk[m-(k-1)] = seq[m]
                      BY <11>1, <5>2, <5>3, <5>4, FS_CardinalityType
                    <11> QED
                      BY <11>3, <11>4
                  <10> QED
                    BY <10>1, <10>2, <5>3
                <9>3. PICK q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m] /\ vals[m] = v[q]
                  BY <9>1, <9>2, Zenon
                <9> QED
                  BY <9>3 DEF TypeOK
              <8> QED
                BY <8>1, <8>2
            <7> QED
              BY <7>1, <7>2
          <6>3. \A m \in DOMAIN seq : u.state[m] = vals[m]
            <7> SUFFICES ASSUME NEW m \in DOMAIN seq
                         PROVE  u.state[m] = vals[m]
              OBVIOUS
            <7>1. Len(t.state) = k-1
              BY <5>10 DEF ValuesMatchInds
            <7>2. m < k => u.state[m] = t.state[m]
              BY <7>1, <5>2, <5>3, <5>4, FS_CardinalityType DEF Concat, u
            <7>3. u.state = [z \in 1..(Len(t.state)+Len(vseqp)) |-> IF z \leq Len(t.state) THEN t.state[z] ELSE vseqp[z-Len(t.state)]]
              BY Zenon DEF Concat, u
            <7>4. (~(m \leq Len(t.state))) => u.state[m] = vseqp[m-Len(t.state)]
              BY <6>1, <7>3, Zenon
            <7>5. m >= k => u.state[m] = v[seqp[m-(k-1)]]
              BY <7>1, <7>4, <5>2, <5>3, <5>4, FS_CardinalityType
            <7>6. CASE m < k
              <8> SUFFICES ASSUME m < k, u.state[m] = t.state[m]
                           PROVE  t.state[m] = vals[m]
                BY <7>2, <7>6
              <8>1. CASE Q[seq[m]] # BOT
                <9>1. vals[m] = Q[seq[m]]
                  BY <8>1
                <9>2. m \in DOMAIN seq_ => t.state[m] = Q[seq[m]]
                  BY <5>10, <8>1 DEF ValuesMatchInds 
                <9>3. m \in DOMAIN seq_
                  BY <5>3
                <9> QED
                  BY <9>1, <9>2, <9>3
              <8>2. CASE Q[seq[m]] = BOT
                <9> USE <8>2
                <9>1. vals[m] = v[CHOOSE q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m]]
                  OBVIOUS
                <9>2. \E q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m]
                  <10>1. seq[m] \in A_
                    BY <5>3
                  <10>2. PICK q \in ProcSet : pc[q] = 2 /\ i[q] = seq[m]
                    BY <10>1, <5>7, <5>9 DEF GoodEnqSet
                  <10> QED
                    BY <3>2, <10>2 DEF TypeOK
                <9>3. PICK q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m] /\ vals[m] = v[q]
                  BY <9>1, <9>2, Zenon
                <9>4. m \in DOMAIN seq_
                  BY <5>3
                <9>5. t.state[m] = v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[m]]
                  BY <5>10, <9>4, <5>3 DEF ValuesMatchInds
                <9>6. \E r \in ProcSet : pc[r] = 2 /\ i[r] = seq[m]
                  <10>1. seq[m] \in A_
                    BY <5>3
                  <10>2. QED
                    BY <10>1, <5>7, <5>9 DEF GoodEnqSet
                <9>7. PICK r \in ProcSet : pc[r] = 2 /\ i[r] = seq[m] /\ t.state[m] = v[r]
                  BY <9>5, <9>6, Zenon
                <9>8. \A n, y \in DOMAIN seq : n # y => seq[n] # seq[y]
                  BY <5>2, PermDistinct
                <9>9. seq[k] = i'[p]
                  BY <5>4
                <9>10. i'[p] # i'[q]
                  BY <9>8, <9>9, <5>2, <5>3, <9>3
                <9>11. p # q /\ p # r
                  BY <9>10, <9>7, <3>2 DEF TypeOK
                <9>12. i'[q] = i[q]
                  BY <9>11, <3>2 DEF TypeOK
                <9>13. pc[q] = 2
                  BY <3>2, <9>3, <9>11 DEF TypeOK
                <9>14. q = r
                  BY <3>2, <9>13, <9>7, <9>3, <9>12 DEF InvL2
                <9> QED
                  BY <9>3, <9>7, <9>14
              <8> QED
                BY <8>1, <8>2
            <7>7. CASE m >= k
              <8> SUFFICES ASSUME m >= k, u.state[m] = v[seqp[m-(k-1)]]
                           PROVE  v[seqp[m-(k-1)]] = vals[m]
                BY <7>5, <7>7
              <8>1. Q[seq[m]] = BOT
                BY <5>5, <5>3
              <8>2. vals[m] = v[CHOOSE q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m]]
                BY <8>1
              <8>3. \E q \in ProcSet : (pc'[q] = 2 /\ i'[q] = seq[m])
                BY <5>11, <5>2, <5>3, <5>4, FS_CardinalityType
              <8>4. PICK q \in ProcSet : pc'[q] = 2 /\ i'[q] = seq[m] /\ vals[m] = v[q]
                BY <8>2, <8>3, Zenon
              <8>5. m-(k-1) \in 1..Cardinality(A)-(k-1)
                BY <5>2, <5>3, <5>4, FS_CardinalityType
              <8>6. seqk[m-(k-1)] = seq[m]
                BY <5>2, <5>3, <5>4, <8>5, FS_CardinalityType
              <8>7. v[seqp[m-(k-1)]] = v[CHOOSE r \in ProcSet : ((r = p /\ L = seqk[m-(k-1)]) \/ (pc[r] = 2 /\ i[r] = seqk[m-(k-1)]))]
                BY <8>5, <8>6, Zenon
              <8>8. \E r \in ProcSet : (pc'[r] = 2  /\ i'[r] = seqk[m-(k-1)])
                BY <8>5, <5>11
              <8>9. \E r \in ProcSet : (r = p /\ seqk[m-(k-1)] = L) \/ (pc[r] = 2 /\ i'[r] = seqk[m-(k-1)])
                BY <8>8, <5>13, Zenon
              <8>10. \A r \in ProcSet : pc[r] = 2 => i[r] = i'[r]
                BY <3>2 DEF TypeOK
              <8>11. PICK r \in ProcSet : ((r = p /\ seqk[m-(k-1)] = L) \/ (pc[r] = 2 /\ i[r] = seqk[m-(k-1)])) /\ v[seqp[m-(k-1)]] = v[r]
                BY <8>7, <8>9, <8>10, Zenon
              <8>12. i'[r] = seq[m]
                BY <3>2, <8>11, <8>6 DEF TypeOK
              <8>13. pc'[q] = 2
                BY <8>4
              <8>14. pc'[r] = 2
                BY <8>11, <3>2 DEF TypeOK
              <8>15. q = r
                BY <8>13, <8>14, <8>4, <8>12, <2>4 DEF InvL2
              <8> QED
                BY <8>15, <8>4, <8>11
            <7> QED
              BY <7>6, <7>7, <5>3
          <6> QED
            BY <5>30, <6>1, <6>2, <6>3, Zenon
                        
        <5>32. GoodRes(A, u.res)'
          <6> DEFINE GoodProcRes(S, res, q) == res[q] = CASE (pc[q] = 2 /\ i[q] \in S) -> ACK
                                                          [] pc[q] = 3                 -> ACK
                                                          [] pc[q] = 7                 -> x[q]
                                                          [] OTHER                     -> BOT
          <6> SUFFICES ASSUME NEW q \in ProcSet'
                       PROVE  GoodProcRes(A, u.res, q)'
            BY DEF GoodRes
          <6>1. A = A_ \union {i'[r] : r \in Sp}
            <7>1. \A a \in A : a \in A_ \union {i'[r] : r \in Sp}
              <8> SUFFICES ASSUME NEW a \in A
                           PROVE  a \in A_ \union {i'[r] : r \in Sp}
                OBVIOUS
              <8>1. PICK idx \in 1..Cardinality(A) : seq[idx] = a
                BY DEF Perm
              <8>2. CASE idx < k
                <9> USE <8>2
                <9>1. idx \in 1..(k-1)
                  OBVIOUS
                <9>2. seq[idx] \in A_
                  OBVIOUS
                <9> QED
                  BY <8>1, <9>2
              <8>3. CASE idx >= k
                <9> USE <8>3
                <9>1. idx \in k..Cardinality(A)
                  OBVIOUS
                <9>2. (idx - (k - 1)) \in 1..(Cardinality(A)-(k-1))
                  BY <5>2, <9>1, FS_CardinalityType
                <9>3. PICK r \in ProcSet : /\ pc'[r] = 2 
                                           /\ i'[r] = seqk[idx - (k - 1)]
                                           /\ \A r_ \in ProcSet : ((pc'[r_] = pc'[r] /\ i'[r_] = i'[r]) => r = r_)
                  BY <5>11, <9>2
                <9>4. seqk[idx - (k - 1)] = seq[idx]
                  BY <9>2
                <9>8. seqp[idx - (k - 1)] = r
                  <10>1. CASE r = p
                    <11> USE <10>1
                    <11>1. seqk[idx - (k - 1)] = L
                      BY <4>1, <9>3
                    <11>2. \A r_ \in ProcSet : pc[r_] = 2 => i[r_] /= L
                      BY DEF InvL2, TypeOK
                    <11>3. \A r_ \in ProcSet : pc[r_] = 2 /\ i[r_] = seqk[idx - (k - 1)] => FALSE
                      BY <11>1, <11>2
                    <11> QED
                      BY <9>2, <11>3, <11>1, Zenon
                  <10>2. CASE r /= p
                    <11> USE <10>2
                    <11>1. i'[r] = i[r]
                      BY <3>2
                    <11>2. \A r_ \in ProcSet : r_ /= p => /\ pc[r_] = pc'[r_]
                                                          /\ i[r_] = i'[r_]
                      BY <3>2
                    <11> QED
                      BY <11>1, <11>2, <9>2, <9>3
                  <10> QED
                    BY <10>1, <10>2
                <9>9. r \in Sp
                  BY <9>8, <9>2
                <9>10. seqk[idx - (k - 1)] \in {i'[r_] : r_ \in Sp}
                  BY <9>9, <9>3, Zenon
                <9> QED
                  BY <9>10, <9>4, <8>1
              <8> QED
                BY <8>2, <8>3
            <7>2. \A b \in A_ \union {i'[r] : r \in Sp} : b \in A
              <8> SUFFICES ASSUME NEW b \in A_ \union {i'[r] : r \in Sp}
                           PROVE  b \in A
                OBVIOUS
              <8>1. CASE b \in A_
                <9> USE <8>1
                <9>1. PICK z \in 1..(k - 1) : seq[z] = b
                  OBVIOUS
                <9>2. z \in 1..Cardinality(A)
                  BY <5>2, <5>4, FS_CardinalityType
                <9> QED
                  BY <9>1, <9>2 DEF Perm
              <8>2. CASE b \in {i'[r] : r \in Sp}
                <9> USE <8>2
                <9>1. PICK r \in Sp : b = i'[r]
                  OBVIOUS
                <9>2. PICK z \in 1..(Cardinality(A)-(k-1)) : \/ (r = p /\ L = seqk[z]) 
                                                             \/ (pc[r] = 2 /\ i[r] = seqk[z])
                  BY <9>1, <5>20
                <9>3. seqk[z] = seq[z + (k - 1)]
                  OBVIOUS
                <9>4. z + (k - 1) \in (k - 1)..Cardinality(A)
                  BY <5>2, <9>1, FS_CardinalityType
                <9>5. seqk[z] \in A
                  BY <9>3, <9>4 DEF Perm
                <9>6. CASE r /= p
                  <10> USE <9>6
                  <10>1. i[r] = i'[r]
                    BY <3>2 DEF TypeOK
                  <10> QED
                    BY <9>5, <9>2, <9>1, <10>1
                <9>7. CASE r = p
                  <10>1. /\ pc[r] /= 2
                         /\ i'[r] = L
                    BY <9>7, <3>2 DEF TypeOK
                  <10> QED
                    BY <10>1, <9>2, <9>5, <9>1
                <9> QED
                  BY <9>6, <9>7
              <8> QED
                BY <8>1, <8>2
            <7> QED
              BY <7>1, <7>2 
          <6>2. \A r \in Sp : pc'[r] = 2
            <7> SUFFICES ASSUME NEW r \in Sp
                         PROVE  pc'[r] = 2
              OBVIOUS
            <7>1. r = p \/ pc[r] = 2
              BY <5>20
            <7>2. r = p => pc'[r] = 2
              BY <3>2 DEF TypeOK
            <7>3. pc[r] = 2 => pc'[r] = 2
              BY <3>2 DEF TypeOK
            <7> QED 
              BY <7>1, <7>2, <7>3            
          <6>3. CASE q \notin Sp
            <7> USE <6>3
            <7>1. GoodProcRes(A_, t.res, q)
              BY <5>10 DEF GoodRes
            <7>2. u.res[q] = t.res[q]
              BY <5>27
            <7>3. q /= p
              <8>1. seqk[1] = seq[k]
                BY <5>2, <5>3, <5>4, FS_CardinalityType
              <8>2. seqk[1] = i'[p]
                BY <8>1, <5>4
              <8>3. seqk[1] = L
                BY <8>2, <3>2 DEF TypeOK
              <8>4. seqp[1] = p
                BY <5>2, FS_CardinalityType, <8>3
              <8>9. p \in Sp
                BY <5>2, FS_CardinalityType, <8>4
              <8> QED
                BY <8>9
            <7>4. /\ pc[q] = pc'[q]
                  /\ i[q] = i'[q]
                  /\ x[q] = x'[q]
              BY <7>3, <3>2
            <7>5. GoodProcRes(A, u.res, q)
              <8>1. GoodProcRes(A_, u.res, q)
                BY <7>1, <7>2
              <8>2. i[q] \in A_ => i[q] \in A
                BY <6>1
              <8>3. pc[q] = 2 /\ i[q] \in A => i[q] \in A_
                <9> SUFFICES ASSUME pc[q] = 2 /\ i[q] \in {i'[r] : r \in Sp} 
                             PROVE  FALSE
                  BY <6>1, Zenon
                <9>1. PICK r \in Sp : i[q] = i'[r]
                  OBVIOUS
                <9>2. r = p \/ pc[r] = 2
                  BY <5>20
                <9>3. r = q
                  <10>1. CASE r = p
                    <11> USE <10>1
                    <11>1. i[q] < L
                      BY DEF InvL2
                    <11>2. i'[p] = L
                      BY <3>2 DEF TypeOK
                    <11> QED
                      BY <11>1, <11>2, <9>1, Isa
                  <10>2. CASE pc[r] = 2
                    <11> USE <10>2
                    <11>1. r /= p
                      BY <3>2
                    <11>2. i[r] = i'[r]
                      BY <11>1, <3>2
                    <11> QED
                      BY <9>1, <11>2 DEF InvL2
                  <10> QED
                    BY <10>1, <10>2, <9>2
                <9> QED
                  BY <9>3
              <8> QED
                BY <8>1, <8>2, <8>3
            <7> QED
              BY <7>5, <7>4, <5>19
          <6>4. CASE q \in Sp
            <7> USE <6>4
            <7>1. u.res[q] = ACK
              BY <5>27
            <7>2. i'[q] \in A
              BY <6>1
            <7>3. pc'[q] = 2
              BY <6>2
            <7> QED
              BY <7>1, <7>2, <7>3, <5>19
          <6> QED
            BY <6>3, <6>4
        
        \* Some ad hoc tricks to hide complex definitions for the pf to go through.
        <5> DEFINE G(w) == ValuesMatchInds(seq, w.state)' /\ GoodRes(A, w.res)'       
        <5>33. (\E w \in M' : ValuesMatchInds(seq, w.state)' /\ GoodRes(A, w.res)') = (\E w \in M' : G(w))
          OBVIOUS
        <5> HIDE <3>2 DEF G, u
        <5>34. u \in M' /\ G(u) => (\E w \in M' : G(w))
          OBVIOUS
        <5>35. G(u)
          BY <5>31, <5>32 DEF G
        <5> QED
          BY <5>28, <5>33, <5>34, <5>35
          
      <4> QED
        BY <4>2, <4>3, Zenon
    <3>3. ASSUME NEW p \in ProcSet,
                 L02(p)
          PROVE  InvS1' 
      <4> USE <3>3, AckBotDef DEF L02
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. GoodEnqSet(A)
        BY DEF GoodEnqSet, TypeOK
      <4>2. JInvSeq(seq)
        BY DEF JInvSeq, TypeOK
      <4>3. PICK t \in M : /\ ValuesMatchInds(seq, t.state)
                           /\ GoodRes(A, t.res)
        BY <4>1, <4>2
      <4>4. i[p] \in A
        BY DEF GoodEnqSet, InvL2, TypeOK
      <4>6. ValuesMatchInds(seq, t.state)'
        <5> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                    [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
        <5> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                    [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
        <5>1. vals1 = vals2
          <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                       PROVE  vals1[k] = vals2[k]
            BY Zenon
          <6>1. CASE seq[k] /= i[p]
            <7> USE <6>1
            <7>1. CASE Q[seq[k]] /= BOT
              BY <7>1
            <7>2. CASE Q[seq[k]] = BOT
              <8> USE <7>2
              <8>1. seq[k] \in A
                BY DEF Perm
              <8>2. PICK r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]
                BY <8>1, <4>1 DEF GoodEnqSet
              <8>4. vals1[k] = v[r] /\ vals2[k] = v[r]'
                BY <8>2 DEF InvL2
              <8>5. QED
                BY <8>4
            <7> QED
              BY <7>1, <7>2
          <6>2. CASE seq[k] = i[p]
            <7> USE <6>2
            <7>1. vals1[k] = v[p]
              BY DEF InvL2
            <7>2. vals2[k] = v[p]
              BY DEF TypeOK
            <7> QED
              BY <7>1, <7>2
          <6>3. QED
            BY <6>1, <6>2
        <5>2. QED
          BY <4>3, <5>1, Zenon DEF ValuesMatchInds
      <4>7. GoodRes(A, t.res)'
        BY <4>3, <4>4 DEF GoodRes, TypeOK
      <4> QED
        BY <4>6, <4>7
    <3>4. ASSUME NEW p \in ProcSet,
                 L03(p)
          PROVE  InvS1'
      <4> USE <3>4 DEF L03
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. GoodEnqSet(A)
        BY DEF GoodEnqSet
      <4>2. JInvSeq(seq)
        BY DEF JInvSeq
      <4>3. PICK t \in M : /\ ValuesMatchInds(seq, t.state)
                           /\ GoodRes(A, t.res)
        BY <4>1, <4>2
      <4>4. t.res[p] = ACK
        BY <4>3 DEF GoodRes
      <4>5. DEFINE u == [state |-> t.state, res |-> [t.res EXCEPT ![p] = BOT]]
      <4>6. u \in TupleDomain
        BY <4>3 DEF TupleDomain, TypeOK, tTypeOK
      <4>7. u.state = t.state
        OBVIOUS
      <4>8. u.res[p] = BOT
        BY <4>3 DEF TupleDomain, TypeOK
      <4>9. \A r \in ProcSet : r /= p =>  u.res[r] = t.res[r]
        OBVIOUS
      <4>10. u \in M'
        <5>1. \E t_ \in M : /\ t_.res[p] =ACK
                            /\ u.state = t_.state
                            /\ u.res[p] = BOT
                            /\ \A q \in ProcSet : q /= p =>  u.res[q] = t_.res[q]
          BY <4>3, <4>4, <4>6, <4>7, <4>8
        <5> QED
          BY Isa, <4>6, <5>1 DEF Filter, TypeOK
      <4>11. ValuesMatchInds(seq, u.state)'
        <5> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                    [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
        <5> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                    [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
        <5>1. vals1 = vals2
          <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                       PROVE  vals1[k] = vals2[k]
            BY Zenon
          <6>1. CASE Q[seq[k]] /= BOT
            BY <6>1
          <6>2. CASE Q[seq[k]] = BOT
            <7> USE <6>2
            <7>1. seq[k] \in A
              BY DEF Perm
            <7>2. PICK r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]
              BY <7>1, <4>1 DEF GoodEnqSet
            <7>4. vals1[k] = v[r] /\ vals2[k] = v[r]'
              BY <7>2 DEF InvL2
            <7>5. QED
              BY <7>4
          <6>3. QED
              BY <6>1, <6>2
        <5>2. QED
          BY <4>3, <5>1, Zenon DEF ValuesMatchInds
      <4>12. GoodRes(A, u.res)'
        <5> DEFINE GoodProcRes(q, res) == res[q] = CASE (pc[q] = 2 /\ i[q] \in A) -> ACK
                                                     [] (pc[q] = 3)               -> ACK
                                                     [] (pc[q] = 7)               -> x[q]
                                                     [] OTHER                     -> BOT
        <5>1. \A q \in ProcSet : q /= p => GoodProcRes(q, t.res)'
          BY <4>3 DEF GoodRes
        <5>2. \A q \in ProcSet : q /= p => GoodProcRes(q, u.res)'
          BY <5>1, <4>9
        <5>4. pc'[p] = 0
          BY DEF TypeOK
        <5>5. GoodProcRes(p, u.res)'
          BY <4>8, <5>4
        <5>6. \A r \in ProcSet : GoodProcRes(r, u.res)'
          BY <5>1, <5>5
        <5> QED
          BY <5>6 DEF GoodRes
      <4> QED
        BY <4>10, <4>11, <4>12
    <3>5. ASSUME NEW p \in ProcSet,
                 L04(p)
          PROVE  InvS1'
      <4> USE <3>5 DEF L04
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. GoodEnqSet(A)
        BY DEF GoodEnqSet
      <4>2. JInvSeq(seq)
        BY DEF JInvSeq
      <4>3. PICK t \in M : /\ ValuesMatchInds(seq, t.state)
                           /\ GoodRes(A, t.res)
        BY <4>1, <4>2
      <4>4. ValuesMatchInds(seq, t.state)'
        <5> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                    [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
        <5> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                    [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
        <5>1. vals1 = vals2
          <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                       PROVE  vals1[k] = vals2[k]
            BY Zenon
          <6>1. CASE Q[seq[k]] /= BOT
            BY <6>1
          <6>2. CASE Q[seq[k]] = BOT
            <7> USE <6>2
            <7>1. seq[k] \in A
              BY DEF Perm
            <7>2. PICK r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]
              BY <7>1, <4>1 DEF GoodEnqSet
            <7>4. vals1[k] = v[r] /\ vals2[k] = v[r]'
              BY <7>2 DEF InvL2
            <7>5. QED
              BY <7>4
          <6>3. QED
              BY <6>1, <6>2
        <5>2. QED
          BY <4>3, <5>1, Zenon DEF ValuesMatchInds
      <4>5. GoodRes(A, t.res)'
        BY <4>3 DEF GoodRes
      <4> QED
        BY <4>3, <4>4, <4>5
    <3>6. ASSUME NEW p \in ProcSet,
                 L05(p)
          PROVE  InvS1'
      <4> USE <3>6 DEF L05
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS 
      <4>1. GoodEnqSet(A)
        <5> SUFFICES ASSUME NEW k \in (1..L - 1)
                     PROVE /\ Q[k] /= BOT => k \in A
                           /\ (k \in A /\ Q[k] = BOT) => \E r \in ProcSet : /\ pc[r] = 2 
                                                                              /\ i[r] = k
          BY DEF GoodEnqSet
        <5>1. CASE Q[k] /= BOT
          BY <5>1 DEF GoodEnqSet
        <5>2. CASE k \in A /\ Q[k] = BOT
          <6> USE <5>2
          <6>1. PICK r \in ProcSet : /\ pc'[r] = 2 
                                   /\ i'[r] = k
            BY DEF GoodEnqSet
          <6>2. /\ pc[r] = 2
                /\ i[r] = k
            BY <6>1 DEF TypeOK
          <6> QED
            BY <6>2
        <5> QED
          BY <5>1, <5>2
      <4>2. \A q \in ProcSet : q /= p => /\ pc[q] = pc'[q]
                                         /\ l[q] = l'[q]
                                         /\ j[q] = j'[q]
        <5>1. CASE l[p] = 1
          BY <5>1 DEF TypeOK
        <5>2. CASE l[p] /= 1
          BY <5>2 DEF TypeOK
        <5> QED
          BY <5>1, <5>2
      <4>3. Len(seq) = Cardinality(A)
        <5>1. IsFiniteSet(1..(L-1))
          BY FS_Interval, Isa DEF TypeOK
        <5>2. IsFiniteSet(A)
          BY <5>1, FS_Subset, Isa
        <5> QED
          BY <5>2, PermLength
      <4>4. JInvSeq(seq)
        <5> SUFFICES ASSUME NEW m \in 1..Len(seq), NEW n \in 1..Len(seq),
                            /\ n < m
                            /\ seq[n] > seq[m]
                            /\ Q[seq[m]] # BOT
                     PROVE  \E q \in ProcSet : /\ pc[q] = 6
                                               /\ seq[n] < l[q]
                                               /\ seq[m] < j[q]
          BY DEF JInvSeq
        <5>1. Q'[seq[m]] # BOT
          OBVIOUS
        <5>2. PICK q \in ProcSet : /\ pc'[q] = 6
                                   /\ seq[n] < l'[q]
                                   /\ seq[m] < j'[q]
          BY DEF JInvSeq
        <5>3. CASE q /= p
          BY <5>2, <5>3, <4>2 DEF TypeOK
        <5>4. CASE q = p
          <6> USE <5>4
          <6>1. CASE l[p] = 1
            <7>1. pc'[p] = 4
              BY <6>1 DEF TypeOK
            <7> QED
              BY <7>1, <5>2
          <6>2. CASE l[p] /= 1
            <7>1. j'[p] = 1
               BY <6>2 DEF TypeOK
            <7>2. seq[m] < 1
              BY <5>2, <7>1
            <7>3. seq[m] \in A
              BY <4>3 DEF Perm
            <7>4. seq[m] \in 1..L - 1
              BY <7>3
            <7> QED
              BY <7>2, <7>4
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>3, <5>4
      <4>5. PICK t \in M : /\ ValuesMatchInds(seq, t.state)
                           /\ GoodRes(A, t.res)
        BY <4>1, <4>4
      <4>6. ValuesMatchInds(seq, t.state)'
        <5> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                    [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
        <5> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                    [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
        <5>1. vals1 = vals2
          <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                       PROVE  vals1[k] = vals2[k]
            BY Zenon
          <6>1. CASE Q[seq[k]] /= BOT
            BY <6>1
          <6>2. CASE Q[seq[k]] = BOT
            <7> USE <6>2
            <7>1. seq[k] \in A
              BY DEF Perm
            <7>2. PICK q \in ProcSet : pc[q] = 2 /\ i[q] = seq[k]
              BY <7>1, <4>1 DEF GoodEnqSet
            <7>3. q /= p
              BY <7>2
            <7>4. vals1[k] = v[q]
              BY <7>2 DEF InvL2
            <7>6. pc'[q] = 2 /\ i'[q] = seq[k]
              BY <7>2, <7>3 DEF TypeOK
            <7>7. \A r \in ProcSet : (pc[r] = 2 /\ i[r] = seq[k]) => q = r
              BY <7>2, <2>4 DEF InvL2
            <7>8. \A r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seq[k]) => q = r
              BY <4>2, <7>7 DEF TypeOK
            <7>9. vals2[k] = v'[q]
              BY <7>6, <7>8
            <7>10. v[q] = v[q]'
              BY <7>4, Isa DEF TypeOK
            <7> QED
              BY <7>4, <7>9, <7>10
          <6>3. QED
              BY <6>1, <6>2
        <5>2. QED
          BY <4>5, <5>1, Zenon DEF ValuesMatchInds
      <4>7. GoodRes(A, t.res)'
        BY <4>5 DEF GoodRes, TypeOK
      <4> QED
        BY <4>6, <4>7
    <3>7. ASSUME NEW p \in ProcSet,
                 L06(p)
          PROVE  InvS1'
      <4> USE <3>7 DEF L06
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. \A q \in ProcSet : q /= p => /\ pc[q] = pc'[q]
                                         /\ l[q] = l'[q]
                                         /\ j[q] = j'[q]
        <5>1. CASE Q[j[p]] = BOT
          <6> USE <5>1
          <6>1. CASE j[p] = l[p] - 1
            BY <6>1 DEF TypeOK
          <6>2. CASE j[p] /= l[p] - 1
            BY <6>2 DEF TypeOK
          <6> QED 
            BY <6>1, <6>2
        <5>2. CASE Q[j[p]] /= BOT
          BY <5>2 DEF TypeOK
        <5> QED
          BY <5>1, <5>2
      <4>2. Len(seq) = Cardinality(A)
        <5>1. IsFiniteSet(1..(L-1))
          BY FS_Interval, Isa DEF TypeOK
        <5>2. IsFiniteSet(A)
          BY <5>1, FS_Subset, Isa
        <5> QED
          BY <5>2, PermLength
      <4>3. CASE Q[j[p]] = BOT
        <5> USE <4>3
        <5>1. GoodEnqSet(A)
          BY <4>1 DEF GoodEnqSet, TypeOK
        <5>2. JInvSeq(seq)
          <6> SUFFICES ASSUME NEW m \in 1..Len(seq), NEW n \in 1..Len(seq),
                              /\ n < m
                              /\ seq[n] > seq[m]
                              /\ Q[seq[m]] # BOT
                       PROVE  \E q \in ProcSet : /\ pc[q] = 6
                                                 /\ seq[n] < l[q]
                                                 /\ seq[m] < j[q]
            BY DEF JInvSeq
          <6>1. PICK q \in ProcSet : /\ pc'[q] = 6
                                     /\ seq[n] < l'[q]
                                     /\ seq[m] < j'[q]
            BY DEF JInvSeq
          <6>2. CASE q /= p
            BY <6>1, <6>2, <4>1
          <6>3. CASE q = p
            <7> USE <6>3
            <7>1. CASE j[p] = l[p] - 1
              BY <7>1, <6>1
            <7>2. CASE j[p] /= l[p] - 1
              <8> USE <7>2
              <8>1. j' = [j EXCEPT ![p] = j[p] + 1]
                BY DEF TypeOK
              <8>2. j'[p] = j[p] + 1
                BY <8>1 DEF TypeOK
              <8>3. seq[m] /= j[p]
                BY <6>1
              <8>4. seq[m] < j[p] + 1
                BY <6>1, <8>2, <8>3 DEF TypeOK
              <8>5. m \in 1..Cardinality(A)
                BY <4>2, Isa DEF Perm
              <8>6. seq[m] \in Nat
                <9>1. seq[m] \in A
                  BY <8>5 DEF Perm
                <9>2. seq[m] \in (1..(L' - 1))
                  BY Isa, <9>1
                <9> QED
                  BY <9>2 DEF TypeOK
              <8>7. seq[m] < j[p]
                BY <8>4, <8>3, <8>6 DEF TypeOK
              <8> QED
                BY <8>7, <6>1
            <7> QED
              BY <7>1, <7>2
          <6> QED
            BY <6>2, <6>3
        <5>3. PICK t \in M : ValuesMatchInds(seq, t.state) /\ GoodRes(A, t.res)
          BY <5>1, <5>2
        <5>4. ValuesMatchInds(seq, t.state)'
          <6> DEFINE vals1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] /= BOT -> Q[seq[k]]
                                                      [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = 2 /\ i[r] = seq[k]]]
          <6> DEFINE vals2 == [k \in DOMAIN seq |-> CASE Q[seq[k]]' /= BOT -> Q[seq[k]]'
                                                      [] OTHER             -> v'[CHOOSE r \in ProcSet : pc[r]' = 2 /\ i[r]' = seq[k]]]
          <6>1. vals1 = vals2
            <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE  vals1[k] = vals2[k]
              BY Zenon
            <7>1. CASE Q[seq[k]] # BOT
              BY <7>1
            <7>2. CASE Q[seq[k]] = BOT
              <8> USE <7>2
              <8>1. seq[k] \in A
                BY DEF Perm
              <8>2. PICK q \in ProcSet : pc[q] = 2 /\ i[q] = seq[k]
                BY <8>1, <5>1 DEF GoodEnqSet
              <8>3. q /= p
                BY <8>2
              <8>4. vals1[k] = v[q]
                BY <8>2 DEF InvL2
              <8>6. pc'[q] = 2 /\ i'[q] = seq[k]
                BY <8>2, <8>3 DEF TypeOK
              <8>7. \A r \in ProcSet : (pc[r] = 2 /\ i[r] = seq[k]) => q = r
                BY <8>2 DEF InvL2
              <8>8. \A r \in ProcSet : (pc'[r] = 2 /\ i'[r] = seq[k]) => q = r
                BY <8>7, <4>1 DEF TypeOK
              <8>9. vals2[k] = v'[q]
                BY <8>6, <8>8
              <8>10. v[q] = v[q]'
                BY <8>4, Isa DEF TypeOK
              <8> QED
                BY <8>4, <8>9, <8>10
            <7>3. QED
              BY <7>1, <7>2
          <6>2. QED
            BY <5>3, <6>1, Zenon DEF ValuesMatchInds
        <5>5. GoodRes(A, t.res)'
          BY <5>3 DEF GoodRes, TypeOK
        <5> QED
          BY <5>3, <5>4, <5>5
      <4>4. CASE Q[j[p]] /= BOT
        <5> USE <4>4
        <5>1. j[p] \notin A
          <6>1. Q'[j[p]] = BOT
            BY DEF TypeOK
          <6>2. DEFINE ActiveProcess == \E r \in ProcSet : /\ pc'[r] = 2
                                                           /\ i'[r] = j[p]
          <6>3. j[p] \in A => ActiveProcess
            BY <6>1 DEF GoodEnqSet
          <6>4. ActiveProcess => Q[j[p]] = BOT
            BY DEF InvL2, TypeOK
          <6> QED
            BY <6>3, <6>4
            
        <5> DEFINE A_ == A \union {j[p]}
        <5> DEFINE seq_ == Concat(<<j[p]>>, seq)
        
        <5>2. seq_[1] = j[p]
            BY DEF Concat
        <5>4. Len(seq_) = Len(seq) + 1
          BY DEF Concat
        <5>5. Cardinality(A_) = Cardinality(A) + 1
          <6>1. IsFiniteSet(1..(L-1))
            BY FS_Interval, Isa DEF TypeOK
          <6>2. IsFiniteSet(A)
            BY <6>1, FS_Subset, Isa
          <6>3. QED
            BY <5>1, <6>2, FS_AddElement, FS_CountingElements, FS_EmptySet, Isa
        <5>6. Len(seq_) = Cardinality(A_)
          BY <4>2, <5>4, <5>5
        <5>7. \A k \in (2..(Len(seq) + 1)) : seq_[k] = seq[k - 1]
          BY DEF Concat 
        <5>8. A_ \in SUBSET (1..(L-1))
          <6>1. j[p] \in 1..(L-1)
            BY DEF InvL6, TypeOK
          <6> QED
            BY <6>1
        <5>9. GoodEnqSet(A_)
          <6> SUFFICES ASSUME NEW k \in 1..(L-1)
                       PROVE  /\ Q[k] /= BOT => k \in A_
                              /\ (k \in A_ /\ Q[k] = BOT) => \E q \in ProcSet : /\ pc[q] = 2 
                                                                                /\ i[q] = k
            BY DEF GoodEnqSet
          <6>1. CASE k /= j[p]
            <7> USE <6>1
            <7>1. CASE Q[k] /= BOT
              BY <7>1 DEF GoodEnqSet
            <7>2. CASE k \in A_ /\ Q[k] = BOT
              BY <7>2, <4>1 DEF GoodEnqSet, TypeOK
            <7> QED
              BY <7>1, <7>2
          <6>2. CASE k = j[p]
            BY <6>2
          <6> QED
            BY <6>1, <6>2
          
        <5>10. seq_ \in Perm(A_)
          <6>7. seq_ \in [1..Len(seq_) -> A_]
            <7>1. \A k \in (2..(Len(seq) + 1)) : seq_[k] \in A
              BY <5>7, <4>2 DEF Perm
            <7>2.  \A k \in (1..(Len(seq_))) : seq_[k] \in A_
              BY <5>2, <7>1, <5>4
            <7>3. DOMAIN seq_ = 1..Len(seq_)
              BY DEF Concat
            <7> QED
              BY <7>2, <7>3 DEF Concat
          <6>8. \A w \in A_ : \E k \in 1..Len(seq_) : seq_[k] = w
            <7> SUFFICES ASSUME NEW w \in A_
                                PROVE \E k \in 1..Len(seq_) : seq_[k] = w
              OBVIOUS
            <7>1. CASE w = j[p]
              BY <5>2, <7>1, <5>4
            <7>2. CASE w \in A
              <8> USE <7>2
              <8>1. PICK k \in 1..Len(seq) : seq[k] = w
                BY <4>2 DEF Perm
              <8>2. seq_[k + 1] = w
                BY <8>1, <5>7
              <8> QED
                BY <8>2, <5>4
            <7> QED
              BY <7>1, <7>2
          <6> QED
            BY <5>6, <6>7, <6>8 DEF Perm
        <5>11. JInvSeq(seq_)      
          <6> SUFFICES ASSUME NEW m \in 1..Len(seq_), NEW n \in 1..Len(seq_),
                               /\ n < m
                               /\ seq_[n] > seq_[m]
                               /\ Q[seq_[m]] # BOT
                       PROVE  \E q \in ProcSet : /\ pc[q] = 6
                                                 /\ seq_[n] < l[q]
                                                 /\ seq_[m] < j[q]
            BY DEF JInvSeq
          <6>1. CASE m \in 2..Len(seq_) /\ n \in 2..Len(seq_)
            <7> USE <6>1
            <7>1. n - 1 < m - 1
              OBVIOUS
            <7>2. seq[n - 1] > seq[m - 1]
              BY <5>4, <5>7
            <7>3. Q'[seq[m - 1]] # BOT
              <8>1. Q[seq[m - 1]] # BOT
                BY <5>4, <5>7
              <8>2. seq[m - 1] \in A
                BY <4>2, <5>4 DEF Perm
              <8>3. seq[m - 1] /= j[p]
                BY <5>1, <8>2
              <8> QED
                BY <8>1, <8>3
            <7>4. PICK q \in ProcSet : /\ pc'[q] = 6
                                       /\ seq[n - 1] < l'[q]
                                       /\ seq[m - 1] < j'[q]
              BY <7>1, <7>2, <7>3, <5>4 DEF JInvSeq
            <7>5. /\ seq_[n] < l'[q]
                  /\ seq_[m] < j'[q]
              BY <7>4, <5>7, <5>4
            <7>6. CASE q /= p
              BY <7>4, <7>5, <7>6, <4>1
            <7>7. CASE q = p
              <8>1. pc' = [pc EXCEPT ![p] = 7]
                OBVIOUS
              <8>2. pc'[p] = 7
                BY <8>1 DEF TypeOK
              <8> QED
                BY <8>2, <7>7, <7>4
            <7> QED
              BY <7>6, <7>7
          <6>2. CASE m = 1
            BY <6>2
          <6>3. CASE n = 1
            <7> USE <6>3
            <7>1. seq_[n] < l[p]
              BY <5>2 DEF InvL6
            <7>2. seq_[m] < j[p]
              BY <5>2
            <7> QED
              BY <7>1, <7>2
          <6> QED
            BY <6>1, <6>2, <6>3
        <5>12. PICK t \in M : /\ ValuesMatchInds(seq_, t.state)
                              /\ GoodRes(A_, t.res)
          BY <5>8, <5>9, <5>10, <5>11
          
        <5>13. DEFINE u == [state |-> Tl(t.state), res |-> [t.res EXCEPT ![p] = Hd(t.state)]]
        
        <5>14. u.res[p] = Hd(t.state)
          BY DEF TypeOK, TupleDomain
        <5>15. u \in M'
          <6>1. u.state = Tl(t.state)
            OBVIOUS
          <6>2. \A r \in ProcSet : r /= p => u.res[r] = t.res[r]
            OBVIOUS
          <6>3. \E t_ \in M : /\ u.state = Tl(t_.state)
                              /\ u.res[p] = Hd(t_.state)
                              /\ \A r \in ProcSet : r /= p => u.res[r] = t_.res[r]
            BY <5>14, <6>1, <6>2
          <6>4. t.state \in [1..Len(t.state) -> Nat]
            BY DEF TupleDomain, TypeOK, Seqs
          <6>5. Hd(t.state) \in Nat \union {BOT}
            BY <6>4 DEF Hd
          <6>6. u \in TupleDomain
            <7>2. u.state \in [1..(Len(t.state) - 1) -> Nat]
              BY <6>4 DEF Tl
            <7>3. Len(t.state) < 1 => u.state \in [1..0 -> Nat]
              BY <7>2
            <7>4. u.state \in Seqs(Nat)
              BY <7>2, <7>3 DEF Seqs
            <7>5. Hd(t.state) \in Nat \union {BOT}
              BY <6>5 DEF Hd
            <7>6. u.res \in [ProcSet -> Nat \union {ACK, BOT}]
              BY <7>5 DEF TupleDomain, TypeOK, tTypeOK
            <7> QED
              BY <7>4, <7>6 DEF TupleDomain, TypeOK  
          <6>7. tTypeOK(u)'
            <7> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  /\ pc'[q] \in {0, 1, 4, 5, 6}  => u.res[q] = BOT
                                /\ pc'[q] \in {2, 3}           => u.res[q] \in {ACK, BOT}
                                /\ pc'[q] = 7                  => u.res[q] \in Nat \union {BOT}
              BY DEF tTypeOK
            <7>1. CASE q = p
              <8> USE <7>1
              <8>1. pc'[q] = 7 /\ x'[q] /= BOT
                BY DEF TypeOK
              <8> QED
                BY <8>1, <6>5, <5>14
            <7>2. CASE q /= p
              BY <7>2, <4>1, <6>2 DEF TypeOK, tTypeOK
            <7> QED
              BY <7>1, <7>2
          <6> QED
            BY <6>3, <6>6, <6>7
            
        <5>16. ValuesMatchInds(seq, u.state)'
          <6> DEFINE vals == [k \in DOMAIN seq |-> CASE Q'[seq[k]] /= BOT -> Q'[seq[k]]
                                                     [] OTHER             -> v'[CHOOSE r \in ProcSet : pc'[r] = 2 /\ i[r] = seq[k]]]
          <6>1. u.state \in [DOMAIN seq -> Nat]
            <7>1. DOMAIN u.state = 1..(Len(t.state) - 1)
              BY DEF Tl
            <7>2. Len(seq_) = Len(t.state)
              BY <5>12 DEF ValuesMatchInds
            <7>3. DOMAIN u.state = 1..Len(seq)
              BY <7>1, <7>2, <5>4
            <7>4. u.state \in Seqs(Nat)
              BY <2>1, <5>15 DEF TypeOK, TupleDomain
            <7>5. DOMAIN seq = 1..Len(seq)
              BY DEF Perm
            <7> QED
              BY <7>3, <7>4, <7>5 DEF Seqs
          <6>2. vals \in [DOMAIN seq -> Nat]
            <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE  vals[k] \in Nat
              OBVIOUS
            <7>1. CASE Q'[seq[k]] /= BOT
              BY <7>1 DEF TypeOK, Perm
            <7>2. CASE Q'[seq[k]] = BOT
              <8> USE <7>2
              <8>1. seq[k] \in A
                BY DEF Perm
              <8>2. PICK r \in ProcSet : pc'[r] = 2 /\ i[r] = seq[k]
                BY <8>1, Isa DEF GoodEnqSet
              <8>3. \A r_ \in ProcSet : pc'[r_] = 2 /\ i[r_] = seq[k] => r_ = r
                BY <8>2 DEF InvL2, TypeOK
              <8>4. vals[k] = v'[r]
                BY <8>2, <8>3
              <8> QED
                BY <8>4 DEF TypeOK
            <7> QED
              BY <7>1, <7>2
            
          <6>3. \A k \in DOMAIN seq : u.state[k] = vals[k]
            <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE  u.state[k] = vals[k]
              BY Zenon
            <7>1. seq[k] /= j[p]
              <8>1. seq[k] \in A
                BY DEF Perm
              <8>2. QED
                BY <8>1, <5>1
            <7>2. k \in 1..Len(u.state)
              BY <6>1
                
            <7>3. Len(u.state) = Len(t.state) - 1
              <8>1. Len(t.state) >= 1 
                BY <5>4, <5>12 DEF ValuesMatchInds 
              <8> QED
                BY <8>1 DEF Tl
                
            <7>4. u.state[k] = t.state[k + 1]
              BY <7>2, <7>3 DEF Tl
            <7>5. Len(u.state) = Len(seq)
              BY <6>1
            <7>6. seq[k] = seq_[k + 1]
              BY <5>7, <7>5, <7>2
            <7>7. k \in 1..Len(seq)
              BY <7>2, <7>5 DEF Perm
            <7>8. k + 1 \in DOMAIN seq_
              BY <7>7, <5>4 DEF Concat
            <7>9. Q[seq[k]] = Q'[seq[k]]
              BY <7>1
            <7>11. CASE Q'[seq[k]] /= BOT
              <8> USE <7>11
              <8>1. Q[seq_[k + 1]] = t.state[k + 1]
                BY <7>6, <7>8, <5>12 DEF ValuesMatchInds
              <8> QED
                BY <7>4, <7>6, <8>1, <7>9
            <7>12. CASE Q'[seq[k]] = BOT
              <8> USE <7>12
              <8>1. Q[seq_[k + 1]] = BOT
                BY <7>9, <7>6
              <8>2. seq[k] \in A
                BY DEF Perm
              <8>3. seq_[k + 1] \in A_
                BY <7>6, <8>2
              <8>4. PICK q \in ProcSet : /\ pc[q] = 2
                                         /\ i[q] = seq_[k + 1]                
                BY <5>9, <5>8, <8>1, <8>3 DEF GoodEnqSet
              <8>5. \A r \in ProcSet : (/\ pc[r] = 2
                                        /\ i[r] = seq_[k + 1]) => r = q
                BY <8>4 DEF InvL2
              <8>6. t.state[k + 1] = v[q]
                BY <7>6, <7>8, <8>1, <8>4, <8>5, <5>12 DEF ValuesMatchInds
              <8>8. /\ pc'[q] = 2
                    /\ i[q] = seq[k]
                BY <8>4, <7>6 DEF TypeOK
              <8>9. \A r \in ProcSet : (/\ pc'[r] = 2
                                        /\ i[r] = seq[k]) => r = q
                <9>1. \A r \in ProcSet : pc'[r] = 2 => r /= p
                  BY DEF TypeOK
                <9> QED
                  BY <4>1, <8>5, <7>6, <9>1 DEF InvL2
              <8>10. vals[k] = v[q]
                BY <8>4, <8>8, <8>9
              <8> QED
                BY <8>10, <8>6, <7>4 DEF TypeOK
            <7> QED
              BY <7>11, <7>12
          <6> QED
            BY <6>1, <6>2, <6>3, Isa DEF ValuesMatchInds

        <5>17. GoodRes(A, u.res)'
          <6> DEFINE GoodProcRes(S, res, q) == res[q] = CASE (pc[q] = 2 /\ i[q] \in S) -> ACK
                                                          [] (pc[q] = 3)               -> ACK
                                                          [] (pc[q] = 7)               -> x[q]
                                                          [] OTHER                     -> BOT
          <6> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  GoodProcRes(A, u.res, q)'
            BY DEF GoodRes
          <6>1. CASE q /= p
            <7> USE <6>1
            <7>1. GoodProcRes(A_, u.res, q)
              BY <5>12 DEF GoodRes
            <7>2. ~(pc[q] = 2 /\ i[q] = j[p])
              BY DEF InvL2
            <7> QED
              BY <4>1, <7>1, <7>2
          <6>2. CASE q = p
            <7> USE <6>2
            <7>1. t.state[1] = Q[j[p]]
              BY <5>12, <5>2, <5>4 DEF ValuesMatchInds
            <7>2. t.state /= <<>>
              BY <5>12, <5>4 DEF ValuesMatchInds
            <7>3. u.res[p] = t.state[1]
              BY <7>2, <5>14 DEF Hd
            <7> QED
              BY <7>1, <7>3 DEF TypeOK
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>15, <5>16, <5>17
      <4> QED
        BY <4>3, <4>4
    <3>8. ASSUME NEW p \in ProcSet,
                 L07(p)
          PROVE  InvS1'
      <4> USE <3>8 DEF L07
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. GoodEnqSet(A)
        BY DEF GoodEnqSet
      <4>2. JInvSeq(seq)
        BY DEF JInvSeq
      <4>3. PICK t \in M : /\ ValuesMatchInds(seq, t.state)
                           /\ GoodRes(A, t.res)
        BY <4>1, <4>2
      <4>4. t.res[p] = x[p]
        BY <4>3 DEF GoodRes
      <4>5. DEFINE u == [state |-> t.state, res |-> [t.res EXCEPT ![p] = BOT]]
      <4>6. u \in TupleDomain
        BY <4>3 DEF TupleDomain, TypeOK, tTypeOK
      <4>7. u.state = t.state
        OBVIOUS
      <4>8. u.res[p] = BOT
        BY <4>3 DEF TupleDomain, TypeOK
      <4>9. \A r \in ProcSet : r /= p =>  u.res[r] = t.res[r]
        OBVIOUS
      <4>10. u \in M'
        <5>1. \E t_ \in M : /\ t_.res[p] = x[p]
                            /\ u.state = t_.state
                            /\ u.res[p] = BOT
                            /\ \A r \in ProcSet : r /= p =>  u.res[r] = t_.res[r]
          BY <4>3, <4>4, <4>6, <4>7, <4>8
        <5> QED
          BY Isa, <4>6, <5>1 DEF Filter, TypeOK
      <4>11. ValuesMatchInds(seq, u.state)'
        BY <4>3, <4>7 DEF ValuesMatchInds, TypeOK
      <4>12. GoodRes(A, u.res)'
        <5> DEFINE GoodProcRes(q, res) == res[q] = CASE (pc[q] = 2 /\ i[q] \in A) -> ACK
                                                     [] (pc[q] = 3)               -> ACK
                                                     [] (pc[q] = 7)               -> x[q]
                                                     [] OTHER                     -> BOT
        <5>1. \A q \in ProcSet : q /= p => GoodProcRes(q, t.res)'
          BY <4>3 DEF GoodRes
        <5>2. \A q \in ProcSet : q /= p => GoodProcRes(q, u.res)'
          BY <5>1, <4>9
        <5>4. pc'[p] = 0
          BY DEF TypeOK
        <5>5. GoodProcRes(p, u.res)'
          BY <4>8, <5>4
        <5>6. \A r \in ProcSet : GoodProcRes(r, u.res)'
          BY <5>1, <5>5
        <5> QED
          BY <5>6 DEF GoodRes
      <4> QED
        BY <4>10, <4>11, <4>12
    <3>9. CASE UNCHANGED vars
      <4> USE <3>9
      <4> SUFFICES ASSUME NEW A \in SUBSET (1..(L'-1)),
                          GoodEnqSet(A)',
                          NEW seq \in Perm(A),
                          JInvSeq(seq)'
                   PROVE  \E t \in M' : /\ ValuesMatchInds(seq, t.state)'
                                        /\ GoodRes(A, t.res)'
        OBVIOUS
      <4>1. PICK t \in M : ValuesMatchInds(seq, t.state) /\ GoodRes(A, t.res)
        BY DEF GoodEnqSet, JInvSeq
      <4>2. GoodRes(A, t.res)' /\ ValuesMatchInds(seq, t.state)'
        BY <4>1 DEF GoodRes, ValuesMatchInds
      <4> QED
        BY <4>1, <4>2
    <3>10. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Inv
<1>3. QED
  BY <1>1, <1>2
                  
THEOREM ImpliedCorrectness == Inv => M # {}
 <1> SUFFICES ASSUME Inv
              PROVE  M # {}
   OBVIOUS
 <1> DEFINE A == {k \in 1..L - 1 : Q[k] /= BOT}
 <1>1. A \in SUBSET 1..(L - 1)
   OBVIOUS
 <1>2. GoodEnqSet(A)
   BY DEF GoodEnqSet
 <1> HIDE DEF A
 <1>3. IsFiniteSet(A)
   <2>1. IsFiniteSet(1..(L-1))
     BY FS_Interval, Isa DEF Inv, TypeOK, PosInts
   <2> QED
     BY <2>1, <1>1, FS_Subset, Isa
 <1>4. A \in SUBSET Int /\ IsFiniteSet(A)
   BY <1>1, <1>3 DEF TypeOK
 <1>5. PICK seq \in [1..Cardinality(A) -> A] : \A m, n \in 1..Cardinality(A) : m < n => seq[m] < seq[n]
   BY WellOrderingPrinciple, <1>4, Zenon DEF Bijection, Surjection
 <1>6. seq \in Perm(A)             
   <2> SUFFICES ASSUME NEW w \in A,
                           \A q \in 1..Cardinality(A) : seq[q] /= w
                PROVE  FALSE
     BY DEF Perm
   <2> DEFINE Image == {seq[k] : k \in 1..Cardinality(A)}
   <2>1. seq \in [1..Cardinality(A) -> Image]
     OBVIOUS
   <2>2. Image \in SUBSET A
     OBVIOUS
   <2>3. w \notin Image
     OBVIOUS
   <2>4. Image \union {w} \in SUBSET A
     BY <2>2
   <2>5. IsFiniteSet(Image)
     BY <1>3, <2>2, FS_Subset
   <2>6. IsFiniteSet(1..Cardinality(A))
     BY <1>3, FS_Interval, FS_CardinalityType
   <2>7. Cardinality(Image) < Cardinality(1..Cardinality(A))
     <3>1. Cardinality(Image \union {w}) = Cardinality(Image) + 1
       BY <2>3, <2>5, FS_AddElement, Zenon
     <3>2. Cardinality(A) >= Cardinality(Image) + 1
       BY <3>1, <1>3, FS_Subset
     <3>3. Cardinality(A) > Cardinality(Image)
       BY <3>2, <2>5, <1>3, FS_CardinalityType
     <3>4. Cardinality(1..Cardinality(A)) = Cardinality(A)
       BY <1>3, FS_Interval, FS_CardinalityType
     <3> QED
       BY <3>3, <3>4
   <2>8. PICK k1, k2 \in 1..Cardinality(A) : k1 # k2 /\ seq[k1] = seq[k2]
     BY FS_PigeonHole, <2>1, <2>5, <2>6, <2>7
   <2>9. CASE k1 < k2
     <5>1. seq[k1] < seq[k2]
       BY <2>9, <1>5
     <5> QED
       BY <2>8, <5>1, Isa
   <2>10. CASE k1 > k2
     <5>1. seq[k1] > seq[k2]
       BY <2>10, <1>5
     <5> QED
       BY <2>8, <5>1, Isa
   <2> QED
     BY <2>8, <2>9, <2>10
 <1>7. JInvSeq(seq)
   <2> SUFFICES ASSUME NEW m \in 1..Len(seq), NEW n \in 1..Len(seq),
                       /\ n < m
                       /\ seq[n] > seq[m]
                       /\ Q[seq[m]] # BOT
                PROVE  \E p \in ProcSet : /\ pc[p] = 6
                                          /\ seq[n] < l[p]
                                          /\ seq[m] < j[p]
     BY DEF JInvSeq
   <2>1. Len(seq) = Cardinality(A)
     BY PermLength, <1>3, <1>6
   <2>2. m \in 1..Cardinality(A) /\ n \in 1..Cardinality(A)
     BY <2>1
   <2>4. seq[n] < seq[m]
     BY <1>5, <2>2 DEF Perm
   <2>5. /\ seq[n] \in 1..L - 1
         /\ seq[m] \in 1..L - 1
     BY <2>2, <1>1, Zenon DEF Perm
   <2> QED
     BY <2>4, <2>5
 <1> HIDE <1>5
 <1>8. \E t \in M : /\ ValuesMatchInds(seq, t.state)
                    /\ GoodRes(A, t.res)
   BY <1>1, <1>2, <1>7, <1>6 DEF Inv, InvS1
 <1> QED
   BY <1>8               

\* Final step!
THEOREM AlgCorrectness == Spec => [](M # {})
  BY InductiveInvariance, ImpliedCorrectness, PTL

===================================================================================================
\* Modification History
\* Last modified Wed May 04 12:09:55 EDT 2022 by uguryavuz
\* Created Fri Apr 22 17:58:18 EDT 2022 by uguryavuz
