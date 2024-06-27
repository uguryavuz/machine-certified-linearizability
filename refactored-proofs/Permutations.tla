---------------------------- MODULE Permutations ----------------------------
EXTENDS Sequences, FiniteSetTheorems, TLAPS

(* Set of all permutations of S *)
Perm(S) == {seq \in Seq(S) : /\ Len(seq) = Cardinality(S) 
                             /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]}
                             
(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Every finite set can be permuted.                                       *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Permutation == 
    ASSUME NEW S, IsFiniteSet(S)
    PROVE  Perm(S) # {}
  <1> DEFINE Q(k) == \E seq \in Seq(S) : /\ Len(seq) = k
                                         /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
  <1> DEFINE n == Cardinality(S)
  <1>1. n \in Nat
    BY FS_CardinalityType                               
  <1>2. Q(0)
    <2> seq == << >>
    <2>1. 1..Len(seq) = {}
      OBVIOUS
    <2> QED  
      BY <2>1, Isa
  <1>3. \A k \in 1 .. n : Q(k-1) => Q(k)
    <2> SUFFICES ASSUME NEW k \in 1..n, Q(k-1)
                 PROVE  Q(k)
      OBVIOUS
    <2>1. k \in Nat
      BY FS_CardinalityType, FS_Subset
    <2>2. PICK seq_prev \in Seq(S) : /\ Len(seq_prev) = k-1
                                     /\ \A i, j \in 1..Len(seq_prev) : i # j => seq_prev[i] # seq_prev[j]
      OBVIOUS
    <2> DEFINE T == S \ Range(seq_prev)
    <2>3. T # {}
      <3> DEFINE R == Range(seq_prev)
      <3>1. IsFiniteSet(T)
        BY FS_Difference, Zenon
      <3>2. Cardinality(T) = n - Cardinality(S \cap R)
        BY FS_Difference, Zenon
      <3>3. S \cap R = R \cap S
        OBVIOUS
      <3>4. IsFiniteSet(R)
        BY FS_Subset, FS_Interval DEF Range
      <3>5. IsFiniteSet(S \cap R)
        BY FS_Intersection, Zenon
      <3>6. Cardinality(S \cap R) <= Cardinality(R)
        BY <3>3, <3>4, FS_Intersection, Zenon
      <3>7. R = {seq_prev[x] : x \in DOMAIN seq_prev}
        BY DEF Range
      <3> HIDE DEF R
      <3>8. IsFiniteSet(DOMAIN seq_prev) => Cardinality(R) <= Cardinality(DOMAIN seq_prev)
        BY <3>7, FS_Image, Isa
      <3>9. Cardinality(R) <= k-1
        BY <2>2, <3>8, FS_Interval DEF Seq
      <3>10. Cardinality(T) > n - k
        BY <3>2, <3>4, <3>5, <3>6, <3>9, FS_CardinalityType
      <3>11. k <= n
        OBVIOUS
      <3>12. Cardinality(T) > 0
        BY <3>1, <3>10, <3>11, FS_CardinalityType
      <3> QED
        BY <3>1, <3>12, FS_EmptySet
    <2>4. PICK x \in T : x \notin Range(seq_prev)
      BY <2>3
    <2> DEFINE seq == Append(seq_prev, x)
    <2>5. seq \in Seq(S)
      OBVIOUS
    <2>6. Len(seq) = k
      BY <2>2
    <2>7. \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
      BY <2>2, <2>4 DEF Range
    <2> QED
      BY <2>5, <2>6, <2>7, Zenon
  <1> DEFINE P(k) == Q(n-k)
  <1> HIDE DEF Q
  <1>4. P(n)
    BY <1>1, <1>2
  <1>5. \A k \in 1 .. n : P(k) => P(k-1)
    BY <1>1, <1>3
  <1> HIDE DEF P
  <1>6. P(0)
    BY <1>1, <1>4, <1>5, DownwardNatInduction, Isa
  <1>7. Q(n)
    BY <1>1, <1>6 DEF P
  <1> QED
    BY <1>7 DEF Q, Perm

(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* In the permutation of a set, for each item of the set, there exists     *)
(* an index at which the item is contained at.                             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_PermutationIndex ==
    ASSUME NEW S, NEW x, NEW pi,
           IsFiniteSet(S), x \in S, pi \in Perm(S)
    PROVE  \E i \in 1..Len(pi) : pi[i] = x
  <1> SUFFICES ASSUME \A i \in 1..Len(pi) : pi[i] # x
               PROVE  FALSE
    OBVIOUS
  <1> DEFINE I == 1..Len(pi)
  <1> DEFINE R == Range(pi)
  <1>1. IsFiniteSet(I)
    BY FS_Interval
  <1>2. pi \in [I -> R]
    BY DEF Perm, Range
  <1>3. Cardinality(I) = Cardinality(S)
    BY FS_Interval DEF Perm
  <1>4. x \notin R
    BY DEF Range
  <1>5. R \in SUBSET S
    BY DEF Range, Perm
  <1>6. IsFiniteSet(R)
    BY <1>5, FS_Subset
  <1>7. Cardinality(R) < Cardinality(S)
    BY <1>4, <1>5, FS_Subset, FS_CardinalityType
  <1>8. Cardinality(R) < Cardinality(I)
    BY <1>3, <1>7
  <1>9. \E y, z \in I : y # z /\ pi[y] = pi[z]
    BY <1>1, <1>2, <1>6, <1>8, FS_PigeonHole
  <1> QED
    BY <1>9 DEF Perm

LEMMA MaxElement ==
    ASSUME NEW S, IsFiniteSet(S), S \in SUBSET Int, S # {}
    PROVE  \E x \in S : (\A y \in S : y <= x)
  <1> DEFINE P(T) == T \in SUBSET Int /\ T # {} => \E x \in T : \A y \in T : y <= x
  <1>1. P({})
    OBVIOUS
  <1>2. ASSUME NEW T, NEW x, P(T), x \notin T
        PROVE  P(T \cup {x})
    <2>. HAVE T \cup {x} \in SUBSET Int
    <2>1. CASE \A y \in T : y <= x
      BY <2>1, Isa
    <2>2. CASE \E y \in T : ~(y <= x)
      <3>. T # {}
        BY <2>2
      <3>1. PICK y \in T : \A z \in T : z <= y
        BY <1>2
      <3>2. x <= y
        BY <2>2, <3>1
      <3>3. QED  BY <3>1, <3>2
    <2>. QED  BY <2>1, <2>2
  <1> HIDE DEF P
  <1>3. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
  <1> QED  
    BY <1>3, Zenon DEF P

THEOREM FS_SortedPermutation ==
    ASSUME NEW S, IsFiniteSet(S), S \in SUBSET Int
    PROVE  \E alpha \in Perm(S) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
  <1> DEFINE P(k) == \A T : (IsFiniteSet(T) /\ Cardinality(T) = k /\ T \in SUBSET Int) 
                                => (\E alpha \in Perm(T) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n])
  <1>1. P(0)
    <2> SUFFICES ASSUME NEW T, IsFiniteSet(T), Cardinality(T) = 0, T \in SUBSET Int
                 PROVE  \E alpha \in Perm(T) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
      BY Zenon DEF P
    <2> T = {}
      BY FS_EmptySet
    <2> DEFINE f == [z \in {} |-> z]
    <2>1. f \in Perm({})
      BY FS_EmptySet DEF Perm
    <2> QED
      BY <2>1
  <1>2. \A k \in Nat : P(k) => P(k+1)
    <2> SUFFICES ASSUME NEW k \in Nat, P(k),
                        NEW T, IsFiniteSet(T), Cardinality(T) = k+1, T \in SUBSET Int
                 PROVE  \E alpha \in Perm(T) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
      BY Zenon DEF P
    <2>1. T # {}
      BY FS_EmptySet
    <2>2. PICK max \in T : (\A y \in T : y <= max)
      BY <2>1, MaxElement, Zenon
    <2> DEFINE W == T \ {max}
    <2>3. Cardinality(W) = Cardinality(T) - Cardinality(T \cap {max})
      BY FS_Difference, Zenon
    <2>4. T \cap {max} = {max}
      OBVIOUS
    <2>5. Cardinality(W) = Cardinality(T) - Cardinality({max})
      BY <2>3, <2>4, Zenon
    <2>6. Cardinality(W) = Cardinality(T) - 1
      BY <2>5, FS_Singleton, Zenon
    <2>7. Cardinality(W) = k
      BY <2>6
    <2>8. IsFiniteSet(W) /\ W \in SUBSET Int /\ Cardinality(W) = k 
      BY <2>7, FS_Difference, Zenon
    <2>9. PICK alpha_prev \in Perm(W) : \A m, n \in 1..Len(alpha_prev) : m < n => alpha_prev[m] < alpha_prev[n]
      BY <2>8, Zenon
    <2> DEFINE alpha == alpha_prev \o <<max>>
    <2>10. alpha \in Seq(T)
      BY DEF Perm
    <2>11. Len(alpha) = k + 1
      BY <2>7, <2>9 DEF Perm
    <2>12. \A i, j \in 1..Len(alpha) : i # j => alpha[i] # alpha[j]
      <3> SUFFICES ASSUME NEW i \in 1..Len(alpha), NEW j \in 1..Len(alpha), i # j
                   PROVE  alpha[i] # alpha[j]
        OBVIOUS
      <3>1. CASE i = k+1
        <4> USE <3>1
        <4>1. alpha[j] \in W
          BY <2>9, <2>11 DEF Perm
        <4>2. alpha[j] # max
          BY <4>1
        <4> QED
          BY <2>11, <4>2
      <3>2. CASE j = k+1
        <4> USE <3>2
        <4>1. alpha[i] \in W
          BY <2>9, <2>11 DEF Perm
        <4>2. alpha[i] # max
          BY <4>1
        <4> QED
          BY <2>11, <4>2
      <3>3. CASE i <= k /\ j <= k
        <4> USE <3>3
        <4>1. alpha[i] = alpha_prev[i] /\ alpha[j] = alpha_prev[j]
          BY <2>11
        <4>2. i \in 1..Len(alpha_prev) /\ j \in 1..Len(alpha_prev)
          BY <2>11
        <4>3. alpha_prev[i] # alpha_prev[j]
          BY <2>9, <4>2, Zenon DEF Perm
        <4> QED
          BY <4>1, <4>3
      <3> QED
        BY <2>11, <3>1, <3>2, <3>3
    <2>13. alpha \in Perm(T)
      BY <2>10, <2>11, <2>12, Zenon DEF Perm
    <2>14. \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
      <3> USE <2>2, <2>9, <2>11
      <3> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha), m < n
                   PROVE  alpha[m] < alpha[n]
        OBVIOUS
      <3>1. CASE m = k+1
        BY <3>1
      <3>2. CASE n = k+1
        <4> USE <3>2
        <4>1. alpha[m] \in W
          BY DEF Perm
        <4>2. alpha[m] < max
          BY <4>1, Isa
        <4> QED
          BY <4>2
      <3>3. CASE m <= k /\ n <= k
        BY <3>3
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>13, <2>14, Zenon
  <1>3. \A k \in Nat : P(k)
    <2> HIDE DEF P
    <2> QED  BY <1>1, <1>2, NatInduction, Isa
  <1> QED
    BY <1>3, FS_CardinalityType, Zenon

=============================================================================
\* Modification History
\* Last modified Thu Jan 18 14:18:01 GMT 2024 by uguryavuz
\* Created Fri Jan 05 12:14:16 EST 2024 by uguryavuz
