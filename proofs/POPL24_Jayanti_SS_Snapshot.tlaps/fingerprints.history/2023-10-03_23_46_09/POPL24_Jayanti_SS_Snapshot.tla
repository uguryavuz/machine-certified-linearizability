--------------------- MODULE POPL24_Jayanti_SS_Snapshot ---------------------
(****************************************************************************
Author: Uğur Y. Yavuz, Lizzie Hernández Videa
Date: 2023-09-28

This is the TLA+ specification of Jayanti's single-writer, single-scanner
snapshot algorithm [Jayanti, 2005], and its proof of linearizability in 
TLAPS, using the tracking technique as described in our work
"A Universal, Sound, and Complete Forward Reasoning Technique for 
Machine-Verified Proofs of Linearizability", to appear in POPL 2024.
Specficially, it corresponds to the partial tracker described in
the Appendix.

TYPE: 
    - Write(i, v) for all writing processes p in 1..N,
    - Scan() for the scanner process S, with a unique PID.

CONSTANTS: 
    - K the number of components.
        * M is the number of components in the paper, here we use K to 
          avoid confusion with the meta-configuration M.

MODEL VALUES: 
    * Model values compare false to everything but themselves. 
    - ACK ('ack' in the paper) is a special value that is used to indicate 
      an operation has been completed.
    - BOT (\bot in the paper) is akin to a null value.
    - WriteSet is the set of writing processes.
    - S is the scanner process.

SHARED VARIABLES:
    - A[0..K-1] is a read/write array initialized to the desired initial 
      state of the snapshot.
    - B[0..K-1] is a read/write array, arbitrarily initialized.
    - X is a Boolean, initially false.
  
LOCAL VARIABLES:
    - For each writing process p, i_p and v_p are local variables.
    - For the scanner process S, j is a local variable, and a[0..K-1] is 
      a local array.

ALGORITHM:
    - Write(i, v):
      ------------
      W1: A[i] <- v
      W2: if X:
      W3:   B[i] <- v
      W4: return ACK
          
    - Scan():
      -------
      S1: X <- true
      S2: for j in 0..K-1: do B[j] <- BOT
      S3: for j in 0..K-1: do a[j] <- A[j]
      S4: X <- false
      S5: for j in 0..K-1:
            b <- B[j]
            if b != BOT then a[j] <- b
      S6: return a
                
NOTE: Each line has at most 1 shared memory instruction.
****************************************************************************)

EXTENDS Integers, TLC, FiniteSets, TLAPS

CONSTANTS ACK, BOT, K, WriteSet, S
VARIABLES pc, X, A, B, a, i, v, j, M   \* M is the meta-configuration.
vars == <<pc, X, A, B, a, i, v, j, M>>

\* A few useful definitions.
IndexSet == 0..K-1
ProcSet  == WriteSet \union {S}

\* Map(d, e) is a map with domain {d} and maps d to e.
Map(d, e)  == [x \in {d} |-> e]  

\* Merge(f, g) is the map obtained by merging f and g.
Merge(f,g) == [x \in (DOMAIN f) \union (DOMAIN g) |-> IF x \in DOMAIN f THEN f[x] ELSE g[x]]

\* Assumptions regarding the model values ACK and BOT.
ASSUME AckBotDef == /\ ACK # BOT
                    /\ BOT \notin Nat

\* Assumptions regarding the processes.
ASSUME ProcDef == /\ S \notin WriteSet

\* K is a strictly positive integer.
ASSUME KDef == /\ K \in Nat \ {0}

\* SPECIFICATION

\* The initial predicate.
\* 
\* Notes:
\*   - Observe that j goes up to K, not just K-1.
\*   - The meta-configuration M contains atomic configurations C = (C.sigma, C.f),
\*     where C.f is a triple (op, arg, res). In the TLA+ specification, we use
\*     (sigma, res) = (C.sigma, C.f.res) as the atomic configuration; as op and arg
\*     are uniquely determined by pc, i, and v.
\*   * This helps the TLAPS proof, as it simplifies the data structure needed to
\*     track the execution of the algorithm.
Init == /\ pc = [p \in ProcSet |-> "L0"]
        /\ X = FALSE
        /\ A \in [IndexSet -> Nat]
        /\ B \in [IndexSet -> Nat \union {BOT}]
        /\ a \in [IndexSet -> Nat]
        /\ i \in [WriteSet -> IndexSet]
        /\ v \in [WriteSet -> Nat]
        /\ j \in 0..K   
        /\ M = {[sigma |-> A, 
                 fres  |-> [p \in ProcSet |-> BOT]]}

\* Line 0.
\* Notes:
\*   - Here, idle processes pick operations and corresponding arguments
\*     and invoke the operation with the argument.
L0(p) == /\ pc[p] = "L0"
         /\ IF p \in WriteSet THEN
              \* Ensure that the single-writer property is satisfied as k is picked.
              /\ pc' = [pc EXCEPT ![p] = "W1"]
              /\ \E w \in Nat : v' = [v EXCEPT ![p] = w]
              /\ \E k \in IndexSet : /\ \A q \in WriteSet : pc[q] # "L0" => i[q] # k
                                     /\ i' = [i EXCEPT ![p] = k]
              \* No need to update the meta-configuration; as explained, we only
              \* track the return value.
              /\ UNCHANGED <<X, A, B, a, j, M>>
            ELSE 
              \* Else means p = S, the scanner process.
              /\ pc' = [pc EXCEPT ![p] = "S1"]
              /\ UNCHANGED <<X, A, B, a, i, v, j, M>>

\* W1: A[i] <- v
W1(p) == /\ pc[p] = "W1"
         /\ pc' = [pc EXCEPT ![p] = "W2"]
         /\ A' = [A EXCEPT ![i[p]] = v[p]]
         /\ UNCHANGED <<X, B, a, i, v, j>>
         \* Update the meta-configuration: linearize nothing, or linearize p's operation.
         \* Recall that this is a partial tracker, so we don't have to consider all subsets of
         \* ongoing operations. 
         /\ M' = M \union {[sigma |-> [c.sigma EXCEPT ![i[p]] = v[p]],
                            fres  |-> [c.fres  EXCEPT ![p] = ACK]] : c \in M}

\* W2: if X: (i.e., if X then goto W3 else goto W4)
W2(p) == /\ pc[p] = "W2"
         /\ IF X = TRUE
              THEN pc' = [pc EXCEPT ![p] = "W3"]
              ELSE pc' = [pc EXCEPT ![p] = "W4"]
         /\ UNCHANGED <<X, A, B, a, i, v, j, M>>

\* W3: B[i] <- v
W3(p) == /\ pc[p] = "W3"
         /\ pc' = [pc EXCEPT ![p] = "W4"]
         /\ B' = [B EXCEPT ![i[p]] = v[p]]
         /\ UNCHANGED <<X, A, a, i, v, j, M>>

\* W4: return ACK
W4(p) == /\ pc[p] = "W4"
         /\ pc' = [pc EXCEPT ![p] = "L0"]
         /\ UNCHANGED <<X, A, B, a, i, v, j>>
         \* Update the meta-configuration: filter out configurations that don't match
         \* the return value of p's operation, and reset the return value to BOT.
         /\ M' = {[sigma |-> c.sigma,
                   fres  |-> [c.fres EXCEPT ![p] = BOT]] : c \in {d \in M : d.fres[p] = ACK}}

\* S1: X <- true
S1(p) == /\ pc[p] = "S1"
         /\ pc' = [pc EXCEPT ![p] = "S2"]
         /\ X' = TRUE
         /\ j' = 0    \* Note that j is a loop variable, so it is reset to for S2.
         /\ UNCHANGED <<A, B, a, i, v, M>>

\* S2: for j in 0..K-1: do B[j] <- BOT
S2(p) == /\ pc[p] = "S2"
         /\ IF j < K
              THEN /\ pc' = pc
                   /\ j' = j + 1
                   /\ B' = [B EXCEPT ![j] = BOT]
              ELSE /\ pc' = [pc EXCEPT ![p] = "S3"]
                   /\ j' = 0
                   /\ B' = B
         /\ UNCHANGED <<X, A, a, i, v, M>>

\* S3: for j in 0..K-1: do a[j] <- A[j]
S3(p) == /\ pc[p] = "S3"
         /\ IF j < K
              THEN /\ pc' = pc
                   /\ j' = j + 1
                   /\ a' = [a EXCEPT ![j] = A[j]]
              ELSE /\ pc' = [pc EXCEPT ![p] = "S4"]
                   /\ j' = j
                   /\ a' = a
         /\ UNCHANGED <<X, A, B, i, v, M>>

\* S4: X <- false
S4(p) == /\ pc[p] = "S4"
         /\ pc' = [pc EXCEPT ![p] = "S5"]
         /\ j' = 0
         /\ X' = FALSE
         /\ UNCHANGED <<A, B, a, i, v, j>>
         \* Update the meta-configuration: linearize the scan, followed by the 
         \* ongoing writes past W1. The result of this is a state of A, and S
         \* getting c.sigma as its return value for all c in M.
         /\ M' = {[sigma |-> A,
                   fres  |-> Merge([w \in WriteSet |-> IF pc[w] \in {"W2", "W3", "W4"} THEN ACK ELSE BOT],
                                   Map(S, c.sigma))] : c \in M}

\* S5: for j in 0..K-1:
\*       b <- B[j]
\*       if b != BOT then a[j] <- b
S5(p) == /\ pc[p] = "S5"
         /\ IF j < K
              THEN /\ pc' = pc
                   /\ j' = j + 1
                   /\ IF B[j] # BOT
                        THEN a' = [a EXCEPT ![j] = B[j]]
                        ELSE a' = a
              ELSE /\ pc' = [pc EXCEPT ![p] = "S6"]
                   /\ j' = 0
                   /\ a' = a
         /\ UNCHANGED <<X, A, B, i, v, M>>

\* S6: return a
S6(p) == /\ pc[p] = "S6"
         /\ pc' = [pc EXCEPT ![p] = "L0"]
         /\ UNCHANGED <<X, A, B, a, i, v, j>>
         \* Update the meta-configuration: filter out configurations that don't match
         \* the return value of S's operation, and reset the return value to BOT.
         /\ M' = {[sigma |-> c.sigma,
                   fres  |-> [c.fres EXCEPT ![S] = BOT]] : c \in {d \in M : d.fres[S] = a}}


\* The next-state relation.
Next == \/ \E w \in WriteSet : \/ L0(w)
                               \/ W1(w)
                               \/ W2(w)
                               \/ W3(w)
                               \/ W4(w)
        \/ L0(S)
        \/ S1(S)
        \/ S2(S)
        \/ S3(S)
        \/ S4(S)
        \/ S5(S)
        \/ S6(S)

\* The specification.
Spec == Init /\ [][Next]_vars

\* TYPE CORRECTNESS

\* Type-correctness for f in an atomic configuration.
CFTypeOK(c) == /\ \A w \in WriteSet : /\ pc[w] \in {"L0", "W1"}       => c.fres[w] = BOT
                                      /\ pc[w] \in {"W2", "W3", "W4"} => c.fres[w] \in {ACK, BOT}
               /\ pc[S] \in {"L0", "S1", "S2", "S3", "S4"} => c.fres[S] = BOT
               /\ pc[S] \in {"S5", "S6"}                   => c.fres[S] \in [IndexSet -> Nat]

\* Domain for atomic configurations.
CDomain == {c \in [sigma: [IndexSet -> Nat], 
                   fres:  [ProcSet -> [IndexSet -> Nat] \union {ACK, BOT}]] : CFTypeOK(c)}

\* Type-correctness invariant.
TypeOK == /\ pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}]
          /\ \A w \in WriteSet : pc[w] \in {"L0", "W1", "W2", "W3", "W4"}  \* Writes are restricted to L0, W1, W2, W3, W4.
          /\ pc[S] \in {"L0", "S1", "S2", "S3", "S4", "S5", "S6"}          \* Scan is restricted to L0, S1, S2, S3, S4, S5, S6.
          /\ X \in BOOLEAN
          /\ A \in [IndexSet -> Nat]
          /\ B \in [IndexSet -> Nat \union {BOT}]
          /\ a \in [IndexSet -> Nat]
          /\ j \in 0..K
          /\ i \in [WriteSet -> IndexSet]
          /\ v \in [WriteSet -> Nat]
          /\ \A w1, w2 \in WriteSet : (i[w1] = i[w2] /\ pc[w1] # "L0" /\ pc[w2] # "L0") => w1 = w2 \* Single-writer property.
          /\ M \in SUBSET CDomain

\* Proof of type-correctness.
LEMMA InitTypeSafety == Init => TypeOK
  <1> USE AckBotDef, ProcDef, KDef DEFS TypeOK, Init, Map, Merge, ProcSet
  <1> SUFFICES ASSUME Init
               PROVE  TypeOK
    OBVIOUS
  <1>1. X \in BOOLEAN
      BY Zenon
  <1>2. M \in SUBSET CDomain
    BY DEF CDomain, CFTypeOK
  <1> QED
    BY <1>1, <1>2

LEMMA NextTypeSafety == TypeOK /\ [Next]_vars => TypeOK'
  <1> USE AckBotDef, ProcDef, KDef DEFS TypeOK, Map, Merge, ProcSet, Next, vars, CDomain, CFTypeOK
  <1> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. ASSUME NEW w \in WriteSet,
               L0(w)
        PROVE  TypeOK'
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      BY <1>1 DEF L0
    <2> QED
      BY <1>1, <2>1 DEF L0
  <1>2. ASSUME NEW w \in WriteSet,
               W1(w)
        PROVE  TypeOK'
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      BY <1>2 DEF W1
    <2>2. (\A w_1 \in WriteSet : pc[w_1] \in {"L0", "W1", "W2", "W3", "W4"})'
      BY <1>2 DEF W1
    <2>3. (pc[S] \in {"L0", "S1", "S2", "S3", "S4", "S5", "S6"})'
      BY <1>2 DEF W1
    <2>4. (X \in BOOLEAN)'
      BY <1>2 DEF W1
    <2>5. (A \in [IndexSet -> Nat])'
      BY <1>2 DEF W1
    <2>6. (B \in [IndexSet -> Nat \union {BOT}])'
      BY <1>2 DEF W1
    <2>7. (a \in [IndexSet -> Nat])'
      BY <1>2 DEF W1
    <2>8. (j \in 0..K)'
      BY <1>2 DEF W1
    <2>9. (i \in [WriteSet -> IndexSet])'
      BY <1>2 DEF W1
    <2>10. (v \in [WriteSet -> Nat])'
      BY <1>2 DEF W1
    <2>11. (\A w1, w2 \in WriteSet : (i[w1] = i[w2] /\ pc[w1] # "L0" /\ pc[w2] # "L0") => w1 = w2)'
      BY <1>2 DEF W1
    <2>12. (M \in SUBSET CDomain)'
      <3> SUFFICES ASSUME NEW d \in M'
                   PROVE  d \in CDomain'
        OBVIOUS
      <3> USE <1>2 DEF W1
      <3>1. M' = M \union {[sigma |-> [c.sigma EXCEPT ![i[w]] = v[w]],
                            fres  |-> [c.fres  EXCEPT ![w] = ACK]] : c \in M}
        OBVIOUS
      <3> QED
        BY <3>1
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
    
  <1>3. ASSUME NEW w \in WriteSet,
               W2(w)
        PROVE  TypeOK'
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      BY <1>3 DEF W2
    <2> QED
      BY <1>3, <2>1 DEF W2
  <1>4. ASSUME NEW w \in WriteSet,
                W3(w)
        PROVE  TypeOK'
    BY <1>4 DEF W3
  <1>5. ASSUME NEW w \in WriteSet,
                W4(w)
        PROVE  TypeOK'
    BY <1>5 DEF W4
  <1>6. CASE L0(S)
    BY Zenon, <1>6 DEF L0
  <1>7. CASE S1(S)
    BY <1>7 DEF S1
  <1>8. CASE S2(S)
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      BY <1>8 DEF S2
    <2> QED
      BY <1>8, <2>1 DEF S2
  <1>9. CASE S3(S)
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      BY <1>9 DEF S3
    <2> QED
      BY <1>9, <2>1 DEF S3
  <1>10. CASE S4(S)
    <2> USE <1>10 DEF S4
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      OBVIOUS
    <2>2. (M \in SUBSET CDomain)'
      OBVIOUS
    <2> QED
      BY Zenon, <1>10, <2>1, <2>2
  <1>11. CASE S5(S)
    <2>1. (pc \in [ProcSet -> {"L0", "W1", "W2", "W3", "W4", "S1", "S2", "S3", "S4", "S5", "S6"}])'
      BY <1>11 DEF S5
    <2> QED
      BY <1>11, <2>1 DEF S5
  <1>12. CASE S6(S)
    BY <1>12 DEF S6
  <1>13. CASE UNCHANGED vars
    BY <1>13
  <1> QED
    BY <1>1, <1>10, <1>11, <1>12, <1>13, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Next

THEOREM TypeSafety == Spec => []TypeOK
  <1> SUFFICES /\ (Init => TypeOK)
               /\ (TypeOK /\ [Next]_vars => TypeOK')
    BY PTL DEF Spec
  <1>1. Init => TypeOK
    BY InitTypeSafety
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    BY NextTypeSafety
  <1> QED
    BY <1>1, <1>2

\* REMAINING INVARIANTS
 
\* Some notes on the remaining invariants:
\* 
\* - The correspondence between labels as they appear in the Appendix is as follows:
\*    - W1 (A[i] <- v)  -> 2
\*    - W2 (if X)       -> 3
\*    - W3 (B[i] <- v)  -> 4
\*    - W4 (return ack) -> 5
\*    - S1 (X <- true)                                              -> 7
\*    - S2 (for j in 0..K-1: do B[j] <- BOT)                        -> 8
\*    - S3 (for j in 0..K-1: do a[j] <- A[j])                       -> 9
\*    - S4 (X <- false)                                             -> 10
\*    - S5 (for j in 0..K-1: b <- B[j]; if b != BOT then a[j] <- b) -> 11
\*    - S6 (return a)                                               -> 12
\*
\* - By the definitions of TypeOK, CFTypeOK, and CDomain, we have that
\*   all type invariants and I_{1, 6}, I_{3, 4, 5}, I_{7, 8, 9, 10}, I_{11, 12},
\*   I_C (as defined in the paper) are all superceded by TypeOK. 
\*    * The second conjunct of I_2 is also superceded,
\*      but not the first conjunct that deals with the sigma and the state.
\*

\* Set of possible scanner return values for the k-th component.
KthReturnSet(k) == CASE pc[S] = "L0" -> {A[k]}
                     [] pc[S] = "S1" -> {A[k]}
                     [] pc[S] = "S2" -> (CASE (k < j /\ B[k] # BOT) -> {A[k], B[k]}
                                           [] OTHER                 -> {A[k]})
                     [] pc[S] = "S3" -> (CASE (B[k] # BOT)          -> {A[k], B[k]}
                                           [] (k < j /\ B[k] = BOT) -> {A[k], a[k]}
                                           [] OTHER                 -> {A[k]})
                     [] pc[S] = "S4" -> (CASE (B[k] # BOT)          -> {A[k], B[k]}
                                           [] OTHER                 -> {A[k], a[k]})
                     [] pc[S] = "S5" -> LET WBk == (\E w \in WriteSet : pc[w] = "W3" /\ i[w] = k)
                                        IN (CASE (WBk  /\ B[k] # BOT /\ k >= j) -> {A[k], B[k]}
                                              [] (WBk  /\ B[k] = BOT /\ k >= j) -> {A[k], a[k]}
                                              [] (~WBk /\ B[k] # BOT /\ k >= j) -> {B[k]}
                                              [] OTHER                          -> {a[k]})
                     [] pc[S] = "S6" -> {a[k]}

\* Set of possible scanner return values.
ScanReturnSet == {f \in [IndexSet -> UNION {KthReturnSet(k) : k \in IndexSet}] 
                    : (\A k \in IndexSet : f[k] \in KthReturnSet(k))}

\* The linearizability invariant (I_L) as described in the paper.
Linearizable == M # {}

\* The first conjunct of I_2 as described in the paper.
Inv_W0 == \A p \in WriteSet : \A c \in M : pc[p] = "W1" => c.sigma[i[p]] = A[i[p]]

\* I_W1 as described in the paper.
Inv_W1 == \A p \in WriteSet : \A c \in M : 
             (pc[p] \in {"W2", "W3", "W4"} /\ c.sigma[i[p]] # A[i[p]]) => c.fres[p] = BOT

\* I_W2 as described in the paper.
Inv_W2 == \A p \in WriteSet : \A c \in M : 
             (pc[p] \in {"W2", "W3", "W4"} => (\E d \in M : /\ d.sigma = [c.sigma EXCEPT ![i[p]] = A[i[p]]]
                                                            /\ d.fres = [c.fres EXCEPT ![p] = ACK]))

\* I_W3 as described in the paper.
Inv_W3 == \A p \in WriteSet : (pc[p] \in {"W2", "W3", "W4"} => A[i[p]] = v[p])

\* I_W4 as described in the paper.
\* Note that the negation has been pushed inside the conjunction to obtain a disjunction.
\* This makes the proof easier.
Inv_W4 == \A k \in IndexSet : \A c \in M : 
             (\A p \in WriteSet : (pc[p] \in {"L0", "W1"} \/ i[p] # k)) => c.sigma[k] = A[k]

\* I_S1 as described in the paper. Note that S is fixed in the implementation, so we don't quantify 
\* over all processes, but reason with respect to S.
Inv_S1 == pc[S] \in {"S2", "S3", "S4"} <=> X = TRUE

\* I_S2 as described in the paper. Same observation regarding S applies here.
\* Also observe that the negation has been pushed inside the conjunction to obtain an implication.
Inv_S2 == \A k \in IndexSet : (/\ B[k] = BOT
                               /\ (pc[S] = "S4" \/ (pc[S] = "S3" /\ k < j))
                               /\ (\A w \in WriteSet : i[w] = k => pc[w] \in {"L0", "W1", "W4"}))
                              => A[k] = a[k]

\* I_S3 as described in the paper. Same observation regarding S applies here.
\* We once again express the negated conjunct as an implication.
Inv_S3 == \A k \in IndexSet : (/\ B[k] # BOT
                               /\ (pc[S] = "S4" \/ pc[S] = "S3" \/ (pc[S] = "S2" /\ k < j))
                               /\ (\A w \in WriteSet : i[w] = k => pc[w] \in {"L0", "W1", "W4"}))
                              => A[k] = B[k]

\* I_M1 as described in the paper.
\* The second conjunct in the existential quantifier is superceded by TypeOK (by how we defined CFTypeOK).
Inv_M1 == \A alpha \in ScanReturnSet : 
              pc[S] \in {"L0", "S1", "S2", "S3", "S4"} => (\E c \in M : c.sigma = alpha)

\* I_M2 as described in the paper.
Inv_M2 == \A alpha \in ScanReturnSet : 
              pc[S] \in {"S5", "S6"} => (\E c \in M : /\ c.sigma = A
                                                      /\ c.fres[S] = alpha)

\* Full inductive invariant.
Inv == /\ TypeOK
       /\ Inv_W0
       /\ Inv_W1
       /\ Inv_W2
       /\ Inv_W3
       /\ Inv_W4
       /\ Inv_S1
       /\ Inv_S2
       /\ Inv_S3
       /\ Inv_M1
       /\ Inv_M2
       /\ Linearizable

\* Proof of inductive invariant.
THEOREM InductiveInvariant == Spec => []Inv
  <1> USE AckBotDef, ProcDef, KDef DEF Inv, ProcSet
  <1> SUFFICES /\ (Init => Inv)
               /\ (Inv /\ [Next]_vars => Inv')
    BY PTL DEF Spec
  <1>1. Init => Inv
    <2> SUFFICES ASSUME Init
                 PROVE  Inv
      OBVIOUS
    <2> USE DEF Init
    <2>1. TypeOK
      BY InitTypeSafety
    <2>2. Inv_W0
      BY DEF Inv_W0 
    <2>3. Inv_W1
      BY DEF Inv_W1
    <2>4. Inv_W2
      BY DEF Inv_W2
    <2>5. Inv_W3
      BY DEF Inv_W3
    <2>6. Inv_W4
      BY DEF Inv_W4
    <2>7. Inv_S1
      BY DEF Inv_S1
    <2>8. Inv_S2
      BY DEF Inv_S2
    <2>9. Inv_S3
      BY DEF Inv_S3
    <2>10. Inv_M1
      BY DEF Inv_M1, ScanReturnSet, KthReturnSet
    <2>11. Inv_M2
      BY DEF Inv_M2
    <2>12. Linearizable
      BY Zenon DEF Linearizable
    <2> QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Inv
  <1>2. Inv /\ [Next]_vars => Inv'
    <2> SUFFICES ASSUME Inv,
                        [Next]_vars
                 PROVE  Inv'
      OBVIOUS
    <2>1. TypeOK'
      BY NextTypeSafety
    <2> USE DEF TypeOK
    <2>2. Inv_W0'
      <3> USE DEF Inv_W0
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_W0'
        BY <3>1 DEF L0, Inv_W4
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_W0'
        BY <3>2 DEF W1, CDomain, CFTypeOK
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_W0'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_W0'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_W0'
        BY <3>5 DEF W4
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3> HIDE DEF TypeOK
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3> USE DEF TypeOK
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>3. Inv_W1'
      <3> USE DEF Inv_W1
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_W1'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_W1'
        BY <3>2 DEF W1, CDomain, CFTypeOK
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_W1'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_W1'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_W1'
        BY <3>5 DEF W4, CDomain, CFTypeOK
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3> HIDE DEF TypeOK
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3> USE DEF TypeOK
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6, CDomain, CFTypeOK
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>4. Inv_W3'
      <3> USE DEF Inv_W3
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_W3'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_W3'
        BY <3>2 DEF W1
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_W3'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_W3'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_W3'
        BY <3>5 DEF W4
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>5. Inv_W2'
      <3> USE DEF Inv_W2
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_W2'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_W2'
        <4> USE <3>2 DEF W1, Inv_W2
        <4> SUFFICES ASSUME NEW p \in WriteSet,
                            NEW c \in M',
                            pc'[p] \in {"W2", "W3", "W4"}
                     PROVE  (\E d \in M' : /\ d.sigma = [c.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
                                           /\ d.fres = [c.fres EXCEPT ![p] = ACK])
          BY Zenon
        <4>1. CASE w = p
          <5> USE <4>1
          <5>1. CASE c \in M
            <6>1. PICK d \in M' : d = [sigma |-> [c.sigma EXCEPT ![i[p]] = v[p]], 
                                       fres |-> [c.fres EXCEPT ![p] = ACK]]
              BY <5>1, Zenon
            <6> QED
              BY <6>1, Zenon
          <5> HIDE DEF TypeOK
          <5>2. CASE c \notin M
            BY <2>4, <5>2 DEF Inv_W3
          <5> QED
            BY Zenon, <5>1, <5>2
        <4>2. CASE w # p
          <5> USE <4>2
          <5>1. CASE c \in M
            <6>1. PICK d \in M : /\ d.sigma = [c.sigma EXCEPT ![i[p]] = A[i[p]]]
                                 /\ d.fres  = [c.fres EXCEPT ![p] = ACK]
              BY <5>1, Zenon
            <6> QED
              BY <5>1, <6>1
          <5>2. CASE c \notin M
            <6> USE <5>2
            <6>1. PICK c_pred \in M : c = [sigma |-> [c_pred.sigma EXCEPT ![i[w]] = v[w]], 
                                           fres  |-> [c_pred.fres  EXCEPT ![w]    = ACK]]
              OBVIOUS
            <6>2. PICK d_pred \in M : /\ d_pred.sigma = [c_pred.sigma EXCEPT ![i[p]] = A[i[p]]]
                                      /\ d_pred.fres  = [c_pred.fres  EXCEPT ![p] = ACK]
              OBVIOUS
            <6>3. PICK d \in M' : d = [sigma |-> [d_pred.sigma EXCEPT ![i[w]] = v[w]], 
                                       fres  |-> [d_pred.fres  EXCEPT ![w]    = ACK]]
              BY Zenon
            <6>4. d.sigma = [c.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
              BY ZenonT(15), <6>1, <6>2, <6>3
            <6>5. d.fres = [c.fres EXCEPT ![p] = ACK]
              BY Zenon, <6>1, <6>2, <6>3
            <6> QED
              BY <6>4, <6>5
          <5> QED
            BY Zenon, <5>1, <5>2
        <4> QED
          BY <4>1, <4>2
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_W2'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_W2'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_W2'
        <4> USE <3>5 DEF W4
        <4> SUFFICES ASSUME NEW p \in WriteSet,
                            NEW c \in M',
                            pc'[p] \in {"W2", "W3", "W4"}
                     PROVE  (\E d \in M' : /\ d.sigma = [c.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
                                           /\ d.fres = [c.fres EXCEPT ![p] = ACK])
          BY Zenon DEF Inv_W2
        <4>1. PICK d_pred_pred \in M : /\ c = [sigma |-> d_pred_pred.sigma,
                                               fres  |-> [d_pred_pred.fres EXCEPT ![w] = BOT]]
                                       /\ d_pred_pred.fres[w] = ACK
          OBVIOUS
        <4>2. PICK d_pred \in M : /\ d_pred.sigma = [d_pred_pred.sigma EXCEPT ![i[p]] = A[i[p]]]
                                  /\ d_pred.fres  = [d_pred_pred.fres  EXCEPT ![p] = ACK]
          BY Zenon, <4>1
        <4>3. /\ d_pred.sigma = [d_pred_pred.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
              /\ d_pred.fres  = [d_pred_pred.fres  EXCEPT ![p] = ACK]
          BY <4>2
        <4>4. d_pred.fres[w] = ACK
          BY <4>1, <4>2
        <4>5. PICK d \in M' : d = [sigma |-> d_pred.sigma,
                                   fres  |-> [d_pred.fres EXCEPT ![w] = BOT]]
          BY Zenon, <4>4
        <4>6. d.sigma = [c.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
          BY <4>1, <4>2, <4>5
        <4>7. w # p
          OBVIOUS
        <4>8. d.fres = [c.fres EXCEPT ![p] = ACK]
          BY SMTT(10), <4>1, <4>2, <4>5, <4>7
        <4> QED
          BY Zenon, <4>5, <4>6, <4>8
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3>10. CASE S4(S)
        <4> USE <3>10 DEF S4
        <4> SUFFICES ASSUME NEW w \in WriteSet,
                            NEW c \in M',
                            pc'[w] \in {"W2", "W3", "W4"}
                     PROVE  (\E d \in M' : /\ d.sigma = [c.sigma EXCEPT ![i'[w]] = A'[i'[w]]]
                                           /\ d.fres = [c.fres EXCEPT ![w] = ACK])
          BY Zenon DEF Inv_W2
        <4>1. PICK d_pred \in M : c = [sigma |-> A,
                                       fres  |-> Merge([q \in WriteSet |-> IF pc[q] \in {"W2", "W3", "W4"} THEN ACK ELSE BOT],
                                                       Map(S, d_pred.sigma))]
          OBVIOUS
        <4>2. c.sigma[i'[w]] = A'[i'[w]]
          BY <4>1
        <4>3. c.fres[w] = ACK
          BY <4>1 DEF Merge
        <4>4. c.sigma = [c.sigma EXCEPT ![i'[w]] = A'[i'[w]]]
          BY <4>1, <4>2, <4>3 DEF CDomain, CFTypeOK, Map
        <4>5. c.fres = [c.fres EXCEPT ![w] = ACK]
          BY Zenon, <2>1, <4>3 DEF CDomain
        <4> QED
          BY Zenon, <4>4, <4>5
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        <4> USE <3>12 DEF S6
        <4> SUFFICES ASSUME NEW p \in WriteSet,
                            NEW c \in M',
                            pc'[p] \in {"W2", "W3", "W4"}
                     PROVE  (\E d \in M' : /\ d.sigma = [c.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
                                           /\ d.fres = [c.fres EXCEPT ![p] = ACK])
          BY Zenon DEF Inv_W2
        <4>1. PICK d_pred_pred \in M : /\ c = [sigma |-> d_pred_pred.sigma,
                                               fres  |-> [d_pred_pred.fres EXCEPT ![S] = BOT]]
                                       /\ d_pred_pred.fres[S] = a
          OBVIOUS
        <4>2. PICK d_pred \in M : /\ d_pred.sigma = [d_pred_pred.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
                                  /\ d_pred.fres  = [d_pred_pred.fres  EXCEPT ![p] = ACK]
          OBVIOUS
        <4>3. d_pred.fres[S] = a
          BY <4>1, <4>2
        <4>4. d_pred \in {e \in M : e.fres[S] = a}
          BY <4>3
        <4>5. PICK d \in M' : d = [sigma |-> d_pred.sigma,
                                   fres  |-> [d_pred.fres EXCEPT ![S] = BOT]]
          BY Zenon, <4>4
        <4>6. d.sigma = [c.sigma EXCEPT ![i'[p]] = A'[i'[p]]]
          BY <4>1, <4>2, <4>5
        <4>7. /\ d.fres = [[d_pred_pred.fres EXCEPT ![p] = ACK] EXCEPT ![S] = BOT]
              /\ c.fres = [d_pred_pred.fres EXCEPT ![S] = BOT]
          BY <4>1, <4>2, <4>5
        <4>8. /\ c.fres[S] = d.fres[S]
              /\ \A q \in WriteSet : q # p => c.fres[q] = d.fres[q]
              /\ d.fres[p] = ACK
          BY <4>7 DEF CDomain
        <4>9. /\ c.fres \in [WriteSet \union {S} -> [IndexSet -> Nat] \union {ACK, BOT}]
              /\ d.fres \in [WriteSet \union {S} -> [IndexSet -> Nat] \union {ACK, BOT}]
          BY <2>1, Zenon DEF CDomain
        <4> HIDE DEF TypeOK
        <4>10. d.fres = [c.fres EXCEPT ![p] = ACK]
          BY <4>8, <4>9
        <4> QED
          BY Zenon, <4>5, <4>6, <4>10
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>6. Inv_W4'
      <3> USE DEF Inv_W4
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_W4'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_W4'
        BY <3>2 DEF W1, CDomain
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_W4'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_W4'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_W4'
        BY <3>5 DEF W4, Inv_W1
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3> HIDE DEF TypeOK
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3> USE DEF TypeOK
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>7. Inv_S1'
      <3> USE DEF Inv_S1
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_S1'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_S1'
        BY <3>2 DEF W1
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_S1'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_S1'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_S1'
        BY <3>5 DEF W4
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY Zenon, <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>8. Inv_S2'
      <3> USE DEF Inv_S2
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_S2'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_S2'
        BY <3>2 DEF W1
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_S2'
        BY <3>3 DEF W2, Inv_S1
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_S2'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_S2'
        BY <3>5 DEF W4
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        <4> USE <3>8 DEF S2
        <4>1. CASE j < K
          BY <4>1
        <4>2. CASE j = K
          <5> USE <4>2
          <5>1. \A k \in IndexSet : (pc'[S] = "S4" \/ k < j') = FALSE
            BY DEF IndexSet
          <5> QED
            BY <5>1
        <4> QED
          BY <4>1, <4>2
      <3>9. CASE S3(S)
        <4> USE <3>9 DEF S3
        <4> SUFFICES ASSUME NEW k \in IndexSet',
                            (/\ B[k] = BOT
                             /\ (pc[S] = "S4" \/ (pc[S] = "S3" /\ k < j))
                             /\ (\A w \in WriteSet : i[w] = k => pc[w] \in {"L0", "W1", "W4"}))'
                     PROVE  (A[k] = a[k])'
          BY DEF Inv_S2
        <4>1. CASE k < j
          <5> USE <4>1
          <5>1. a'[k] = a[k]
            BY DEF TypeOK
          <5> QED
            BY <5>1
        <4>2. CASE k = j
          <5> USE <4>2
          <5>1. j < K
            BY DEF IndexSet
          <5>2. a'[k] = A[k]
            BY <5>1
          <5> QED
            BY <5>2
        <4> QED
          BY <4>1, <4>2 DEF TypeOK, IndexSet
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>9. Inv_S3'
      <3> USE DEF Inv_S3
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_S3'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_S3'
        BY <3>2 DEF W1
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_S3'
        BY <3>3 DEF W2, Inv_S1
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_S3'
        BY <3>4 DEF W3, Inv_W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_S3'
        BY <3>5 DEF W4
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        <4> USE <3>7 DEF S1
        <4>1. \A k \in IndexSet : pc'[S] = "S2" /\ ((k < j') = FALSE)
          BY DEF IndexSet
        <4> QED
          BY <4>1
      <3>8. CASE S2(S)
        <4> USE <3>8 DEF S2
        <4> SUFFICES ASSUME NEW k \in IndexSet',
                            (/\ B[k] # BOT
                             /\ (pc[S] = "S4" \/ pc[S] = "S3" \/ (pc[S] = "S2" /\ k < j))
                             /\ (\A w \in WriteSet : i[w] = k => pc[w] \in {"L0", "W1", "W4"}))'
                     PROVE  (A[k] = B[k])'
          BY DEF Inv_S3
        <4>1. CASE k < j
          <5> USE <4>1
          <5>1. B'[k] = B[k]
            OBVIOUS
          <5> QED
            BY <5>1
        <4>2. CASE k = j
          <5> USE <4>2
          <5>1. j < K
            BY DEF IndexSet
          <5>2. B'[k] = BOT
            BY <5>1
          <5> QED
            BY <5>2
        <4> QED
          BY <4>1, <4>2 DEF IndexSet
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>10. Inv_M1'
      <3> USE DEF Inv_M1
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_M1'
        <4> USE <3>1 DEF L0
        <4>1. pc[S] = pc'[S]
          OBVIOUS
        <4>2. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY <4>1 DEF KthReturnSet
        <4>3. ScanReturnSet = ScanReturnSet'
          BY <4>2 DEF ScanReturnSet
        <4> QED
          BY <4>3
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_M1'
        <4> SUFFICES ASSUME NEW beta \in ScanReturnSet',
                            pc'[S] \in {"L0", "S1", "S2", "S3", "S4"}
                     PROVE  \E c \in M' : c.sigma = beta
          BY DEF Inv_M1
        <4> USE <3>2 DEF W1
        <4>1. CASE beta[i[w]] = A[i[w]]'
          <5> USE <4>1
          <5>1. PICK alpha \in ScanReturnSet : \A k \in IndexSet : (k # i[w] => alpha[k] = beta[k])
            <6>1. \A k \in IndexSet : k # i[w] => KthReturnSet(k) = KthReturnSet(k)'
              BY DEF KthReturnSet
            <6>2. PICK z \in KthReturnSet(i[w]) : z \in Nat
              BY DEF KthReturnSet 
            <6>3. DEFINE alpha == [k \in IndexSet |-> IF k # i[w] THEN beta[k] ELSE z]
            <6>4. \A k \in IndexSet : (k # i[w] => beta[k] \in KthReturnSet(k))
              BY <6>1 DEF ScanReturnSet
            <6>5. \A k \in IndexSet : (k # i[w] => alpha[k] \in KthReturnSet(k))
              BY <6>4
            <6>6. alpha[i[w]] \in KthReturnSet(i[w])
              BY <6>2
            <6>7. alpha \in ScanReturnSet
              BY <6>5, <6>6 DEF ScanReturnSet
            <6> QED
              BY <6>7
          <5>2. PICK d \in M : d.sigma = alpha
            BY <5>1
          <5>3. PICK c \in M' : c = [sigma |-> [d.sigma EXCEPT ![i[w]] = v[w]],
                                     fres  |-> [d.fres  EXCEPT ![w] = ACK]]
            BY Zenon, <5>2
          <5>4. c.sigma = beta
            <6>1. \A k \in IndexSet : c.sigma[k] = beta[k]
              <7>1. \A k \in IndexSet : (k # i[w]) => c.sigma[k] = beta[k]
                BY <5>1, <5>2, <5>3
              <7>2. beta[i[w]] = v[w]
                OBVIOUS
              <7>3. c.sigma[i[w]] = v[w]
                BY <5>3 DEF CDomain
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>2. beta \in [IndexSet -> Nat]
              <7>1. \A k \in IndexSet : KthReturnSet(k)' \in SUBSET Nat
                BY DEF KthReturnSet
              <7> QED
                BY Zenon, <7>1 DEF ScanReturnSet
            <6>3. c.sigma \in [IndexSet -> Nat]
              BY <5>3 DEF CDomain
            <6> HIDE DEF TypeOK
            <6> QED
              BY <6>1, <6>2, <6>3
          <5> QED
            BY Zenon, <5>3, <5>4
        <4>2. CASE beta[i[w]] # A[i[w]]'
          <5> USE <4>2
          <5>1. \A k \in IndexSet : k # i[w] => KthReturnSet(k) = KthReturnSet(k)'
            BY DEF KthReturnSet
          <5>2. beta[i[w]] \in KthReturnSet(i[w])'
            BY DEF ScanReturnSet
          <5>3. beta[i[w]] \in KthReturnSet(i[w])
            BY <5>2 DEF KthReturnSet
          <5>4. beta \in ScanReturnSet
            BY <5>1, <5>3 DEF ScanReturnSet
          <5> QED
            BY <5>4
        <4> QED
          BY <4>1, <4>2
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_M1'
        <4> USE <3>3 DEF W2
        <4>1. pc[S] = pc'[S]
          OBVIOUS
        <4>2. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY <4>1 DEF KthReturnSet
        <4>3. ScanReturnSet = ScanReturnSet'
          BY <4>2 DEF ScanReturnSet
        <4> QED
          BY <4>3
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_M1'
        <4> SUFFICES ASSUME NEW alpha \in ScanReturnSet',
                            pc'[S] \in {"L0", "S1", "S2", "S3", "S4"}
                     PROVE  \E c \in M' : c.sigma = alpha
          BY DEF Inv_M1
        <4> USE <3>4 DEF W3
        <4>1. \A k \in IndexSet : k # i[w] => KthReturnSet(k) = KthReturnSet(k)'
          BY DEF KthReturnSet
        <4>2. \A k \in IndexSet : (k # i[w] => alpha[k] \in KthReturnSet(k))
          BY <4>1 DEF ScanReturnSet
        <4>3. B'[i[w]] = A'[i[w]] /\ B'[i[w]] # BOT
          BY DEF Inv_W3
        <4>4. KthReturnSet(i[w])' \in SUBSET KthReturnSet(i[w])
          BY <4>3 DEF KthReturnSet
        <4>5. alpha[i[w]] \in KthReturnSet(i[w])
          BY <4>4 DEF ScanReturnSet, IndexSet
        <4>6. alpha \in ScanReturnSet
          BY <4>2, <4>5 DEF ScanReturnSet
        <4> QED
          BY <4>6
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_M1'
        <4> SUFFICES ASSUME NEW alpha \in ScanReturnSet',
                            pc'[S] \in {"L0", "S1", "S2", "S3", "S4"}
                     PROVE  \E c \in M' : c.sigma = alpha
          BY DEF Inv_M1
        <4> USE <3>5 DEF W4
        <4>1. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY DEF KthReturnSet
        <4>2. ScanReturnSet = ScanReturnSet'
          BY <4>1 DEF ScanReturnSet
        <4>3. PICK d_pred \in M : d_pred.sigma = alpha
          BY <4>2
        <4>4. PICK d \in M : /\ d.sigma = [d_pred.sigma EXCEPT ![i[w]] = A[i[w]]]
                             /\ d.fres  = [d_pred.fres  EXCEPT ![w] = ACK]
          BY DEF Inv_W2
        <4>5. d_pred.sigma[i[w]] = A[i[w]]
          <5>1. alpha[i[w]] \in KthReturnSet(i[w])
            BY <4>1 DEF ScanReturnSet
          <5>2. CASE /\ B[i[w]] = BOT
                     /\ \/ pc[S] = "S4"
                        \/ /\ pc[S] = "S3"
                           /\ i[w] < j
            <6> USE <5>2
            <6>1. alpha[i[w]] \in {A[i[w]], a[i[w]]}
              BY <5>1 DEF KthReturnSet
            <6>2. A[i[w]] = a[i[w]]
              BY DEF Inv_S2
            <6> QED
              BY <4>3, <6>1, <6>2
          <5>3. CASE /\ B[i[w]] # BOT
                     /\ \/ pc[S] \in {"S3", "S4"}
                        \/ /\ pc[S] = "S2"
                           /\ i[w] < j
            <6> USE <5>3
            <6>1. alpha[i[w]] \in {A[i[w]], B[i[w]]}
              BY <5>1 DEF KthReturnSet
            <6>2. A[i[w]] = B[i[w]]
              BY DEF Inv_S3
            <6> QED
              BY <4>3, <6>1, <6>2
          <5>4. CASE \/ pc[S] = "L0"
                     \/ pc[S] = "S1"
                     \/ (pc[S] = "S2" /\ (B[i[w]] = BOT \/ i[w] >= j))
                     \/ (pc[S] = "S3" /\  B[i[w]] = BOT /\ i[w] >= j) 
            <6> USE <5>4
            <6>1. alpha[i[w]] \in {A[i[w]]}
              BY <5>1 DEF KthReturnSet, IndexSet
            <6> QED
              BY <4>3, <6>1
          <5> QED
            BY <5>2, <5>3, <5>4 DEF IndexSet
        <4>6. d_pred.sigma = d.sigma
          BY <4>4, <4>5 DEF CDomain
        <4>7. d.fres[w] = ACK
          BY <4>3, <4>4 DEF CDomain
        <4>8. PICK c \in M' : c = [sigma |-> d.sigma,
                                   fres  |-> [d.fres EXCEPT ![w] = BOT]]
          BY Zenon, <4>4, <4>7
        <4> QED
          BY Zenon, <4>3, <4>6, <4>8
      <3>6. CASE L0(S)
        <4> SUFFICES ASSUME NEW alpha \in ScanReturnSet'
                     PROVE  \E c \in M' : c.sigma = alpha
          BY <3>6 DEF Inv_M1, L0
        <4> USE <3>6 DEF L0
        <4>1. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY DEF IndexSet, KthReturnSet
        <4>2. ScanReturnSet = ScanReturnSet'
          BY <4>1 DEF ScanReturnSet
        <4>3. \A k \in IndexSet : KthReturnSet(k) = {A[k]}
          BY DEF KthReturnSet
        <4>4. \A k \in IndexSet : \A z \in KthReturnSet(k) : z = A[k]
          BY <4>3
        <4>5. \A k \in IndexSet : alpha[k] = A[k]
          BY Zenon, <4>2, <4>4 DEF ScanReturnSet
        <4>6. alpha = A
          BY <4>2, <4>5 DEF ScanReturnSet
        <4>7. A \in ScanReturnSet
          BY <4>3 DEF ScanReturnSet
        <4>8. PICK c \in M : c.sigma = alpha
          BY <4>6, <4>7
        <4> QED
          BY <4>8
      <3>7. CASE S1(S)
        <4> USE <3>7 DEF S1
        <4>1. \A k \in IndexSet : k >= j'
          BY DEF IndexSet
        <4>2. \A k \in IndexSet : KthReturnSet(k)' = {A[k]}
          BY <4>1 DEF IndexSet, KthReturnSet
        <4>3. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY <4>2 DEF IndexSet, KthReturnSet
        <4>4. ScanReturnSet = ScanReturnSet'
          BY <4>3 DEF ScanReturnSet
        <4> QED
          BY <4>4
      <3>8. CASE S2(S)
        <4> USE <3>8 DEF S2
        <4>1. CASE j < K
          <5> USE <4>1
          <5>1. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
            <6> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  KthReturnSet(k) = KthReturnSet(k)'
              OBVIOUS
            <6>1. A'[k] = A[k]
              OBVIOUS
            <6>2. B' = [B EXCEPT ![j] = BOT]
              OBVIOUS
            <6>3. CASE k # j
              <7> USE <6>3
              <7>1. B'[k] = B[k]
                BY <6>2
              <7>2. (k < j) = (k < j')
                BY DEF IndexSet
              <7> QED
                BY <7>1, <7>2, <6>1 DEF KthReturnSet
            <6>4. CASE k = j
              <7> USE <6>4
              <7>1. B'[k] = BOT
                BY <6>2 
              <7>2. KthReturnSet(k)' = {A[k]}
                BY <6>1, <7>1 DEF KthReturnSet
              <7>3. KthReturnSet(k) = {A[k]}
                BY DEF KthReturnSet
              <7> QED
                BY <7>2, <7>3
            <6> QED
              BY <6>3, <6>4
          <5>2. ScanReturnSet = ScanReturnSet'
            BY <5>1 DEF ScanReturnSet
          <5> QED
            BY <5>2
        <4>2. CASE j = K
          <5> USE <4>2 DEF IndexSet
          <5>1. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
            <6> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  KthReturnSet(k) = KthReturnSet(k)'
              OBVIOUS
            <6>1. KthReturnSet(k) = CASE (B[k] # BOT) -> {A[k], B[k]}
                                      [] OTHER        -> {A[k]}
              BY DEF KthReturnSet
            <6>3. KthReturnSet(k)' = CASE (B'[k] #BOT) -> {A'[k], B'[k]}
                                       [] OTHER        -> {A'[k]}
              BY DEF KthReturnSet
            <6>5. B = B'
              OBVIOUS
            <6>6. KthReturnSet(k) = KthReturnSet(k)'
              BY <6>1, <6>3, <6>5
            <6> QED
              BY <6>6
          <5>2. ScanReturnSet = ScanReturnSet'
            BY <5>1 DEF ScanReturnSet
          <5> QED
            BY <5>2
        <4> QED
          BY <4>1, <4>2
      <3>9. CASE S3(S)  
        <4> USE <3>9 DEF S3
        <4>1. CASE j < K
          <5> USE <4>1
          <5>1. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
            <6> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  KthReturnSet(k) = KthReturnSet(k)'
              OBVIOUS
            <6>1. A'[k] = A[k]
              OBVIOUS
            <6>2. a' = [a EXCEPT ![j] = A[j]]
              OBVIOUS
            <6>3. CASE k # j
              <7> USE <6>3
              <7>1. (k < j) = (k < j')
                BY DEF IndexSet
              <7>2. a'[k] = a[k]
                BY <6>2
              <7> QED
                BY <6>1, <7>1, <7>2 DEF KthReturnSet
            <6>4. CASE k = j
              <7> USE <6>4
              <7>1. CASE B[k] = BOT
                <8> USE <7>1
                <8>1. a'[k] = A[k]
                  BY <6>2
                <8>2. KthReturnSet(k)' = {A'[k]}
                  BY <8>1 DEF KthReturnSet
                <8>3. KthReturnSet(k) = {A[k]}
                  BY DEF KthReturnSet
                <8> QED
                  BY Zenon, <6>1, <8>2, <8>3 DEF KthReturnSet
              <7>2. CASE B[k] # BOT
                BY <7>2 DEF KthReturnSet
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <6>3, <6>4
          <5>2. ScanReturnSet = ScanReturnSet'
            BY <5>1 DEF ScanReturnSet
          <5> QED
            BY <5>2
        <4>2. CASE j = K
          <5> USE <4>2 DEF IndexSet
          <5>1. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
            <6> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  KthReturnSet(k) = KthReturnSet(k)'
              OBVIOUS
            <6>1. KthReturnSet(k) = CASE (B[k] # BOT) -> {A[k], B[k]}
                                      [] OTHER        -> {A[k], a[k]}
              BY DEF KthReturnSet
            <6>2. KthReturnSet(k)' = CASE (B'[k] # BOT) -> {A'[k], B'[k]}
                                       [] OTHER         -> {A'[k], a'[k]}
              BY DEF KthReturnSet
            <6>3. a = a'
              OBVIOUS
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ScanReturnSet = ScanReturnSet'
            BY <5>1 DEF ScanReturnSet
          <5> QED
            BY <5>2
        <4> QED
          BY <4>1, <4>2
      <3>10. CASE S4(S)
        BY <3>10 DEF S4
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        <4> SUFFICES ASSUME NEW alpha \in ScanReturnSet',
                            pc'[S] \in {"L0", "S1", "S2", "S3", "S4"}
                     PROVE  \E c \in M' : c.sigma = alpha
          BY DEF Inv_M1
        <4> USE <3>12 DEF S6
        <4>1. \A k \in IndexSet : KthReturnSet(k) = {a[k]}
          BY DEF KthReturnSet
        <4>2. a \in ScanReturnSet
          BY <4>1 DEF ScanReturnSet
        <4>3. PICK d \in M : /\ d.sigma = A
                             /\ d.fres[S] = a
          BY <4>2 DEF Inv_M2
        <4>4. d \in {e \in M : e.fres[S] = a}
          BY <4>3
        <4>5. PICK c \in M' : c = [sigma |-> d.sigma, 
                                   fres  |-> [d.fres EXCEPT ![S] = BOT]]
          BY Zenon, <4>3, <4>4
        <4>6. c.sigma = A'
          BY <4>3, <4>5
        <4>7. c.fres[S] = BOT
          BY <4>5 DEF CDomain
        <4>8. \A k \in IndexSet : KthReturnSet(k)' = {A'[k]}
          BY DEF KthReturnSet
        <4>9. \A k \in IndexSet : \A z \in KthReturnSet(k)' : z = A'[k]
          BY <4>8
        <4>10. \A k \in IndexSet : alpha[k] = A'[k]
          BY <4>9 DEF ScanReturnSet
        <4>11. alpha = A'
          BY <4>10 DEF ScanReturnSet
        <4> QED
          BY Zenon, <4>5, <4>6, <4>7, <4>11
      <3>13. CASE UNCHANGED vars
        <4>1. ScanReturnSet = ScanReturnSet'
          BY <3>13 DEF vars, ScanReturnSet, KthReturnSet
        <4> QED
          BY <3>13, <4>1 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>11. Inv_M2'
      <3> USE DEF Inv_M2
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Inv_M2'
        <4> USE <3>1 DEF L0
        <4>1. pc[S] = pc'[S]
          OBVIOUS
        <4>2. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY <4>1 DEF KthReturnSet
        <4>3. ScanReturnSet = ScanReturnSet'
          BY <4>2 DEF ScanReturnSet
        <4> QED
          BY <4>3
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Inv_M2'
        <4> USE <3>2 DEF W1
        <4> SUFFICES ASSUME pc'[S] \in {"S5", "S6"},
                            NEW alpha \in ScanReturnSet'
                     PROVE  \E c \in M' : /\ c.sigma = A'
                                          /\ c.fres[S] = alpha
          OBVIOUS
        <4>1. \A k \in IndexSet : k # i[w] => KthReturnSet(k) = KthReturnSet(k)'
          BY DEF KthReturnSet
        <4>2. KthReturnSet(i[w]) = KthReturnSet(i[w])'
          BY DEF KthReturnSet
        <4>3. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY <4>1, <4>2
        <4>4. ScanReturnSet = ScanReturnSet'
          BY <4>3 DEF ScanReturnSet
        <4>5. PICK d \in M : /\ d.sigma = A
                             /\ d.fres[S] = alpha
          BY <4>4
        <4>6. PICK c \in M' : c = [sigma |-> [d.sigma EXCEPT ![i[w]] = v[w]],
                                   fres  |-> [d.fres  EXCEPT ![w]    = ACK]]
          OBVIOUS
        <4>7. /\ c.sigma = A'
              /\ c.fres[S] = alpha
          BY <4>5, <4>6
        <4> QED
          BY <4>6, <4>7
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Inv_M2'
        <4> USE <3>3 DEF W2
        <4>1. pc[S] = pc'[S]
          OBVIOUS
        <4>2. \A k \in IndexSet : KthReturnSet(k) = KthReturnSet(k)'
          BY <4>1 DEF KthReturnSet
        <4>3. ScanReturnSet = ScanReturnSet'
          BY <4>2 DEF ScanReturnSet
        <4> QED
          BY <4>3
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Inv_M2'
        <4> SUFFICES ASSUME NEW alpha \in ScanReturnSet',
                            pc'[S] \in {"S5", "S6"}
                     PROVE  \E c \in M' : /\ c.sigma = A'
                                          /\ c.fres[S] = alpha
          BY DEF Inv_M2
        <4> USE <3>4 DEF W3
        <4>1. \A k \in IndexSet : k # i[w] => KthReturnSet(k) = KthReturnSet(k)'
          BY DEF KthReturnSet
        <4>2. B'[i[w]] = A'[i[w]] /\ B'[i[w]] # BOT
          BY DEF Inv_W3
        <4>3. KthReturnSet(i[w])' \in SUBSET KthReturnSet(i[w])
          BY <4>2 DEF KthReturnSet
        <4>4. alpha[i[w]] \in KthReturnSet(i[w])
          BY <4>3 DEF ScanReturnSet, IndexSet
        <4>6. alpha \in ScanReturnSet
          BY <4>1, <4>4 DEF ScanReturnSet
        <4> QED
          BY <4>6
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Inv_M2'
        <4> USE <3>5 DEF W4
        <4> SUFFICES ASSUME pc'[S] \in {"S5", "S6"},
                            NEW alpha \in ScanReturnSet'
                     PROVE  \E c \in M' : /\ c.sigma = A
                                          /\ c.fres[S] = alpha
            OBVIOUS
        <4>1. \A k \in IndexSet : KthReturnSet(k)' = KthReturnSet(k)
          BY DEF KthReturnSet
        <4>2. ScanReturnSet = ScanReturnSet'
          BY <4>1 DEF ScanReturnSet
        <4>3. PICK d_pred \in M : /\ d_pred.sigma = A
                                  /\ d_pred.fres[S] = alpha
          BY <4>2
        <4>5. PICK d \in M : /\ d.sigma = [d_pred.sigma EXCEPT ![i[w]] = A[i[w]]]
                             /\ d.fres = [d_pred.fres EXCEPT ![w] = ACK]
          BY DEF Inv_W2
        <4>6. /\ d.fres[w] = ACK
              /\ d.sigma = A
              /\ d.fres[S] = alpha
          BY <4>3, <4>5 DEF CDomain
        <4>7. PICK c \in M' : c = [sigma |-> d.sigma,
                                   fres  |-> [d.fres EXCEPT ![w] = BOT]]
          BY Zenon, <4>5, <4>6
        <4>8. /\ c.sigma = A
              /\ c.fres[S] = alpha
          BY <4>6, <4>7
        <4> QED
          BY <4>7, <4>8
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3>10. CASE S4(S)
        <4> SUFFICES ASSUME NEW alpha \in ScanReturnSet',
                            pc'[S] \in {"S5", "S6"}
                     PROVE  \E c \in M' : /\ c.sigma = A'
                                          /\ c.fres[S] = alpha
          BY DEF Inv_M2
        <4> USE <3>10 DEF S4
        <4>1. \A k \in IndexSet : KthReturnSet(k)' \in SUBSET KthReturnSet(k)
          BY DEF KthReturnSet, IndexSet
        <4>2. ScanReturnSet' \in SUBSET ScanReturnSet
          BY <4>1 DEF ScanReturnSet
        <4>3. PICK d \in M : /\ d.sigma = alpha
                             /\ d.fres[S] = BOT
          BY <4>2 DEF Inv_M1, CDomain, CFTypeOK
        <4>4. PICK c \in M' : c = [sigma |-> A,
                                   fres  |-> Merge([w \in WriteSet |-> IF pc[w] \in {"W2", "W3", "W4"} THEN ACK ELSE BOT],
                                                   Map(S, d.sigma))]
          BY Zenon, <4>3
        <4>5. /\ c.sigma = A
              /\ c.fres[S] = alpha
          BY <4>3, <4>4 DEF Merge, Map
        <4> QED
          BY <4>5
      <3>11. CASE S5(S)
        <4> USE <3>11 DEF S5
        <4>1. CASE j < K
          <5> USE <4>1
          <5>1. \A k \in IndexSet : k # j => KthReturnSet(k) = KthReturnSet(k)'
            <6> SUFFICES ASSUME NEW k \in IndexSet,
                                k # j
                          PROVE  KthReturnSet(k) = KthReturnSet(k)'
              OBVIOUS
            <6>1. (k >= j) = (k >= j')
              BY DEF IndexSet
            <6>2. a'[k] = a[k]
              OBVIOUS
            <6> QED
              BY <6>1, <6>2 DEF KthReturnSet
          <5>2. \A k \in IndexSet : k = j => KthReturnSet(k)' \in SUBSET KthReturnSet(k)
            <6> SUFFICES ASSUME NEW k \in IndexSet,
                                k = j
                          PROVE  KthReturnSet(k)' \in SUBSET KthReturnSet(k)
              OBVIOUS
            <6>1. CASE B[k] # BOT
              <7> USE <6>1
              <7>1. a'[k] = B[k]
                BY DEF IndexSet
              <7>2. {B[k]} \in SUBSET KthReturnSet(k)
                BY DEF KthReturnSet
              <7>3. KthReturnSet(k)' = {a'[k]}
                BY DEF KthReturnSet, IndexSet
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>2. CASE B[j] = BOT
              <7> USE <6>2
              <7>1. a'[k] = a[k]
                BY DEF IndexSet
              <7>2. {a[k]} \in SUBSET KthReturnSet(k)
                BY DEF KthReturnSet
              <7>3. KthReturnSet(k)' = {a'[k]}
                BY DEF KthReturnSet, IndexSet
              <7> QED
                BY <7>1, <7>2, <7>3
            <6> QED
              BY <6>1, <6>2
          <5>3. ScanReturnSet' \in SUBSET ScanReturnSet
            BY <5>1, <5>2 DEF ScanReturnSet
          <5> QED
            BY <5>3
        <4>2. CASE j = K
          <5> USE <4>2
          <5>1 \A k \in IndexSet : k < j
            BY DEF IndexSet
          <5>2. \A k \in IndexSet : KthReturnSet(k) = {a[k]}
            BY <5>1 DEF KthReturnSet, IndexSet
          <5>3. \A k \in IndexSet : KthReturnSet(k)' = {a[k]}
            BY DEF KthReturnSet
          <5>4. ScanReturnSet = ScanReturnSet'
            BY <5>2, <5>3 DEF ScanReturnSet
          <5> QED
            BY <5>4
        <4> QED
          BY <4>1, <4>2
      <3>12. CASE S6(S)
        BY <3>12 DEF S6
      <3>13. CASE UNCHANGED vars
        <4>1. ScanReturnSet = ScanReturnSet'
          BY <3>13 DEF vars, ScanReturnSet, KthReturnSet
        <4> QED
          BY <3>13, <4>1 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>12. Linearizable'
      <3> USE DEF Linearizable
      <3>1. ASSUME NEW w \in WriteSet,
                   L0(w)
            PROVE  Linearizable'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW w \in WriteSet,
                   W1(w)
            PROVE  Linearizable'
        BY <3>2 DEF W1
      <3>3. ASSUME NEW w \in WriteSet,
                   W2(w)
            PROVE  Linearizable'
        BY <3>3 DEF W2
      <3>4. ASSUME NEW w \in WriteSet,
                   W3(w)
            PROVE  Linearizable'
        BY <3>4 DEF W3
      <3>5. ASSUME NEW w \in WriteSet,
                   W4(w)
            PROVE  Linearizable'
        <4> USE <3>5 DEF W4
        <4>1. PICK d_pred \in M : TRUE
          OBVIOUS
        <4>2. PICK d \in M : /\ d.sigma = [d_pred.sigma EXCEPT ![i[w]] = A[i[w]]]
                             /\ d.fres  = [d_pred.fres  EXCEPT ![w] = ACK]
          BY <4>1 DEF Inv_W2
        <4>3. d.fres[w] = ACK
          BY <4>2 DEF CDomain
        <4>4. PICK c \in M' : c = [sigma |-> d.sigma,
                                   fres  |-> [d.fres EXCEPT ![w] = BOT]]
          BY Zenon, <4>2, <4>3
        <4> QED
          BY Zenon, <4>1, <4>4
      <3>6. CASE L0(S)
        BY <3>6 DEF L0
      <3>7. CASE S1(S)
        BY <3>7 DEF S1
      <3>8. CASE S2(S)
        BY <3>8 DEF S2
      <3>9. CASE S3(S)  
        BY <3>9 DEF S3
      <3> HIDE DEF TypeOK
      <3>10. CASE S4(S)
        BY Zenon, <3>10 DEF S4
      <3> USE DEF TypeOK
      <3>11. CASE S5(S)
        BY <3>11 DEF S5
      <3>12. CASE S6(S)
        <4> USE <3>12 DEF S6
        <4>1. \A k \in IndexSet : KthReturnSet(k) = {a[k]}
          BY DEF KthReturnSet
        <4>2. PICK alpha \in ScanReturnSet : alpha = a
          BY <4>1 DEF ScanReturnSet
        <4>3. PICK d \in M : d.fres[S] = a
          BY <4>2 DEF Inv_M2
        <4>4. d \in {e \in M : e.fres[S] = a}
          BY <4>3
        <4>5. PICK c \in M' : c = [sigma |-> d.sigma, 
                                   fres  |-> [d.fres EXCEPT ![S] = BOT]]
          BY Zenon, <4>3, <4>4
        <4> QED
          BY Zenon, <4>5
      <3>13. CASE UNCHANGED vars
        BY <3>13 DEF vars
      <3> QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>5, <2>4, <2>6, <2>7, <2>8, <2>9 DEF Inv
  <1> QED 
    BY <1>1, <1>2

=============================================================================
\* Modification History
\* Last modified Tue Oct 03 23:46:07 EDT 2023 by uguryavuz
\* Created Thu Sep 28 22:04:57 EDT 2023 by uguryavuz
