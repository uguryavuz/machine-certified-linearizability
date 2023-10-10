---------------------- MODULE POPL24_HerlihyWingQueue ----------------------
(****************************************************************************
Authors: Prasad Jayanti, Siddhartha Jayanti, Uğur Y. Yavuz, Lizzie Hernández Videa
Date: 2023-10-02

This is the TLA+ specification of the Herlihy-Wing queue, as described in
[Herlihy & Wing, 1990] (on page 475 in the publication) and its proof 
of linearizability in TLAPS, using the tracking technique as described in our work 
"A Universal, Sound, and Complete Forward Reasoning Technique for Machine-Verified 
Proofs of Linearizability", to appear in POPL 2024. Specficially, it corresponds to 
the partial tracker as described in the paper and its Appendix.

[Herlihy & Wing, 1990] 
Maurice P. Herlihy and Jeannette M. Wing. 1990. 
"Linearizability: a correctness condition for concurrent objects." 
ACM Trans. Program. Lang. Syst. 12, 3 (July 1990), 463–492. https://doi.org/10.1145/78969.78972

This file relies on lemmas proven in the file POPL24_HerlihyWingQueuePrelude.tla.

FILE OUTLINE:
    - Lines 69-130: Preliminary definitions and lemmas
    - Lines 130-286: Specification
    - Lines 286-376: Type-correctness and proof of type-correctness
    - Lines 376-469: Remaining invariants
    - Lines 469-568: Proof that invariants imply linearizability
    - Lines 568-2799: Proof of inductive invariance
    - Lines 2799-2801: Proof of linearizability (immediate from the two proofs above)

TYPE:
    - Enqueue(v) for adding an element v to the queue. Invokable by any process.
    - Dequeue() for removing an element from the queue. Invokable by any process.

MODEL VALUES:
    - ACK ('ack' in the paper) is a special value that is used to indicate 
      an operation has been completed.
    - BOT (\bot in the paper) is akin to a null value.
    - ProcSet is the set of all processes.

SHARED VARIABLES:
    - X is a read/fetch-and-inc register, initialized to 1.
    - Q is an infinite read/write/swap array, initialized to [BOT, BOT, ...].

LOCAL VARIABLES:
    - For each process: i_p, j_p, l_p, x_p and v_p are local

ALGORITHM:
    - Enqueue(v):
      -----------
      E1: i <- fetch-and-inc(X)
      E2: Q[i] <- v
      E3: return ACK

    - Dequeue():
      -----------
      D1: l <- X
      D2: if l = 1 
             then goto D1 
             else j <- 1
      D3: x <- swap(Q[j], BOT)
          if x = BOT 
             then if j = l - 1
                     then goto D1
                     else {j <- j + 1; goto D3}
      D4: return x
                         
NOTE: Each line has at most 1 shared memory instruction.
****************************************************************************)

EXTENDS Integers, FiniteSetTheorems, Functions, TLAPS, POPL24_HerlihyWingQueuePrelude

CONSTANTS ACK, BOT, ProcSet
VARIABLES pc, X, Q, i, j, l, x, v, M    \* M is the meta-configuration.
vars == <<pc, X, Q, i, j, l, x, v, M>>

\* Preliminary definitions and lemmas 

\* The following set of sequence-related definitions are taken from 
\* Sequences.tla in the standard modules of TLA+. Head is redefined
\* to return BOT if the sequence is empty; in the standard modules,
\* Head is undefined for empty sequences. As we override this definition,
\* we do not extend Sequences here and instead copy the remaining
\* definitions (i.e. Seqs [called Seq in Sequences], Concat, Tail).

\* Set of all sequences containing items from S.
Seqs(S) == UNION {[1..n -> S] : n \in Nat}

\* Concatenation of two sequences.
Concat(s1, s2) == [k \in 1..(Len(s1)+Len(s2)) |-> IF k \leq Len(s1) 
                                                     THEN s1[k] 
                                                     ELSE s2[k-Len(s1)]]

\* Head of a sequence, BOT if the sequence is empty.
Head(s) == IF s # << >> THEN s[1] ELSE BOT

\* Tail of a sequence.
Tail(s) == [k \in 1..(Len(s)-1) |-> s[k+1]]

PosInts == Nat \ {0}

\* Expression defined in POP24_HerlihyWingQueuePrelude:
\* Perm(S) : The set of all permutations of items of S
LEMMA PermDef == \A S : Perm(S) = {f \in [1..Cardinality(S) -> S] : 
                                        \A w \in S : \E q \in 1..Cardinality(S) : f[q] = w}
  BY DEF Perm

\* Lemmas proven in POP24_HerlihyWingQueuePrelude:

\* PermLength : The length of a permutation is the same as the cardinality of the set it permutes.
LEMMA PermLengthLem == \A S : IsFiniteSet(S) => (\A pi \in Perm(S) : Cardinality(S) = Len(pi))
  BY PermLength

\* PermDistinct : Permutation of a set has different elements at different indices.
LEMMA PermDistinctLem == \A S : IsFiniteSet(S) 
                                    => (\A pi \in Perm(S) : 
                                           \A k, m \in DOMAIN pi : k # m => pi[k] # pi[m])
  BY PermDistinct

\* MaxElement : Every set of integers has a maximum element.
LEMMA MaxElementLem == \A S : (S \in SUBSET Int /\ S # {} /\ IsFiniteSet(S)) 
                                    => \E s \in S : (\A y \in S : y <= s)
  BY Zenon, MaxElement

\* WellOrderingPrinciple : There exists an ordering f (a bijection 1..Card(S) -> S
\*                         that monotonically increases) of every finite set S of integers.
LEMMA WellOrderingPrincipleLem == \A S : (S \in SUBSET Int /\ IsFiniteSet(S)) 
                                            => \E f \in Bijection(1..Cardinality(S), S) : 
                                                   (\A m, n \in 1..Cardinality(S) : m < n => f[m] < f[n])
  BY Zenon, WellOrderingPrinciple
                    
\* SPECIFICATION
                    
\* The initial predicate.
\*   Notes:
\*   - The meta-configuration M contains atomic configurations C = (C.sigma, C.f),
\*     where C.f is a triple (op, arg, res). In the TLA+ specification, we use
\*     (sigma, fres) = (C.sigma, C.f.res) as the atomic configuration; as op and arg
\*     are uniquely determined by pc, i, and v.
\*   * Alternatively, one can keep these fields in the meta-configuration and
\*     prove an invariant that, for a process p, the value of pc[p] imposes a 
\*     unique value for C.f.op[p], and the value of the variables passed in as 
\*     arguments, does so for C.f.arg[p], for all configurations C in M. Since
\*     this increases proof overhead, we opt for this simplification.
Init == /\ pc = [p \in ProcSet |-> "L0"]
        /\ X = 1
        /\ Q = [index \in PosInts |-> BOT]
        /\ i \in [ProcSet -> PosInts]
        /\ j \in [ProcSet -> PosInts]
        /\ l \in [ProcSet -> PosInts]
        /\ x \in [ProcSet -> PosInts \union {BOT}]
        /\ v \in [ProcSet -> PosInts]
        /\ M = {[sigma |-> << >>,
                 fres  |-> [p \in ProcSet |-> BOT]]}

\* Definitions needed to define actions on the meta-configuration M.

\* General domain for an atomic configuration c in M
\* (without accounting for type-correctness).
\*   - sigma is a sequence of positive integers, representing the queue.
\*   - fres is a function from ProcSet to positive integers, ACK or BOT for each process.
CDomain == [sigma : Seqs(PosInts), fres : [ProcSet -> (PosInts \union {ACK, BOT})]]

\* Type-correctness for f in a configuration c in M.
\*   - Specifically, this ensures the correct type of return value for each process,
\*     given their program counter.
CFTypeOK(c) == \A p \in ProcSet : /\ pc[p] \in {"L0", "E1", "D1", "D2", "D3"} => c.fres[p] = BOT
                                  /\ pc[p] \in {"E2", "E3"}                   => c.fres[p] \in {ACK, BOT}
                                  /\ pc[p] \in {"D4"}                         => c.fres[p] \in PosInts \union {BOT}

\* UnlinearizedEnqs: set of enqueuing processes w/o response (per atomic configuration c) 
\* at "E2" or "E3". This captures the definitions used in Figure 4, line 2.
UnlinearizedEnqs(c) == {q \in ProcSet : pc[q] \in {"E2", "E3"} /\ c.fres[q] = BOT}

\* Set of configuraitons after process p returns r. 
\* (Filter non-r responses, and reset the response field).
Filter(p, r) == {d \in CDomain : \E c \in M : /\ c.fres[p] = r
                                              /\ d.fres[p] = BOT
                                              /\ \A q \in ProcSet : q # p => d.fres[q] = c.fres[q]
                                              /\ d.sigma = c.sigma}

\* Line 0.
\* Notes:
\*   - Here, idle processes pick operations and corresponding arguments
\*     and invoke the operation with the argument.
L0(p) == /\ pc[p] = "L0"
         /\ \E new_line \in {"E1", "D1"} : /\ pc' = [pc EXCEPT ![p] = new_line]
                                           /\ IF new_line = "E1" 
                                                 THEN \E new_v \in PosInts : 
                                                          v' = [v EXCEPT ![p] = new_v]
                                                 ELSE v' = v
         /\ UNCHANGED <<X, Q, i, j, l, x, M>>

\* E1: i <- fetch-and-inc(X)     
E1(p) == /\ pc[p] = "E1"
         /\ pc' = [pc EXCEPT ![p] = "E2"]
         /\ i' = [i EXCEPT ![p] = X]
         /\ X' = X + 1
         /\ UNCHANGED <<Q, j, l, x, v>>
         \* Update the meta-configuration: linearize all possible subsets of unlinearized
         \* enqueue operations in every possible order, starting from every possible 
         \* initial configuration d in M.
         /\ M' = {c \in CDomain :
                    \* The prime is added to CFTypeOK and UnlinearizedEnqs to ensure that
                    \* p is included in the set of unlinearized enqueue operations.
                    \* Specifically, note that UnlinearizedEnqs(d)' = UnlinearizedEnqs(c) \union {p}.
                    /\ CFTypeOK(c)'
                    /\ \E d \in M : 
                          \E S \in SUBSET UnlinearizedEnqs(d)' : 
                             \E seq \in Perm(S) : 
                                \* DOMAIN seq is precisely 1..Card(S). The appended sequence to c.sigma
                                \* is exactly the enqueued values in the order specified by seq.
                                /\ c.sigma = Concat(d.sigma, [k \in DOMAIN seq |-> v[seq[k]]])
                                /\ \A q \in ProcSet : IF q \in S THEN c.fres[q] = ACK ELSE c.fres[q] = d.fres[q]}

\* E2: Q[i] <- v
E2(p) == /\ pc[p] = "E2"
         /\ pc' = [pc EXCEPT ![p] = "E3"]
         /\ Q' = [Q EXCEPT ![i[p]] = v[p]]
         /\ UNCHANGED <<X, i, j, l, x, v, M>>

\* E3: return ACK
E3(p) == /\ pc[p] = "E3"
         /\ pc' = [pc EXCEPT ![p] = "L0"]
         /\ UNCHANGED <<X, Q, i, j, l, x, v>>
         \* Update the meta-configuration: filter out configurations that don't match
         \* the return value of p's operation, and reset the return value to BOT.
         /\ M' = Filter(p, ACK)

\* D1: l <- X
D1(p) == /\ pc[p] = "D1"
         /\ pc' = [pc EXCEPT ![p] = "D2"]
         /\ l' = [l EXCEPT ![p] = X]
         /\ UNCHANGED <<X, Q, i, j, x, v, M>>

\* D2: if l = 1 then goto D1 else j <- 1
D2(p) == /\ pc[p] = "D2"
         /\ IF l[p] = 1 
               THEN /\ pc' = [pc EXCEPT ![p] = "D1"]
                    /\ j' = j
               ELSE /\ pc' = [pc EXCEPT ![p] = "D3"]
                    /\ j' = [j EXCEPT ![p] = 1]
         /\ UNCHANGED <<X, Q, i, l, x, v, M>>

\* D3: x <- swap(Q[j], BOT)
\*     if x = BOT then 
\*        if j = l - 1 then goto D1 
\*        else {j <- j + 1; goto D3}
D3(p) == /\ pc[p] = "D3"
         /\ x' = [x EXCEPT ![p] = Q[j[p]]]
         /\ Q' = [Q EXCEPT ![j[p]] = BOT]
         /\ IF Q[j[p]] = BOT \* This is x is the pseudocode.
               THEN IF j[p] = l[p] - 1
                       THEN /\ pc' = [pc EXCEPT ![p] = "D1"]
                            /\ UNCHANGED <<j, M>>
                       ELSE /\ j' = [j EXCEPT ![p] = j[p] + 1]
                            /\ UNCHANGED <<pc, M>>
               ELSE /\ pc' = [pc EXCEPT ![p] = "D4"]
                    /\ j' = j
                    \* Update the meta-configuration: linearize p's dequeue.
                    /\ M' = {d \in CDomain : /\ CFTypeOK(d)'
                                             /\ \E c \in M : /\ d.fres[p] = Head(c.sigma)
                                                             /\ \A q \in ProcSet : q # p => d.fres[q] = c.fres[q]
                                                             /\ d.sigma = Tail(c.sigma)}
         /\ UNCHANGED <<X, i, l, v>>

\* D4: return x
D4(p) == /\ pc[p] = "D4"
         /\ pc' = [pc EXCEPT ![p] = "L0"]
         /\ UNCHANGED <<X, Q, i, j, l, x, v>>
         \* Update the meta-configuration: filter out configurations that don't match
         \* the return value of p's operation, and reset the return value to BOT.
         /\ M' = Filter(p, x[p])

\* The next-state relation.
Next == \E p \in ProcSet : \/ L0(p)
                           \/ E1(p)
                           \/ E2(p)
                           \/ E3(p)
                           \/ D1(p)
                           \/ D2(p)
                           \/ D3(p)
                           \/ D4(p)

\* The specification.
Spec == Init /\ [][Next]_vars

\* TYPE CORRECTNESS
TypeOK == /\ pc \in [ProcSet -> {"L0", "E1", "E2", "E3", "D1", "D2", "D3", "D4"}]
          /\ X \in PosInts
          /\ Q \in [PosInts -> PosInts \union {BOT}]
          /\ i \in [ProcSet -> PosInts]
          /\ j \in [ProcSet -> PosInts]
          /\ l \in [ProcSet -> PosInts]
          /\ x \in [ProcSet -> PosInts \union {BOT}]
          /\ v \in [ProcSet -> PosInts]
          /\ M \in SUBSET {c \in CDomain : CFTypeOK(c)}

\* Proof of type-correctnesss.
LEMMA InitTypeSafety == Init => TypeOK
  <1> SUFFICES ASSUME Init
               PROVE  TypeOK
    OBVIOUS
  <1> USE DEF PosInts, Init, TypeOK
  <1>10. M \in SUBSET {c \in CDomain : CFTypeOK(c)}
    <2> DEFINE c == [sigma |-> << >>, fres |-> [p \in ProcSet |-> BOT]]
    <2>1. c.sigma \in [1..0 -> PosInts]
      OBVIOUS
    <2>2. c.sigma \in Seqs(PosInts)
      BY <2>1, Zenon DEF Seqs
    <2> QED
      BY <2>2 DEF CDomain, CFTypeOK
  <1> QED
    BY <1>10 DEF TypeOK

LEMMA NextTypeSafety == TypeOK /\ [Next]_vars => TypeOK'
  <1> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1> USE DEF TypeOK, CDomain, CFTypeOK, Seqs, PosInts
  <1>1. ASSUME NEW p \in ProcSet,
               L0(p)
        PROVE  TypeOK'
    BY <1>1 DEF L0
  <1>2. ASSUME NEW p \in ProcSet,
               E1(p)
        PROVE  TypeOK'
    BY <1>2 DEF E1
  <1>3. ASSUME NEW p \in ProcSet,
               E2(p)
        PROVE  TypeOK'
    BY <1>3 DEF E2
  <1>4. ASSUME NEW p \in ProcSet,
               E3(p)
        PROVE  TypeOK'
    BY <1>4 DEF E3, Filter
  <1>5. ASSUME NEW p \in ProcSet,
               D1(p)
        PROVE  TypeOK'
    BY <1>5 DEF D1
  <1>6. ASSUME NEW p \in ProcSet,
               D2(p)
        PROVE  TypeOK'
    BY <1>6 DEF D2
  <1>7. ASSUME NEW p \in ProcSet,
               D3(p)
        PROVE  TypeOK'
    <2> USE <1>7 DEF D3
    <2>1. (pc \in [ProcSet -> {"L0", "E1", "E2", "E3", "D1", "D2", "D3", "D4"}])'
      BY Zenon
    <2>2. (j \in [ProcSet -> PosInts])'
      OBVIOUS
    <2>3. M' \in SUBSET {c \in CDomain : CFTypeOK(c)'}
      BY Zenon
    <2>  QED
      BY Zenon, <2>1, <2>2, <2>3 DEF TypeOK
  <1>8. ASSUME NEW p \in ProcSet,
               D4(p)
        PROVE  TypeOK'
    BY <1>8 DEF D4, Filter
  <1>9. CASE UNCHANGED vars
    BY <1>9 DEF vars
  <1> QED
    BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Next

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

\* Some notes on the remaining invariants
\* 
\* - The correspondence between labels as they appear in the paper is as follows:
\*   - E1 (i <- fetch-and-inc(X)) -> 2
\*   - E2 (Q[i] <- v)             -> 3
\*   - E3 (return ACK)            -> 4
\*   - D1 (l <- X)                -> 6
\*   - D2 (if l = 1 then goto D1 else j <- 1) -> 7
\*   - D3 (x <- swap(Q[j], BOT) ...)          -> 8
\*   - D4 (return x)                          -> 9
\*
\* - By the definitions of TypeOK, CDomain, and CFTypeOK, we have that
\*   all type invariants and I_{1, 5}, I_2, I_6, I_9 and the configuration-related
\*   conjuncts of I_3, I_4, I_7, and I_8 are superceded by TypeOK.

\* The non-configuration-related conjuncts of I_3 as it appears in the paper.
Inv_E2 == \A p \in ProcSet : pc[p] = "E2" => /\ 1 <= i[p]
                                             /\ i[p] < X
                                             /\ Q[i[p]] = BOT
                                             /\ \A q \in ProcSet : (pc[q] \in {"E2", "E3"} /\ q # p) => i[q] # i[p]

\* The non-configuration-related conjuncts of I_4 as it appears in the paper.
Inv_E3 == \A p \in ProcSet : pc[p] = "E3" => /\ 1 <= i[p]
                                             /\ i[p] < X
                                             /\ \A q \in ProcSet : (pc[q] \in {"E2", "E3"} /\ q # p) => i[q] # i[p]

\* The non-configuration-related conjuncts of I_7 as it appears in the paper.
Inv_D2 == \A p \in ProcSet : pc[p] = "D2" => /\ 1 <= l[p]
                                             /\ l[p] <= X

\* The non-configuration-related conjuncts of I_8 as it appears in the paper.
Inv_D3 == \A p \in ProcSet : pc[p] = "D3" => /\ 1 <= j[p]
                                             /\ j[p] < l[p]
                                             /\ l[p] <= X

\* Q must be empty starting at and past index X. (I_a in the paper)
Inv_Q == \A k \in PosInts : k > X - 1 => Q[k] = BOT                                         

\* Predicates needed to define I_b in the paper.
\* See the appendix for a thorough explanation of the predicates and the invariant.

\* GoodEnqSet: Given a set A of indices between 1 and X-1, whether the set can
\* correspond to a set of linearized enqueue operations.
GoodEnqSet(A) == \A k \in 1..X-1 : /\ Q[k] # BOT => k \in A
                                   /\ (k \in A /\ Q[k] = BOT) => \E q \in ProcSet : (pc[q] = "E2" /\ i[q] = k)
                                                                                     
\* ValuesMatchInds: Given a sequence of indices seq and the sigma of a configuration c
\* whether sigma indeed corresponds to the order of linerizations conjectured by the
\* sequence of indices seq.
\* Note that the version in the paper takes C as an argument, but since C.f is unused
\* in the definition, we omit it here; and instead take C.sigma directly as an argument.
ValuesMatchInds(seq, sigma) == 
      sigma = [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                      [] OTHER           -> v[CHOOSE q \in ProcSet : pc[q] = "E2" /\ i[q] = seq[k]]]      

\* GoodRes: For a conjectured set of linearized enqueue indices A and the f.res of a
\* configuration c, whether the return values in f.res indeed correspond to the 
\* linearizations in conjectured by A.
\* Note that the version in the paper takes C as an argument, but since C.f is unused
\* in the definition, we omit it here; and instead take C.f.res directly as an argument.
GoodRes(A, res) == \A q \in ProcSet : res[q] = CASE (pc[q] = "E2" /\ i[q] \in A) -> ACK
                                                 [] (pc[q] = "E3")               -> ACK
                                                 [] (pc[q] = "D4")               -> x[q]
                                                 [] OTHER                        -> BOT

\* JInvSeq: Assert that all inversions in the sequence of indices seq are justified.
\* See the appendix for a discussion of inversions and justified inversions.
JInvSeq(seq) == \A m, n \in 1..Len(seq) : (n < m /\ seq[n] > seq[m] /\ Q[seq[m]] # BOT)
  => \E q \in ProcSet : /\ pc[q] = "D3"
                        /\ seq[n] < l[q]
                        /\ seq[m] < j[q]

\* I_b as it appears in the paper.
Inv_Main == \A A \in SUBSET 1..X-1 : 
                GoodEnqSet(A) => \A seq \in Perm(A) : 
                                     JInvSeq(seq) => 
                                        \E c \in M : /\ ValuesMatchInds(seq, c.sigma)
                                                     /\ GoodRes(A, c.fres)

\* The linearizability invariant (I_L) as described in the paper.
Linearizable == M # {}

\* Inductive invariant without linearizability
InvNL == /\ TypeOK
         /\ Inv_E2
         /\ Inv_E3
         /\ Inv_D2
         /\ Inv_D3
         /\ Inv_Q
         /\ Inv_Main
         
\* Proof that InvNL implies M # {} by itself.
\* This proof relies on the following extraneous definitions and theorems:
\*   - Bijection, Surjection: Defined in Functions.tla in the standard modules of TLA+.
\*   - The following finite set-related theorems from FiniteSetTheorems.tla in the standard module:
\*      * FS_Interval: a..b is a finite set for any a, b \in Nat.
\*      * FS_Subset: Any subset of a finite set is finite.
\*      * FS_CardinalityType: The cardinality of a finite set is a natural number.
\*      * FS_AddElement: The cardinality of a set increases by 1 when an element is added.
\*      * FS_PigeonHole: The pigeonhole principle.
\*   - WellOrderingPrinciple and PermLength from POP24_HerlihyWingQueuePrelude.
THEOREM LinearizabilityFromInvNL == InvNL => Linearizable
  <1> SUFFICES ASSUME InvNL
              PROVE  M # {}
    BY DEF Linearizable
  <1> DEFINE A == {k \in 1..X-1 : Q[k] # BOT}
  <1>1. A \in SUBSET 1..X-1
    OBVIOUS
  <1>2. GoodEnqSet(A)
    BY DEF GoodEnqSet
  <1> HIDE DEF A
  <1>3. IsFiniteSet(A)
    <2>1. IsFiniteSet(1..X-1)
      BY FS_Interval, Isa DEF InvNL, TypeOK, PosInts
    <2> QED
      BY <2>1, <1>1, FS_Subset, Isa
  <1>4. A \in SUBSET Int /\ IsFiniteSet(A)
    BY <1>1, <1>3 DEF TypeOK
  <1>5. PICK seq \in [1..Cardinality(A) -> A] : \A m, n \in 1..Cardinality(A) : m < n => seq[m] < seq[n]
    BY WellOrderingPrinciple, <1>4, Zenon DEF Bijection, Surjection
  <1>6. seq \in Perm(A)             
    <2> SUFFICES ASSUME NEW w \in A,
                            \A q \in 1..Cardinality(A) : seq[q] # w
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
      BY Zenon, FS_PigeonHole, <2>1, <2>5, <2>6, <2>7
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
                PROVE  \E p \in ProcSet : /\ pc[p] = "D3"
                                          /\ seq[n] < l[p]
                                          /\ seq[m] < j[p]
      BY DEF JInvSeq
    <2>1. Len(seq) = Cardinality(A)
      BY PermLength, <1>3, <1>6
    <2>2. m \in 1..Cardinality(A) /\ n \in 1..Cardinality(A)
      BY <2>1
    <2>4. seq[n] < seq[m]
      BY <1>5, <2>2 DEF Perm
    <2>5. /\ seq[n] \in 1..X-1
          /\ seq[m] \in 1..X-1
      BY <2>2, <1>1, Zenon DEF Perm
    <2> QED
      BY <2>4, <2>5
  <1> HIDE <1>5
  <1>8. \E c \in M : /\ ValuesMatchInds(seq, c.sigma)
                    /\ GoodRes(A, c.fres)
    BY <1>1, <1>2, <1>7, <1>6 DEF InvNL, Inv_Main
  <1> QED
    BY <1>8
       
\* Full inductive invariant.
Inv == /\ TypeOK
       /\ Inv_E2
       /\ Inv_E3
       /\ Inv_D2
       /\ Inv_D3
       /\ Inv_Q
       /\ Inv_Main
       /\ Linearizable

\* Assumptions regarding the model values ACK and BOT.
ASSUME AckBotDef == /\ ACK # BOT
                    /\ BOT \notin Nat

\* Proof of inductive invariant without linearizability
THEOREM InductiveInvariantNL == Spec => []InvNL
  <1> USE AckBotDef DEF InvNL, PosInts
  <1> SUFFICES /\ (Init => InvNL)
               /\ (InvNL /\ [Next]_vars => InvNL')
    BY PTL DEF Spec
  <1>1. Init => InvNL
    <2> SUFFICES ASSUME Init
                 PROVE  InvNL
      OBVIOUS
    <2> USE DEF Init
    <2>1. TypeOK
      BY InitTypeSafety
    <2>2. Inv_E2
      BY DEF Inv_E2
    <2>3. Inv_E3
      BY DEF Inv_E3
    <2>4. Inv_D2
      BY DEF Inv_D2
    <2>5. Inv_D3
      BY DEF Inv_D3
    <2>6. Inv_Q
      BY DEF Inv_Q
    <2>7. Inv_Main
      <3> SUFFICES ASSUME NEW A \in SUBSET (1..(X-1)),
                        GoodEnqSet(A),
                        NEW seq \in Perm(A),
                        JInvSeq(seq)
                 PROVE  \E c \in M : /\ ValuesMatchInds(seq, c.sigma)
                                     /\ GoodRes(A, c.fres)
        BY Zenon DEF Inv_Main
      <3>1. A = {}
        BY DEF GoodEnqSet
      <3>2. Cardinality(A) = 0
        BY <3>1, Zenon DEF Cardinality
      <3>3. seq = << >>
        BY <3>1, <3>2 DEF Perm, JInvSeq
      <3> QED
        BY <3>1, <3>3 DEF ValuesMatchInds, GoodRes
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF InvNL
  <1>2. InvNL /\ [Next]_vars => InvNL'
    <2> SUFFICES ASSUME InvNL /\ [Next]_vars
                 PROVE  InvNL'
      OBVIOUS
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. Inv_E2'
      <3> USE DEF Inv_E2
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv_E2'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW p \in ProcSet,
                   E1(p)
            PROVE  Inv_E2'
        <4> USE <3>2 DEF E1
        <4> SUFFICES ASSUME NEW q \in ProcSet,
                            pc'[q] = "E2"
                     PROVE  /\ 1 <= i'[q] /\ i'[q] < X' /\ Q'[i'[q]] = BOT
                            /\ \A r \in ProcSet : pc'[r] \in {"E2", "E3"} /\ r # q => i'[r] # i'[q]
          OBVIOUS
        <4>1. 1 <= i'[q]
          BY DEF TypeOK
        <4>2. i'[q] < X'
          BY DEF TypeOK
        <4>3. Q'[i'[q]] = BOT
          BY DEF TypeOK, Inv_Q
        <4>4. \A r \in ProcSet : pc'[r] \in {"E2", "E3"} /\ r # q => i'[r] # i'[q]
          <5> SUFFICES ASSUME NEW r \in ProcSet,
                              pc'[r] \in {"E2", "E3"} /\ r # q
                       PROVE  i'[r] # i'[q]
            OBVIOUS
          <5>1. CASE q # p /\ r # p
            BY <5>1 DEF TypeOK
          <5>2. CASE q = p \/ r = p
            <6>1. PICK s \in {q, r} : s # p
              BY <5>2
            <6>2. i[s] < X
              BY <6>1 DEF TypeOK, Inv_E3 
            <6> QED
              BY <6>1, <6>2 DEF TypeOK
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>3. ASSUME NEW p \in ProcSet,
                   E2(p)
            PROVE  Inv_E2'
        BY <3>3 DEF E2, TypeOK
      <3>4. ASSUME NEW p \in ProcSet,
                   E3(p)
            PROVE  Inv_E2'
        BY <3>4 DEF E3
      <3>5. ASSUME NEW p \in ProcSet,
                   D1(p)
            PROVE  Inv_E2'
        BY <3>5 DEF D1
      <3>6. ASSUME NEW p \in ProcSet,
                   D2(p)
            PROVE  Inv_E2'
        BY <3>6 DEF D2, TypeOK
      <3>7. ASSUME NEW p \in ProcSet,
                   D3(p)
            PROVE  Inv_E2'
        BY <3>7 DEF D3, TypeOK
      <3>8. ASSUME NEW p \in ProcSet,
                   D4(p)
            PROVE  Inv_E2'
        BY <3>8 DEF D4
      <3>9. CASE UNCHANGED vars
        BY <3>9 DEF vars
      <3>10. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>3. Inv_E3'
      <3> USE DEF Inv_E3
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv_E3'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW p \in ProcSet,
                   E1(p)
            PROVE  Inv_E3'
        BY <3>2 DEF E1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   E2(p)
            PROVE  Inv_E3'
        BY <3>3 DEF E2, TypeOK, Inv_E2
      <3>4. ASSUME NEW p \in ProcSet,
                   E3(p)
            PROVE  Inv_E3'
        BY <3>4 DEF E3
      <3>5. ASSUME NEW p \in ProcSet,
                   D1(p)
            PROVE  Inv_E3'
        BY <3>5 DEF D1
      <3>6. ASSUME NEW p \in ProcSet,
                   D2(p)
            PROVE  Inv_E3'
        BY <3>6 DEF D2, TypeOK
      <3>7. ASSUME NEW p \in ProcSet,
                   D3(p)
            PROVE  Inv_E3'
        BY <3>7 DEF D3, TypeOK
      <3>8. ASSUME NEW p \in ProcSet,
                   D4(p)
            PROVE  Inv_E3'
        BY <3>8 DEF D4
      <3>9. CASE UNCHANGED vars
        BY <3>9 DEF vars
      <3>10. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>4. Inv_D2'
      <3> USE DEF Inv_D2
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv_D2'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW p \in ProcSet,
                   E1(p)
            PROVE  Inv_D2'
        BY <3>2 DEF E1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   E2(p)
            PROVE  Inv_D2'
        BY <3>3 DEF E2
      <3>4. ASSUME NEW p \in ProcSet,
                   E3(p)
            PROVE  Inv_D2'
        BY <3>4 DEF E3
      <3>5. ASSUME NEW p \in ProcSet,
                   D1(p)
            PROVE  Inv_D2'
        BY <3>5 DEF D1, TypeOK
      <3>6. ASSUME NEW p \in ProcSet,
                   D2(p)
            PROVE  Inv_D2'
        BY <3>6 DEF D2, TypeOK
      <3>7. ASSUME NEW p \in ProcSet,
                   D3(p)
            PROVE  Inv_D2'
        BY <3>7 DEF D3, TypeOK
      <3>8. ASSUME NEW p \in ProcSet,
                   D4(p)
            PROVE  Inv_D2'
        BY <3>8 DEF D4
      <3>9. CASE UNCHANGED vars
        BY <3>9 DEF vars
      <3>10. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>5. Inv_D3'
      <3> USE DEF Inv_D3
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv_D3'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW p \in ProcSet,
                   E1(p)
            PROVE  Inv_D3'
        BY <3>2 DEF E1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   E2(p)
            PROVE  Inv_D3'
        BY <3>3 DEF E2
      <3>4. ASSUME NEW p \in ProcSet,
                   E3(p)
            PROVE  Inv_D3'
        BY <3>4 DEF E3
      <3>5. ASSUME NEW p \in ProcSet,
                   D1(p)
            PROVE  Inv_D3'
        BY <3>5 DEF D1
      <3>6. ASSUME NEW p \in ProcSet,
                   D2(p)
            PROVE  Inv_D3'
        BY <3>6 DEF D2, TypeOK, Inv_D2
      <3>7. ASSUME NEW p \in ProcSet,
                   D3(p)
            PROVE  Inv_D3'
        BY <3>7 DEF D3, TypeOK
      <3>8. ASSUME NEW p \in ProcSet,
                   D4(p)
            PROVE  Inv_D3'
        BY <3>8 DEF D4
      <3>9. CASE UNCHANGED vars
        BY <3>9 DEF vars
      <3>10. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>6. Inv_Q'
      <3> USE DEF Inv_Q
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv_Q'
        BY <3>1 DEF L0
      <3>2. ASSUME NEW p \in ProcSet,
                   E1(p)
            PROVE  Inv_Q'
        BY <3>2 DEF E1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   E2(p)
            PROVE  Inv_Q'
        BY <3>3 DEF E2, TypeOK, Inv_E2
      <3>4. ASSUME NEW p \in ProcSet,
                   E3(p)
            PROVE  Inv_Q'
        BY <3>4 DEF E3
      <3>5. ASSUME NEW p \in ProcSet,
                   D1(p)
            PROVE  Inv_Q'
        BY <3>5 DEF D1
      <3>6. ASSUME NEW p \in ProcSet,
                   D2(p)
            PROVE  Inv_Q'
        BY <3>6 DEF D2
      <3>7. ASSUME NEW p \in ProcSet,
                   D3(p)
            PROVE  Inv_Q'
        BY <3>7 DEF D3
      <3>8. ASSUME NEW p \in ProcSet,
                   D4(p)
            PROVE  Inv_Q'
        BY <3>8 DEF D4
      <3>9. CASE UNCHANGED vars
        BY <3>9 DEF vars
      <3>10. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2>7. Inv_Main'
      <3>1. CASE UNCHANGED vars
        <4> USE <3>1 DEF vars
        <4> SUFFICES ASSUME NEW A \in SUBSET 1..X'-1,
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                         /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
          BY DEF GoodEnqSet, JInvSeq, Inv_Main
        <4>2. ValuesMatchInds(seq, c.sigma)' /\ GoodRes(A, c.fres)'
          BY <4>1 DEF GoodRes, ValuesMatchInds
        <4> QED
          BY <4>1, <4>2
      <3>2. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv_Main'
        <4> USE <3>2 DEF L0
        <4> SUFFICES ASSUME NEW A \in SUBSET 1..X'-1,
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                         /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
          BY DEF GoodEnqSet, JInvSeq, Inv_Main
        <4>2. GoodRes(A, c.fres)'
          BY <4>1 DEF GoodRes
        <4>3. ValuesMatchInds(seq, c.sigma) = ValuesMatchInds(seq, c.sigma)'
          <5> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                       [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
          <5> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
          <5>1. vals_1 = vals_2
            <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE vals_1[k] = vals_2[k]
              BY Zenon
            <6>1. CASE Q[seq[k]] # BOT
              BY <6>1
            <6>2. CASE Q[seq[k]] = BOT
              BY <6>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY Zenon, <5>1 DEF ValuesMatchInds
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>3. ASSUME NEW p \in ProcSet,
                   E2(p)
            PROVE  Inv_Main'
        <4> USE <3>3, AckBotDef DEF E2
        <4> SUFFICES ASSUME NEW A \in SUBSET 1..X'-1,
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                         /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. GoodEnqSet(A)
          BY DEF GoodEnqSet, TypeOK
        <4>2. JInvSeq(seq)
          BY DEF JInvSeq, TypeOK
        <4>3. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
          BY <4>1, <4>2 DEF Inv_Main
        <4>4. i[p] \in A
          BY DEF GoodEnqSet, TypeOK, Inv_E2
        <4>5. GoodRes(A, c.fres)'
          BY <4>3, <4>4 DEF GoodRes, TypeOK
        <4>6. ValuesMatchInds(seq, c.sigma)'
          <5> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                       [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
          <5> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
          <5>1. vals_1 = vals_2
            <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE vals_1[k] = vals_2[k]
              BY Zenon
            <6>1. CASE seq[k] # i[p]
              BY <6>1 DEF Inv_E2, GoodEnqSet, Perm
            <6>2. CASE seq[k] = i[p]
              BY <6>2 DEF TypeOK, Inv_E2
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY Zenon, <4>3, <5>1 DEF ValuesMatchInds
        <4> QED
          BY <4>5, <4>6
      <3>4. ASSUME NEW p \in ProcSet,
                   E3(p)
            PROVE  Inv_Main'
        <4> USE <3>4 DEF E3
        <4> SUFFICES ASSUME NEW A \in SUBSET (1..(X'-1)),
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE  \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                          /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. GoodEnqSet(A)
          BY DEF GoodEnqSet
        <4>2. JInvSeq(seq)
          BY DEF JInvSeq
        <4>3. PICK d \in M : ValuesMatchInds(seq, d.sigma) /\ GoodRes(A, d.fres)
          BY <4>1, <4>2 DEF Inv_Main
        <4>4. d.fres[p] = ACK
          BY <4>3 DEF GoodRes
        <4> DEFINE c == [sigma |-> d.sigma, fres |-> [d.fres EXCEPT ![p] = BOT]]
        <4>5. c \in CDomain
          BY <4>3 DEF CDomain, CFTypeOK, TypeOK
        <4>6. c \in M'
          BY Zenon, <4>4, <4>5 DEF Filter, TypeOK, CDomain
        <4>7. ValuesMatchInds(seq, c.sigma)'
          <5> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                       [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
          <5> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
          <5>1. vals_1 = vals_2
            <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE vals_1[k] = vals_2[k]
              BY Zenon
            <6>1. CASE Q[seq[k]] # BOT
              BY <6>1
            <6>2. CASE Q[seq[k]] = BOT
              BY <6>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY Zenon, <4>3, <5>1 DEF ValuesMatchInds
        <4>8. GoodRes(A, c.fres)'
          <5> DEFINE GoodProcRes(q, res) == res[q] = CASE (pc[q] = "E2" /\ i[q] \in A) -> ACK
                                                       [] (pc[q] = "E3")               -> ACK
                                                       [] (pc[q] = "D4")               -> x[q]
                                                       [] OTHER                        -> BOT
          <5>1. \A q \in ProcSet : q # p => GoodProcRes(q, d.fres)'
            BY <4>3 DEF GoodRes
          <5>2. \A q \in ProcSet : q # p => GoodProcRes(q, c.fres)'
            BY <5>1 DEF Filter
          <5>3. pc'[p] = "L0"
            BY DEF TypeOK
          <5>4. GoodProcRes(p, c.fres)'
            BY <5>3 DEF Filter, CDomain, TypeOK
          <5>5. \A r \in ProcSet : GoodProcRes(r, c.fres)'
            BY <5>1, <5>4
          <5> QED
            BY <5>5 DEF GoodRes
        <4> QED
          BY <4>6, <4>7, <4>8
      <3>5. ASSUME NEW p \in ProcSet,
                   D1(p)
            PROVE  Inv_Main'
        <4> USE <3>5 DEF D1
        <4> SUFFICES ASSUME NEW A \in SUBSET 1..X'-1,
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                         /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
          BY DEF GoodEnqSet, JInvSeq, Inv_Main
        <4>2. GoodRes(A, c.fres)'
          BY <4>1 DEF GoodRes
        <4>3. ValuesMatchInds(seq, c.sigma) = ValuesMatchInds(seq, c.sigma)'
          <5> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                       [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
          <5> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
          <5>1. vals_1 = vals_2
            <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE vals_1[k] = vals_2[k]
              BY Zenon
            <6>1. CASE Q[seq[k]] # BOT
              BY <6>1
            <6>2. CASE Q[seq[k]] = BOT
              BY <6>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY Zenon, <5>1 DEF ValuesMatchInds
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>6. ASSUME NEW p \in ProcSet,
                   D2(p)
            PROVE  Inv_Main'
        <4> USE <3>6 DEF D2
        <4> SUFFICES ASSUME NEW A \in SUBSET 1..X'-1,
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                         /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. GoodEnqSet(A)
          BY DEF TypeOK, GoodEnqSet
        <4>2. \A q \in ProcSet : q # p => pc[q] = pc'[q] /\ l[q] = l'[q] /\ j[q] = j'[q]
          BY DEF TypeOK
        <4>3. Len(seq) = Cardinality(A)
          <5>1. IsFiniteSet(1..(X-1))
            BY FS_Interval DEF TypeOK
          <5>2. IsFiniteSet(A)
            BY Zenon, <5>1, FS_Subset
          <5> QED
            BY <5>2, PermLength
        <4>4. JInvSeq(seq)
          <5> SUFFICES ASSUME NEW m \in 1..Len(seq),
                              NEW n \in 1..Len(seq),
                              n < m, seq[n] > seq[m],
                              Q[seq[m]] # BOT
                       PROVE  \E q \in ProcSet : pc[q] = "D3" /\ seq[n] < l[q] /\ seq[m] < j[q]
            BY DEF JInvSeq
          <5>1. Q'[seq[m]] # BOT
            OBVIOUS
          <5>2. PICK q \in ProcSet : pc'[q] = "D3" /\ seq[n] < l'[q] /\ seq[m] < j'[q]
            BY DEF JInvSeq
          <5>3. CASE q # p
            BY <5>2, <5>3, <4>2 DEF TypeOK
          <5>4. CASE q = p
            <6>1. CASE l[p] = 1
              BY <5>2, <5>4, <6>1 DEF TypeOK
            <6>2. CASE l[p] # 1
              <7> USE <6>2
              <7>1. j'[p] = 1
                BY DEF TypeOK
              <7>2. seq[m] < 1
                BY <5>2, <5>4, <7>1
              <7>3. seq[m] \in A
                BY <4>3 DEF Perm
              <7>4. seq[m] \in 1..X-1
                BY Zenon, <7>3
              <7> QED
                BY <7>2, <7>4
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY <5>3, <5>4
        <4>5. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
          BY <4>1, <4>4 DEF Inv_Main
        <4>6. ValuesMatchInds(seq, c.sigma)'
          <5> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                       [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
          <5> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
          <5>1. vals_1 = vals_2
            <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE vals_1[k] = vals_2[k]
              BY Zenon
            <6>1. CASE Q[seq[k]] # BOT
              BY <6>1
            <6>2. CASE Q[seq[k]] = BOT
              BY <6>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY Zenon, <4>5, <5>1 DEF ValuesMatchInds
        <4>7. GoodRes(A, c.fres)'
          BY <4>5 DEF GoodRes, TypeOK
        <4> QED
          BY <4>6, <4>7
      <3>7. ASSUME NEW p \in ProcSet,
                   D4(p)
            PROVE  Inv_Main'
        <4> USE <3>7 DEF D4
        <4> SUFFICES ASSUME NEW A \in SUBSET (1..(X'-1)),
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE  \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                          /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. GoodEnqSet(A)
          BY DEF GoodEnqSet
        <4>2. JInvSeq(seq)
          BY DEF JInvSeq
        <4>3. PICK d \in M : ValuesMatchInds(seq, d.sigma) /\ GoodRes(A, d.fres)
          BY <4>1, <4>2 DEF Inv_Main
        <4>4. d.fres[p] = x[p]
          BY <4>3 DEF GoodRes
        <4> DEFINE c == [sigma |-> d.sigma, fres |-> [d.fres EXCEPT ![p] = BOT]]
        <4>5. c \in CDomain
          BY <4>3 DEF CDomain, CFTypeOK, TypeOK
        <4>6. c \in M'
          BY Zenon, <4>4, <4>5 DEF Filter, TypeOK, CDomain
        <4>7. ValuesMatchInds(seq, c.sigma)'
          <5> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                       [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
          <5> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
          <5>1. vals_1 = vals_2
            <6> SUFFICES ASSUME NEW k \in DOMAIN seq
                         PROVE vals_1[k] = vals_2[k]
              BY Zenon
            <6>1. CASE Q[seq[k]] # BOT
              BY <6>1
            <6>2. CASE Q[seq[k]] = BOT
              BY <6>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY Zenon, <4>3, <5>1 DEF ValuesMatchInds
        <4>8. GoodRes(A, c.fres)'
          <5> DEFINE GoodProcRes(q, res) == res[q] = CASE (pc[q] = "E2" /\ i[q] \in A) -> ACK
                                                       [] (pc[q] = "E3")               -> ACK
                                                       [] (pc[q] = "D4")               -> x[q]
                                                       [] OTHER                        -> BOT
          <5>1. \A q \in ProcSet : q # p => GoodProcRes(q, d.fres)'
            BY <4>3 DEF GoodRes
          <5>2. \A q \in ProcSet : q # p => GoodProcRes(q, c.fres)'
            BY <5>1 DEF Filter
          <5>3. pc'[p] = "L0"
            BY DEF TypeOK
          <5>4. GoodProcRes(p, c.fres)'
            BY <5>3 DEF Filter, CDomain, TypeOK
          <5>5. \A r \in ProcSet : GoodProcRes(r, c.fres)'
            BY <5>1, <5>4
          <5> QED
            BY <5>5 DEF GoodRes
        <4> QED
          BY <4>6, <4>7, <4>8
      <3>8. ASSUME NEW p \in ProcSet,
                   D3(p)
            PROVE  Inv_Main'
        <4> USE <3>8 DEF D3
        <4> SUFFICES ASSUME NEW A \in SUBSET (1..(X'-1)),
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE  \E c \in M' : /\ ValuesMatchInds(seq, c.sigma)'
                                          /\ GoodRes(A, c.fres)'
          BY DEF Inv_Main
        <4>1. \A q \in ProcSet : q # p => pc[q] = pc'[q] /\ l[q] = l'[q] /\ j[q] = j'[q]
          BY DEF TypeOK
        <4>2. Len(seq) = Cardinality(A)
          <5>1. IsFiniteSet(1..(X-1))
            BY FS_Interval DEF TypeOK
          <5>2. IsFiniteSet(A)
            BY Zenon, <5>1, FS_Subset
          <5> QED
            BY <5>2, PermLength
        <4>3. CASE Q[j[p]] = BOT
          <5> USE <4>3
          <5>1. GoodEnqSet(A)
            BY <4>1 DEF GoodEnqSet, TypeOK
          <5>2. JInvSeq(seq)
            <6> SUFFICES ASSUME NEW m \in 1..Len(seq),
                                NEW n \in 1..Len(seq),
                                n < m, seq[n] > seq[m],
                                Q[seq[m]] # BOT
                         PROVE  \E q \in ProcSet : pc[q] = "D3" /\ seq[n] < l[q] /\ seq[m] < j[q]
              BY DEF JInvSeq
            <6>1. PICK q \in ProcSet : pc'[q] = "D3" /\ seq[n] < l'[q] /\ seq[m] < j'[q]
              BY DEF JInvSeq
            <6>2. CASE q # p
              BY <6>1, <6>2, <4>1
            <6>3. CASE q = p
              <7> USE <6>3
              <7>1. CASE j[p] = l[p] - 1
                BY <7>1, <6>1
              <7>2. CASE j[p] # l[p] - 1
                <8> USE <7>2
                <8>1. seq[m] < j[p] + 1
                  BY <6>1 DEF TypeOK
                <8>2. m \in 1..Cardinality(A)
                  BY <4>2 DEF Perm
                <8>3. seq[m] \in Nat
                  <9>1. seq[m] \in (1..(X' - 1))
                    BY Zenon, <8>2 DEF Perm
                  <9> QED
                    BY <9>1 DEF TypeOK
                <8>4. seq[m] < j[p]
                  BY <8>1, <8>3 DEF TypeOK
                <8> QED
                  BY <8>4, <6>1
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <6>2, <6>3
          <5>3. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
            BY <5>1, <5>2 DEF Inv_Main
          <5>4. ValuesMatchInds(seq, c.sigma)'
            <6> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT -> Q[seq[k]]
                                                         [] OTHER           -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
            <6> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                         [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
            <6>1. vals_1 = vals_2
              <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                           PROVE vals_1[k] = vals_2[k]
                BY Zenon
              <7>1. CASE Q[seq[k]] # BOT
                BY <7>1
              <7>2. CASE Q[seq[k]] = BOT
                BY <7>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY Zenon, <5>3, <6>1 DEF ValuesMatchInds
          <5>5. GoodRes(A, c.fres)'
            BY <5>3 DEF GoodRes, TypeOK
          <5> QED
            BY <5>3, <5>4, <5>5
        <4>4. CASE Q[j[p]] # BOT
          <5> USE <4>4
          <5>1. j[p] \notin A
            <6>1. Q'[j[p]] = BOT
              BY DEF TypeOK
            <6> DEFINE ActiveProcess == \E r \in ProcSet : pc'[r] = "E2" /\ i'[r] = j[p]
            <6>2. j[p] \in A => ActiveProcess
              BY Zenon, <6>1 DEF GoodEnqSet
            <6>3. ActiveProcess => Q[j[p]] = BOT
              BY DEF Inv_E2, TypeOK
            <6> QED
              BY <6>2, <6>3
          \* A_ and seq_ justify the existence of the corresponding configuration in M
          \* through Inv_Main.
          <5> DEFINE A_ == A \union {j[p]}
          <5> DEFINE seq_ == Concat(<<j[p]>>, seq)
          
          \* Some useful auxiliary facts about A, seq, seq_
          <5>2. IsFiniteSet(1..X'-1)
            BY FS_Interval DEF TypeOK
          <5>3. IsFiniteSet(A)
            BY Zenon, FS_Subset, <5>2
          <5>4. Cardinality(A) \in Nat
            BY FS_CardinalityType, <5>3
          <5>5. Len(seq) \in Nat
            BY <5>4 DEF Len, Perm
          <5>6. seq_ = [k \in 1..(1+Len(seq)) |-> IF k <= 1 THEN <<j[p]>>[k] ELSE seq[k-Len(<<j[p]>>)]]
            BY DEF Concat, Len
          <5>7. Len(<<j[p]>>) = 1
            BY DEF Len
          <5>8. seq_ = [k \in 1..(1+Len(seq)) |-> IF k <= 1 THEN <<j[p]>>[k] ELSE seq[k-1]]
            BY Zenon, <5>6, <5>7
          <5>9. seq_[1] = j[p]
            BY <5>6, <5>5
          <5>10. Len(seq_) = Len(seq) + 1
            BY <5>5 DEF Concat, Len
          <5>11. Len(seq_) \in Nat
            BY <5>10, <5>5
            
          <5>12. Cardinality(A_) = Cardinality(A) + 1
            <6>1. IsFiniteSet(1..(X-1))
              BY FS_Interval DEF TypeOK
            <6>2. IsFiniteSet(A)
              BY <5>3
            <6> QED
              BY Zenon, <5>1, <6>2, FS_AddElement, FS_CountingElements, FS_EmptySet
          
          <5>13. Len(seq_) = Cardinality(A_)
            BY <4>2, <5>10, <5>12
            
          <5>14. \A k \in (2..(Len(seq) + 1)) : k-1 \in 1..1+Len(seq)
            BY <5>5
            
          <5>15. \A k \in (2..(Len(seq) + 1)) : seq_[k] = seq[k - 1]
            BY <5>9, <5>5, <5>8
            
          <5>16. A_ \in SUBSET (1..(X-1))
            <6>1. j[p] \in 1..X-1
              BY DEF Inv_D3, TypeOK
            <6> QED
              BY Zenon, <6>1
              
          <5>17. GoodEnqSet(A_)
            <6> SUFFICES ASSUME NEW k \in 1..X-1
                         PROVE  /\ Q[k] # BOT => k \in A_
                                /\ (k \in A_ /\ Q[k] = BOT) => \E q \in ProcSet : pc[q] = "E2" /\ i[q] = k
              BY DEF GoodEnqSet
            <6>1. CASE k # j[p]
              <7> USE <6>1
              <7>1. CASE Q[k] # BOT
                BY <7>1 DEF GoodEnqSet
              <7>2. CASE k \in A_ /\ Q[k] = BOT
                BY <7>2, <4>1 DEF GoodEnqSet, TypeOK
              <7> QED
                BY <7>1, <7>2
            <6>2. CASE k = j[p]
              BY <6>2
            <6> QED
              BY <6>1, <6>2
          
          <5>18. seq_ \in Perm(A_)
            <6>1. seq_ \in [1..Len(seq_) -> A_]
              <7>1. \A k \in (2..(Len(seq) + 1)) : seq_[k] \in A
                <8>3. \A k \in 1..Cardinality(A) : seq[k] \in A
                  BY DEF Perm
                <8>4. \A k \in 2..Cardinality(A)+1 : seq[k-1] \in A
                  BY FS_CardinalityType, <5>3, <8>3
                <8>5. \A k \in 2..Len(seq)+1 : seq[k-1] \in A
                  BY <8>4, <5>4 DEF Len, Perm
                <8> QED
                  BY <5>15, <8>5
              <7>2. \A k \in (1..(Len(seq_))) : seq_[k] \in A_
                BY <5>9, <7>1, <5>10
              <7>3. Len(<<j[p]>>) = 1
                BY DEF Len
              <7>4. DOMAIN seq_ = 1..(Len(seq) + 1)
                BY <5>5, <7>3 DEF Concat, Len
              <7>5. Len(seq_) = Len(seq) + 1
                BY <5>5 DEF TypeOK, Concat, Len
              <7>6. DOMAIN seq_ = 1..Len(seq_)
                BY Zenon, <7>4, <7>5
              <7> QED
                BY <7>2, <7>6 DEF Concat
            <6>2. \A w \in A_ : \E k \in 1..Len(seq_) : seq_[k] = w
              <7> SUFFICES ASSUME NEW w \in A_
                                  PROVE \E k \in 1..Len(seq_) : seq_[k] = w
                OBVIOUS
              <7>1. CASE w = j[p]
                BY <5>9, <7>1, <5>10, <5>5
              <7>2. CASE w \in A
                <8> USE <7>2
                <8>1. PICK k \in 1..Len(seq) : seq[k] = w
                  BY <4>2 DEF Perm
                <8>2. k+1 \in 2..Len(seq_)
                  BY <5>10, <5>11, <5>5
                <8>3. seq_[k+1] = seq[k]
                  BY <8>2, <5>15, <5>5
                <8> QED
                  BY <8>2, <8>3, <8>1
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <5>13, <6>1, <6>2 DEF Perm
                
          <5>19. JInvSeq(seq_)      
            <6> SUFFICES ASSUME NEW m \in 1..Len(seq_), NEW n \in 1..Len(seq_),
                                 /\ n < m
                                 /\ seq_[n] > seq_[m]
                                 /\ Q[seq_[m]] # BOT
                         PROVE  \E q \in ProcSet : /\ pc[q] = "D3"
                                                   /\ seq_[n] < l[q]
                                                   /\ seq_[m] < j[q]
              BY DEF JInvSeq
            <6>1. CASE m \in 2..Len(seq_) /\ n \in 2..Len(seq_)
              <7> USE <6>1
              <7>1. n - 1 < m - 1
                OBVIOUS
              <7>2. seq[n - 1] > seq[m - 1]
                BY <5>10, <5>15
              <7>3. Q'[seq[m - 1]] # BOT
                <8>1. Q[seq[m - 1]] # BOT
                  BY <5>10, <5>15
                <8>2. m \in 2..Cardinality(A)+1 => seq[m-1] \in A
                  BY <5>3, FS_CardinalityType DEF Perm
                <8>3. Len(seq) = Cardinality(A)
                  BY FS_CardinalityType, <5>3 DEF Len, Perm
                <8>4. Len(seq)+1 = Len(seq_)
                  BY <5>10
                <8>5. seq[m - 1] \in A
                  BY <8>2, <8>3, <8>4
                <8>6. seq[m - 1] # j[p]
                  BY <5>1, <8>5
                <8> QED
                  BY <8>1, <8>6
              <7>4. PICK q \in ProcSet : pc'[q] = "D3" /\ seq[n - 1] < l'[q] /\ seq[m - 1] < j'[q]
                BY <7>1, <7>2, <7>3, <5>10, <5>5 DEF JInvSeq
              <7>5. seq_[n] < l'[q] /\ seq_[m] < j'[q]
                BY <7>4, <5>15, <5>10
              <7>6. CASE q # p
                BY <7>4, <7>5, <7>6, <4>1
              <7>7. CASE q = p
                <8>1. pc' = [pc EXCEPT ![p] = "D4"]
                  OBVIOUS
                <8>2. pc'[p] = "D4"
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
                BY <5>9 DEF Inv_D3
              <7>2. seq_[m] < j[p]
                BY <5>9
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <6>1, <6>2, <6>3
          
          <5>20. PICK c \in M : ValuesMatchInds(seq_, c.sigma) /\ GoodRes(A_, c.fres)
            BY <5>16, <5>17, <5>18, <5>19 DEF Inv_Main
                
          <5> DEFINE d == [sigma |-> Tail(c.sigma), fres |-> [c.fres EXCEPT ![p] = Head(c.sigma)]]
        
          <5>21. d.fres[p] = Head(c.sigma)
            BY DEF TypeOK, CDomain
            
          <5>22. d \in M'
            <6>1. d.sigma = Tail(c.sigma)
              OBVIOUS
            <6>2. \A r \in ProcSet : r # p => d.fres[r] = c.fres[r]
              OBVIOUS
            <6>3. \E c_ \in M : /\ d.sigma = Tail(c_.sigma) 
                                /\ d.fres[p] = Head(c_.sigma) 
                                /\ \A r \in ProcSet : r # p => d.fres[r] = c_.fres[r]
              BY <5>21, <6>1, <6>2
            <6>4. c \in CDomain
              BY DEF TypeOK  
            <6>5. c.sigma \in Seqs(PosInts)
              BY <6>4 DEF CDomain
            <6>6. \E z \in Nat : DOMAIN c.sigma = 1..z
              BY <6>5 DEF Seqs
            <6>7. DOMAIN c.sigma = 1..Len(c.sigma)
              BY <6>6 DEF Len
            <6>8. c.sigma \in [1..Len(c.sigma) -> PosInts]
              BY Zenon, <6>7, <6>5 DEF Seqs
            <6>9. Len(c.sigma) \in Nat
              BY <6>6 DEF Len
            <6>10. Head(c.sigma) \in PosInts \union {BOT}
              BY <6>5 DEF Head, Seqs
            <6>11. d \in CDomain
              <7>1. d.sigma \in [1..Len(c.sigma)-1 -> PosInts]
                BY <6>9, <6>8 DEF Tail
              <7>2. Len(c.sigma) < 1 => d.sigma \in [1..0 -> PosInts]
                BY <7>1, <6>9
              <7>3. d.sigma \in Seqs(PosInts)
                BY <7>1, <7>2, <6>9 DEF Seqs
              <7>4. Head(c.sigma) \in PosInts \union {BOT}
                BY <6>10 DEF Head
              <7>5. d.fres \in [ProcSet -> PosInts \union {ACK, BOT}]
                BY <7>4 DEF CDomain, TypeOK
              <7> QED
                BY <7>3, <7>5 DEF CDomain
            <6>12. CFTypeOK(d)'
              <7> SUFFICES ASSUME NEW q \in ProcSet
                           PROVE  /\ pc'[q] \in {"L0", "E1", "D1", "D2", "D3"}  => d.fres[q] = BOT
                                  /\ pc'[q] \in {"E2", "E3"}                    => d.fres[q] \in {ACK, BOT}
                                  /\ pc'[q] = "D4"                              => d.fres[q] \in PosInts \union {BOT}
                BY DEF CFTypeOK
              <7>1. CASE q = p
                BY <7>1, <6>10, <5>21 DEF TypeOK
              <7>2. CASE q # p
                BY <7>2, <6>2, <4>1 DEF TypeOK, CFTypeOK
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY Zenon, <6>3, <6>11, <6>12
              
          <5>23. ValuesMatchInds(seq, d.sigma)'
            <6> DEFINE vals == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                       [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i[r] = seq[k]]]
            <6>1. d.sigma \in [DOMAIN seq -> PosInts]
              <7>1. DOMAIN d.sigma = 1..(Len(c.sigma) - 1)
                BY DEF Tail
              <7>2. Len(seq_) = Len(c.sigma)
                BY <5>20 DEF ValuesMatchInds, Len
              <7>3. DOMAIN d.sigma = 1..Len(seq)
                BY <7>1, <7>2, <5>10, <5>5
              <7>4. d.sigma \in Seqs(PosInts)
                BY <2>1, <5>22, <5>5 DEF TypeOK, CDomain
              <7>5. DOMAIN seq = 1..Cardinality(A)
                BY DEF Perm, Len
              <7>6. Len(seq) = Cardinality(A)
                BY <5>4, <7>5 DEF Len
              <7>7. DOMAIN seq = 1..Len(seq)
                BY <7>5, <7>6
              <7> QED
                BY <7>3, <7>4, <7>7 DEF Seqs
            <6>2. vals \in [DOMAIN seq -> PosInts]
              <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                           PROVE  vals[k] \in PosInts
                OBVIOUS
              <7>1. CASE Q'[seq[k]] # BOT
                BY <7>1 DEF TypeOK, Perm
              <7>2. CASE Q'[seq[k]] = BOT
                <8> USE <7>2
                <8>1. seq[k] \in A
                  BY DEF Perm
                <8>2. PICK r \in ProcSet : pc'[r] = "E2" /\ i[r] = seq[k]
                  BY Zenon, <8>1 DEF GoodEnqSet
                <8>3. \A r_ \in ProcSet : pc'[r_] = "E2" /\ i[r_] = seq[k] => r_ = r
                  BY <8>2 DEF Inv_E2, TypeOK
                <8>4. vals[k] = v'[r]
                  BY <8>2, <8>3
                <8> QED
                  BY <8>4 DEF TypeOK
              <7> QED
                BY <7>1, <7>2
              
            <6>3. \A k \in DOMAIN seq : d.sigma[k] = vals[k]
              <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                           PROVE  d.sigma[k] = vals[k]
                BY Zenon
              <7>1. seq[k] # j[p]
                BY <5>1 DEF Perm
              <7>2. k \in 1..Len(d.sigma)
                BY <5>4, <6>1 DEF Perm, Len
              <7>3. DOMAIN seq_ = DOMAIN c.sigma
                BY <5>20 DEF ValuesMatchInds
              <7>4. DOMAIN c.sigma = 1..(1+Len(seq))
                BY <7>3, <5>8
              <7>5. Len(c.sigma) = 1 + Len(seq)
                BY <5>5, <7>4 DEF Len
              <7>6. Len(d.sigma) = Len(seq)
                BY <6>1 DEF Len
              <7>7. Len(d.sigma) = Len(c.sigma) - 1
                BY <7>5, <7>6, <5>5
              <7>8. d.sigma[k] = c.sigma[k + 1]
                BY <7>2, <7>7 DEF Tail
              <7>9. seq[k] = seq_[k + 1]
                BY <5>15, <7>6, <7>2, <5>5
              <7>10. k \in 1..Len(seq)
                BY <7>2, <7>6, <5>5 DEF Perm
              <7>11. k + 1 \in DOMAIN seq_
                BY <7>3, <7>4, <7>10, <5>5
              <7>12. Q[seq[k]] = Q'[seq[k]]
                BY <7>1
              <7>13. CASE Q'[seq[k]] # BOT
                <8> USE <7>13
                <8>1. Q[seq_[k + 1]] = c.sigma[k + 1]
                  BY <7>9, <7>11, <5>20 DEF ValuesMatchInds
                <8> QED
                  BY <7>8, <7>9, <8>1, <7>12
              <7>14. CASE Q'[seq[k]] = BOT
                <8> USE <7>14
                <8>1. Q[seq_[k + 1]] = BOT
                  BY <7>12, <7>9
                <8>2. seq[k] \in A
                  BY DEF Perm
                <8>3. seq_[k + 1] \in A_
                  BY <7>9, <8>2
                <8>4. PICK q \in ProcSet : pc[q] = "E2" /\ i[q] = seq_[k + 1]                
                  BY <5>17, <5>16, <8>1, <8>3 DEF GoodEnqSet
                <8>5. \A r \in ProcSet : (pc[r] = "E2" /\ i[r] = seq_[k + 1]) => r = q
                  BY <8>4 DEF Inv_E2
                <8>6. c.sigma[k + 1] = v[q]
                  BY <7>9, <7>11, <8>1, <8>4, <8>5, <5>20 DEF ValuesMatchInds
                <8>7. pc'[q] = "E2" /\ i[q] = seq[k]
                  BY <8>4, <7>9 DEF TypeOK
                <8>8. \A r \in ProcSet : (pc'[r] = "E2" /\ i[r] = seq[k]) => r = q
                  BY <4>1, <8>5, <7>9 DEF Inv_E2, TypeOK
                <8>9. vals[k] = v[q]
                  BY <8>4, <8>7, <8>8
                <8> QED
                  BY <8>9, <8>6, <7>8 DEF TypeOK
              <7> QED
                BY <7>13, <7>14
            <6> QED
              BY Isa, <6>1, <6>2, <6>3 DEF ValuesMatchInds
          
          <5>24. GoodRes(A, d.fres)'
            <6> DEFINE GoodProcRes(S, res, q) == res[q] = CASE (pc[q] = "E2" /\ i[q] \in S) -> ACK
                                                            [] (pc[q] = "E3")               -> ACK
                                                            [] (pc[q] = "D4")               -> x[q]
                                                            [] OTHER                        -> BOT
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  GoodProcRes(A, d.fres, q)'
              BY DEF GoodRes
            <6>1. CASE q # p
              <7> USE <6>1
              <7>1. GoodProcRes(A_, d.fres, q)
                BY <5>20 DEF GoodRes
              <7>2. ~(pc[q] = "E2" /\ i[q] = j[p])
                BY DEF Inv_E2
              <7> QED
                BY <4>1, <7>1, <7>2
            <6>2. CASE q = p
              <7> USE <6>2
              <7>1. seq_[1] = j[p]
                BY <5>5, <5>6
              <7>2. c.sigma[1] = Q[j[p]]
                BY <7>1, <5>5, <5>8, <5>20 DEF ValuesMatchInds
              <7>3. c.sigma # <<>>
                BY <5>20, <5>10, <5>5, <5>6 DEF ValuesMatchInds
              <7>4. d.fres[p] = c.sigma[1]
                BY <7>3, <5>21 DEF Head
              <7> QED
                BY <7>2, <7>4 DEF TypeOK
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY <5>22, <5>23, <5>24
        <4> QED
          BY <4>3, <4>4
      <3>9. ASSUME NEW p \in ProcSet,
                   E1(p)
            PROVE  Inv_Main'
        <4> USE <3>9 DEF E1
        <4> SUFFICES ASSUME NEW A \in SUBSET 1..X'-1,
                            NEW seq \in Perm(A),
                            GoodEnqSet(A)',
                            JInvSeq(seq)'
                     PROVE  \E c \in M' : ValuesMatchInds(seq, c.sigma)' /\ GoodRes(A, c.fres)'
          BY Zenon DEF Inv_Main
        <4>1. i'[p] = X
          BY DEF TypeOK
        <4>2. CASE i'[p] \notin A
          <5> USE <4>2
          <5>1. pc'[p] = "E2" /\ i'[p] \notin A
            BY DEF TypeOK
          <5>2. \A k \in 1..X : /\ Q[k] # BOT => k \in A
                                /\ (k \in A /\ Q[k] = BOT) => (\E r \in ProcSet : pc'[r] = "E2" /\ i'[r] = k)
            BY DEF GoodEnqSet, TypeOK
          <5>3. GoodEnqSet(A)
            BY <5>2 DEF TypeOK, GoodEnqSet
          <5>4. seq \in Perm(A)
            BY DEF Perm
          <5>5. JInvSeq(seq)
            BY DEF JInvSeq, TypeOK
          <5>6. A \in SUBSET 1..X-1
            BY DEF TypeOK
          <5>7. PICK c \in M : ValuesMatchInds(seq, c.sigma) /\ GoodRes(A, c.fres)
            BY <5>3, <5>4, <5>5, <5>6 DEF Inv_Main
          <5> DEFINE S_ == {}
          <5> DEFINE seq_ == << >>
          <5>8. c \in CDomain /\ CFTypeOK(c)'
            BY <5>7 DEF TypeOK, CDomain, CFTypeOK
          <5>9. S_ \in SUBSET UnlinearizedEnqs(c)' /\ seq_ \in Perm(S_)
            BY FS_EmptySet DEF Perm, UnlinearizedEnqs
          <5>10. c.sigma = Concat(c.sigma, [k \in DOMAIN seq_ |-> v[seq[k]]])
            <6> DEFINE s2 == [k \in DOMAIN seq_ |-> v[seq[k]]]
            <6>1. Len(s2) = 0
              BY DEF Len
            <6>2. c \in CDomain
              BY DEF TypeOK  
            <6>3. c.sigma \in Seqs(PosInts)
              BY <6>2 DEF CDomain
            <6>4. Len(c.sigma) \in Nat
              BY <6>3 DEF Seqs, Len
            <6>5. Concat(c.sigma, s2) = [k \in 1..(Len(c.sigma)) |-> c.sigma[k]]
              BY <6>1, <6>4 DEF Concat
            <6>6. DOMAIN c.sigma = 1..Len(c.sigma)
              BY <5>7 DEF TypeOK, CDomain, Seqs, Len
            <6>7. [k \in DOMAIN c.sigma |-> c.sigma[k]] = c.sigma
              BY DEF TypeOK, CDomain, Seqs
            <6>8. [k \in 1..Len(c.sigma) |-> c.sigma[k]] = c.sigma
              BY <6>6, <6>7
            <6> QED
              BY <6>5, <6>8
          <5>11. c \in M'
            BY <5>8, <5>9, <5>10
          <5>12. GoodRes(A, c.fres)'
            BY <5>7 DEF GoodRes
          <5>13. ValuesMatchInds(seq, c.sigma) = ValuesMatchInds(seq, c.sigma)'
            <6> DEFINE vals_1 == [k \in DOMAIN seq |-> CASE Q[seq[k]] # BOT  -> Q[seq[k]]
                                                         [] OTHER            -> v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[k]]]
            <6> DEFINE vals_2 == [k \in DOMAIN seq |-> CASE Q'[seq[k]] # BOT -> Q'[seq[k]]
                                                         [] OTHER            -> v'[CHOOSE r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[k]]]
            <6>1. vals_1 = vals_2
              <7> SUFFICES ASSUME NEW k \in DOMAIN seq
                           PROVE vals_1[k] = vals_2[k]
                BY Zenon
              <7>1. CASE Q[seq[k]] # BOT
                BY <7>1
              <7>2. CASE Q[seq[k]] = BOT
                BY <7>2 DEF GoodEnqSet, Perm, Inv_E2, TypeOK
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY Zenon, <5>7, <6>1 DEF ValuesMatchInds
          <5> QED
            BY Zenon, <5>7, <5>11, <5>12, <5>13
        <4>3. CASE i'[p] \in A
          <5> USE <4>3
          <5>1. IsFiniteSet(1..X)
            BY FS_Interval DEF TypeOK
          <5>2. IsFiniteSet(A)
            BY Isa, <5>1, FS_Subset DEF TypeOK
          <5>3. DOMAIN seq = 1..Cardinality(A)
            BY DEF Perm
          <5>4. PICK k \in 1..Cardinality(A) : seq[k] = i'[p]
            BY Zenon, <5>3 DEF Perm
          <5>5. \A z \in k..Cardinality(A) : Q[seq[z]] = BOT
            <6>1. Q[i'[p]] = BOT
              BY DEF TypeOK, Inv_Q
            <6> SUFFICES ASSUME \E z \in (k+1)..Cardinality(A) : Q[seq[z]] # BOT
                         PROVE  FALSE
              BY <5>4, <6>1
            <6>2. PICK z \in (k+1)..Cardinality(A) : Q[seq[z]] # BOT
              OBVIOUS
            <6>3. k < z
              OBVIOUS
            <6>4. seq[z] < seq[k]
              <7>1. seq \in Perm(A) /\ A \in SUBSET 1..X
                BY DEF TypeOK
              <7>2. seq[z] \in A
                BY DEF Perm
              <7>3. \A b \in A : b <= X
                BY <7>1
              <7>4. seq[z] <= X
                BY <7>2, <7>3, Isa
              <7>5. k # z
                BY <6>2
              <7>6. k \in DOMAIN seq /\ z \in DOMAIN seq
                BY <5>3, <5>4, <7>2
              <7>7. \A y, q \in DOMAIN seq : y # q => seq[y] # seq[q]
                BY PermDistinct, <5>2
              <7>8. seq[k] # seq[z]
                BY <7>6, <7>7, <5>2
              <7>11. X = seq[k]
                BY <5>4 DEF TypeOK
              <7> QED
                BY <7>4, <7>8, <7>11, Isa
            <6>5. Q'[seq[z]] # BOT
              BY <6>2
            <6>6. Cardinality(A) = Len(seq)
              BY <5>2, PermLength
            <6>7. PICK q \in ProcSet : pc'[q] = "D3" /\ seq[k] < l'[q] /\ seq[z] < j'[q]
              BY <5>4, <6>2, <6>3, <6>4, <6>5, <6>6 DEF JInvSeq
            <6>8. l'[q] <= X
              BY <2>5, <6>7 DEF Inv_D3
            <6>9. seq[k] < X
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
            <6> SUFFICES ASSUME NEW m \in 1..(X-1)
                         PROVE  /\ Q[m] # BOT => m \in A_
                                /\ (m \in A_ /\ Q[m] = BOT) => \E q \in ProcSet : (pc[q] = "E2" /\ i[q] = m)
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
              <7>5. PICK q \in ProcSet : (pc'[q] = "E2" /\ i'[q] = m)
                BY <7>4 DEF GoodEnqSet, TypeOK
              <7>6. p # q => pc[q] = "E2" /\ i[q] = m
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
                         PROVE  \E q \in ProcSet : (pc[q] = "D3" /\ seq_[n] < l[q] /\ seq_[m] < j[q])
              BY DEF JInvSeq
            <6>1. \A a, b \in 1..Len(seq) : (b < a /\ seq[b] > seq[a] /\ Q'[seq[a]] # BOT)
                                               => (\E r \in ProcSet : (pc'[r] = "D3" /\ seq[b] < l'[r] /\ seq[a] < j'[r]))
              BY DEF JInvSeq
            <6>2. Len(seq) \in Nat /\ Len(seq_) \in Nat /\ Len(seq_) <= Len(seq)
              BY <5>2, <5>3, FS_CardinalityType DEF Len
            <6>3. \A y \in 1..Len(seq_) : y \in 1..Len(seq)
              BY <5>2, <5>4, <6>2, FS_CardinalityType, PermLength DEF Len
            <6>4. \A y \in 1..Len(seq_) : seq_[y] = seq[y]
              BY <6>3 DEF Len
            <6>5. seq[n] > seq[m] /\ Q'[seq[m]] # BOT
              BY DEF Len
            <6>6. PICK r \in ProcSet : (pc[r] = "D3" /\ seq[n] < l[r] /\ seq[m] < j[r])
              BY <6>1, <6>3, <6>5 DEF TypeOK
            <6> QED
              BY <6>3, <6>6, <6>4 DEF Len
          <5>9. A_ \in SUBSET 1..(X-1)
            <6> SUFFICES ASSUME NEW n \in A_
                         PROVE n \in 1..(X-1)
              OBVIOUS         
            <6>1. PICK kn \in 1..(k-1) : seq[kn] = n
              OBVIOUS
            <6>2. \A y \in 1..k-1 : y \in 1..Cardinality(A)
              BY <5>2, <5>4, FS_CardinalityType
            <6>3. kn \in 1..Cardinality(A)
              BY <6>1, <6>2, Isa DEF Perm
            <6>4. n \in A
              BY <6>1, <6>2, <6>3 DEF Perm
            <6>5. A \in SUBSET 1..X
              BY DEF TypeOK
            <6>6. n \in 1..X
              BY <6>4, <6>5
            <6>7. n # X => n \in 1..(X-1)
              BY <6>4, <6>5, <6>6 DEF TypeOK
            <6> SUFFICES ASSUME n = X
                         PROVE  FALSE
              BY <6>7
            <6>8. seq[kn] = X
              BY <6>1
            <6>9. seq[k] = X
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
          <5>10. PICK c \in M : ValuesMatchInds(seq_, c.sigma) /\ GoodRes(A_, c.fres)
            BY Zenon, <5>6, <5>7, <5>8, <5>9 DEF Inv_Main
          
          \* Set of indices to be linearized.
          <5> DEFINE Sk == {seq[z] : z \in k..Cardinality(A)} 
          
          \* Sequence of indices in the order they are to be linearized.
          <5> DEFINE seqk == [z \in 1..(Cardinality(A)-(k-1)) |-> seq[z+(k-1)]]
          
          \* Note that for every index appearing in seqk, corresponding process must exist and is unique.
          <5>11. \A z \in DOMAIN seqk : 
                    \E r \in ProcSet : /\ pc'[r] = "E2" 
                                       /\ i'[r] = seqk[z]
                                       /\ \A r_ \in ProcSet : ((pc'[r_] = pc'[r] /\ i'[r_] = i'[r]) => r = r_)
            <6> SUFFICES ASSUME NEW z \in DOMAIN seqk
                         PROVE  \E r \in ProcSet : /\ pc'[r] = "E2" 
                                                   /\ i'[r] = seqk[z]
                                                   /\ \A r_ \in ProcSet : ((pc'[r_] = pc'[r] /\ i'[r_] = i'[r]) => r = r_)
              OBVIOUS
            <6>1. z+(k-1) \in k..Cardinality(A)
              BY <5>2, <5>4, FS_CardinalityType
            <6>2. Q[seq[z+(k-1)]] = BOT
              BY <5>5, <6>1
            <6>3. seq[z+(k-1)] \in A
              BY <6>1 DEF Perm
            <6>4. PICK r \in ProcSet : pc'[r] = "E2" /\ i'[r] = seq[z+(k-1)]
              BY <6>2, <6>3, Isa DEF GoodEnqSet
            <6> QED
              BY <2>2, <6>4 DEF Inv_E2
          
          <5>12. \A q \in ProcSet : pc'[q] = "E2" <=> (q = p \/ pc[q] = "E2")
            BY DEF TypeOK
          
          <5>13. \A q \in ProcSet : pc'[q] = "E2" <=> (q = p /\ i'[q] = X) \/ (pc[q] = "E2" /\ i'[q] = i[q])
            BY DEF TypeOK
            
          \* Sequence of "corresponding" processes in the order they are to be linearized.
          <5> DEFINE seqp == [z \in 1..(Cardinality(A)-(k-1)) |-> CHOOSE r \in ProcSet : ((r = p /\ X = seqk[z]) \/ (pc[r] = "E2" /\ i[r] = seqk[z]))]
  
          \* The set of processes in the aforementioned sequence.
          <5> DEFINE Sp == {seqp[z] : z \in DOMAIN seqp}
  
          \* The sequence of to-be-written values in the order they are to be linearized.
          <5> DEFINE vseqp == [z \in DOMAIN seqp |-> v[seqp[z]]]
          
          \* The linearized configuration : append to c.sigma, and acknowledge processes in Sp.
          <5> DEFINE d == [sigma |-> Concat(c.sigma, vseqp),   
                           fres |-> [q \in ProcSet |-> IF q \in Sp THEN ACK ELSE c.fres[q]]]
            
          \* Some ad hoc tricks to facilitate proof.
          <5> DEFINE P(w) == /\ CFTypeOK(w)'
                             /\ \E y \in M : \E B \in SUBSET UnlinearizedEnqs(y)' : \E pi \in Perm(B) : 
                                    /\ w.sigma = Concat(y.sigma, [m \in DOMAIN pi |-> v[pi[m]]])
                                    /\ \A q \in ProcSet : IF q \in B THEN w.fres[q] = ACK ELSE w.fres[q] = y.fres[q]
          
          <5>14. M'  = {w \in CDomain : P(w)}
            OBVIOUS
          
          <5> HIDE <3>9 DEF P
          <5>15. d \in M' <=> (d \in CDomain /\ P(d))
            BY <5>14
                       
          <5>16. d \in M' <=> (/\ d \in CDomain 
                               /\ CFTypeOK(d)'
                               /\ \E y \in M : (\E B \in SUBSET UnlinearizedEnqs(y)' : (\E pi \in Perm(B) : 
                                    (/\ d.sigma = Concat(y.sigma, [m \in DOMAIN pi |-> v[pi[m]]])
                                     /\ \A q \in ProcSet : IF q \in B THEN d.fres[q] = ACK ELSE d.fres[q] = y.fres[q]))))
            BY Zenon, <5>15 DEF P
            
          <5>17. d \in CDomain
            <6>1. d.fres \in [ProcSet -> PosInts \union {ACK, BOT}]
              BY DEF TypeOK, CFTypeOK
            <6> SUFFICES ASSUME TRUE
                         PROVE  d.sigma \in Seqs(PosInts)
              BY <6>1 DEF CDomain
            <6>2. d.sigma = [z \in 1..(Len(c.sigma)+Len(vseqp)) |-> IF z \leq Len(c.sigma) THEN c.sigma[z] ELSE vseqp[z-Len(c.sigma)]]
              BY Zenon DEF Concat
            <6>3. \E n \in Nat : DOMAIN c.sigma = 1..n
              BY DEF TypeOK, CDomain, Seqs, Len
            <6>4. Len(c.sigma) \in Nat
              BY <5>10, <6>3 DEF Len
            <6>5. DOMAIN vseqp = 1..Cardinality(A)-(k-1)
              BY FS_CardinalityType
            <6>6. Cardinality(A)-(k-1) \in Nat
              BY <5>2, <5>4, FS_CardinalityType
            <6>7. Len(vseqp) \in Nat
              BY <6>6, <6>5 DEF Len
            <6>8. Len(c.sigma) + Len(vseqp) \in Nat
              BY <6>4, <6>7
            <6>9. \A z \in DOMAIN vseqp : vseqp[z] \in PosInts
              <7> SUFFICES ASSUME NEW z \in DOMAIN vseqp
                           PROVE  vseqp[z] \in PosInts
                BY Zenon
              <7>1. vseqp[z] = v[seqp[z]]
                OBVIOUS
              <7>2. PICK r \in ProcSet : r = seqp[z]
                OBVIOUS
              <7>3. v[r] \in PosInts
                BY DEF TypeOK
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>10. \A z \in 1..Len(c.sigma) : c.sigma[z] \in PosInts
              BY <5>10 DEF TypeOK, CDomain, Seqs, Len
            <6>11. \A z \in DOMAIN d.sigma : d.sigma[z] \in PosInts
              <7> SUFFICES ASSUME NEW z \in DOMAIN d.sigma
                           PROVE  d.sigma[z] \in PosInts
                OBVIOUS
              <7>1. d.sigma[z] = IF z <= Len(c.sigma) THEN c.sigma[z] ELSE vseqp[z-Len(c.sigma)]
                BY Zenon, <6>2
              <7>2. z \in 1..(Len(c.sigma)+Len(vseqp))
                BY Zenon, <6>2
              <7>3. z \in Nat
                BY <6>8, <7>2
              <7> USE <7>3
              <7>4. CASE z <= Len(c.sigma)
                <8> USE <7>4
                <8>1. d.sigma[z] = c.sigma[z]
                  BY <7>1
                <8>2. (1 <= z /\ z <= Len(c.sigma)) => z \in 1..Len(c.sigma)
                  BY <6>2, <6>4
                <8>3. 1 <= z /\ z <= Len(c.sigma)
                  BY <7>2
                <8>4. z \in 1..Len(c.sigma)
                  BY <8>3
                <8>5. c.sigma[z] \in PosInts
                  BY <6>10, <7>1, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7>5. CASE z > Len(c.sigma)
                <8> USE <7>5
                <8>1. d.sigma[z] = vseqp[z-Len(c.sigma)]
                  BY <7>1, <7>3, <6>4
                <8>2. z-Len(c.sigma) \in DOMAIN vseqp => vseqp[z-Len(c.sigma)] = v[seqp[z-Len(c.sigma)]]
                  BY Zenon
                <8>3. DOMAIN vseqp = DOMAIN seqp
                  OBVIOUS
                <8>4. \A q, m, n \in Nat : (m \in 1..q /\ n \in 0..q /\ m > n) => m \in (n+1)..q
                  OBVIOUS
                <8>5. Len(c.sigma) \in 0..(Len(c.sigma)+Len(vseqp)) => z \in (Len(c.sigma)+1)..(Len(c.sigma)+Len(vseqp))
                  BY <6>2, <6>4, <6>7, <6>8, <8>4, Zenon
                <8> HIDE DEF vseqp
                <8>6. Len(c.sigma) \in 0..(Len(c.sigma)+Len(vseqp))
                  BY <6>4, <6>7, <6>8
                <8>7. z \in (Len(c.sigma)+1)..(Len(c.sigma)+Len(vseqp))
                  BY <8>5, <8>6
                <8>8. z-Len(c.sigma) \in 1..Len(vseqp)
                  BY <6>4, <6>7, <8>7
                <8>9. DOMAIN vseqp = 1..Len(vseqp)
                  BY <5>2, <6>5, FS_CardinalityType DEF Len
                <8>10. vseqp[z-Len(c.sigma)] = v[seqp[z-Len(c.sigma)]]
                  BY <8>2, <8>8, <8>9
                <8>11. seqp[z-Len(c.sigma)] \in ProcSet => v[seqp[z-Len(c.sigma)]] \in PosInts
                  BY DEF TypeOK, Zenon
                <8>12. \A n \in DOMAIN seqp : seqp[n] \in ProcSet
                  <9> SUFFICES ASSUME NEW n \in DOMAIN seqp
                               PROVE  seqp[n] \in ProcSet
                    OBVIOUS
                  <9>1. PICK r \in ProcSet : r = seqp[n]
                    OBVIOUS
                  <9> QED
                    BY Zenon, <9>1
                <8>13. seqp[z-Len(c.sigma)] \in ProcSet
                  BY Zenon, <8>12, <8>8, <8>9, <8>3
                <8>14. v[seqp[z-Len(c.sigma)]] \in PosInts
                  BY <8>11, <8>13
                <8> QED
                  BY <8>1, <8>10, <8>14
              <7> QED
                BY <6>4, <7>4, <7>5
            <6>12. DOMAIN d.sigma = 1..(Len(c.sigma)+Len(vseqp))
              BY <6>2, Zenon
            <6>13. d.sigma \in [1..(Len(c.sigma)+Len(vseqp)) -> PosInts]
              BY <6>2, <6>11, <6>12, Zenon
            <6> QED
              BY <6>8, <6>13, Zenon DEF Seqs
          
          <5>18. seqp = seqp'
            <6> SUFFICES ASSUME NEW z \in DOMAIN seqp
                         PROVE seqp[z] = seqp'[z]
              OBVIOUS
            <6>1. pc'[p] = "E2" /\ i'[p] = X
              BY <3>9 DEF TypeOK
            <6>2. \A r \in ProcSet : (pc[r] = "E2" /\ i[r] = seqk[z]) => (pc'[r] = "E2" /\ i'[r] = seqk[z])
              BY <3>9 DEF TypeOK
            <6>3. \A r \in ProcSet : (pc'[r] = "E2" /\ i'[r] = seqk[z]) => (r = p /\ X = seqk[z]) \/ (pc[r] = "E2" /\ i[r] = seqk[z])
              BY <3>9 DEF TypeOK
            <6>4. X+1 # seqk[z]
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
              <7>7. X+1 \notin A
                BY <3>9 DEF TypeOK
              <7> QED
                BY <7>6, <7>7
            <6> QED
              BY <3>9, <6>1, <6>2, <6>3, <6>4 DEF TypeOK
          
          <5>19. d = d'
            <6>1. v = v'
              BY <3>9
            <6>2. seqp = seqp'
              BY <5>18
            <6> HIDE DEF seqp
            <6>3. d.sigma = d.sigma'
              BY Zenon, <6>1, <6>2 
            <6>4. d.fres = d.fres'
              BY <6>2
            <6> QED
              BY <6>3, <6>4
          
          <5>20. \A q \in Sp : /\ q \in ProcSet 
                               /\ (\E z \in DOMAIN seqp : (q = p /\ X = seqk[z]) \/ (pc[q] = "E2" /\ i[q] = seqk[z]))
            <6> SUFFICES ASSUME NEW q \in Sp
                         PROVE  /\ q \in ProcSet 
                                /\ \E z \in DOMAIN seqp : (q = p /\ X = seqk[z]) \/ (pc[q] = "E2" /\ i[q] = seqk[z])
              OBVIOUS
            <6>1. PICK z \in DOMAIN seqp : q = seqp[z]
              OBVIOUS
            <6>2. seqk[1] = X
              BY <4>1, <5>2, <5>4, FS_CardinalityType
            <6>3. seq[k] = X
              BY <5>2, <5>4, <6>2, FS_CardinalityType
            <6>4. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
              BY <5>2, PermDistinct
            <6>5. \A n \in DOMAIN seq : n # k => seq[n] # X
              BY <6>4, <5>2, <5>3, <6>3
            <6>6. \A n \in DOMAIN seqk : n # 1 => seqk[n] # X
              BY <6>5, <5>2, <5>3, <5>4, FS_CardinalityType
            <6>7. CASE z # 1
              <7> USE <6>7
              <7>1. seqp[z] = CHOOSE r \in ProcSet : (pc[r] = "E2" /\ i[r] = seqk[z])
                BY <6>1, <6>6
              <7>2. PICK r \in ProcSet : (pc'[r] = "E2" /\ i'[r] = seqk[z])
                BY <5>11
              <7>3. (r = p /\ i'[r] = X) \/ (pc[r] = "E2" /\ i'[r] = seqk[z])
                BY <7>2, <5>13
              <7>4. pc[r] = "E2" /\ i'[r] = seqk[z]
                BY <6>6, <7>2, <7>3
              <7>5. pc[q] = "E2" /\ i[q] = seqk[z]
                BY <3>9, <6>1, <7>1, <7>4 DEF TypeOK
              <7>6. \A n \in DOMAIN seqp : seqp[n] \in ProcSet
                <8> SUFFICES ASSUME NEW n \in DOMAIN seqp
                             PROVE  seqp[n] \in ProcSet
                  OBVIOUS
                <8>1. PICK f \in ProcSet : f = seqp[n]
                  OBVIOUS
                <8> QED
                  BY <8>1, Zenon
              <7> QED
                BY <6>1, <7>5, <7>6
            <6>8. CASE z = 1
              <7> USE <6>8
              <7>1. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ X = seqk[z])
                BY <6>1, <6>6
              <7>2. PICK r \in ProcSet : (pc'[r] = "E2" /\ i'[r] = seqk[z])
                BY <5>11
              <7>3. (r = p /\ i'[r] = X) \/ (pc[r] = "E2" /\ i'[r] = seqk[z])
                BY <7>2, <5>13
              <7>4. \A r_ \in ProcSet : pc[r_] = "E2" => i'[r_] < X
                BY <3>9 DEF TypeOK, Inv_E2
              <7>5. r = p /\ X = seqk[z]
                BY <7>2, <7>3, <7>4, <6>2 DEF TypeOK
              <7>6. seqp[z] = r
                BY <7>1, <7>2, <7>5
              <7> QED
                BY <6>1, <7>5, <7>6
            <6> QED
              BY <6>7, <6>8
              
          <5>21. CFTypeOK(d)'
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  /\ pc'[q] \in {"L0", "E1", "D1", "D2", "D3"}  => d.fres[q] = BOT
                                /\ pc'[q] \in {"E2", "E3"}                    => d.fres[q] \in {ACK, BOT}
                                /\ pc'[q] = "D4"                              => d.fres[q] \in PosInts \union {BOT}
              BY <5>19, Zenon DEF CFTypeOK
            <6>1. CASE pc'[q] \in {"L0", "E1", "D1", "D2", "D3"}
              <7> USE <6>1
              <7>1. q \notin Sp
                <8> SUFFICES ASSUME q \in Sp
                             PROVE  FALSE
                  OBVIOUS
                <8>1. PICK z \in DOMAIN seqp : pc[q] = "E2" /\ i[q] = seqk[z]
                  BY <3>9, <5>20 DEF TypeOK
                <8>2. CASE z # 1
                  BY <3>9, <8>1, <8>2
                <8>3. CASE z = 1
                  BY <3>9, <8>1, <8>3
                <8> QED
                  BY <8>2, <8>3
              <7>2. c.fres[q] = BOT
                BY <3>9 DEF TypeOK, CFTypeOK
              <7> QED
                BY <7>1, <7>2
            <6>2. CASE pc'[q] = "E2"
              <7> USE <6>2
              <7>1. CASE q \in Sp
                BY <7>1
              <7>2. CASE q \notin Sp
                BY <3>9, <7>2 DEF TypeOK, CFTypeOK
              <7> QED
                BY <7>1, <7>2
            <6>3. CASE pc'[q] = "E3"
              <7> USE <6>3
              <7>1. q \notin Sp
                <8> SUFFICES ASSUME q \in Sp
                             PROVE  FALSE
                  OBVIOUS
                <8>1. PICK z \in DOMAIN seqp : pc[q] = "E2" /\ i[q] = seqk[z]
                  BY <3>9, <5>20 DEF TypeOK
                <8>2. CASE z # 1
                  BY <3>9, <8>1, <8>2
                <8>3. CASE z = 1
                  BY <3>9, <8>1, <8>3
                <8> QED
                  BY <8>2, <8>3
              <7>2. c.fres[q] \in {ACK, BOT}
                BY <3>9 DEF TypeOK, CFTypeOK
              <7> QED
                BY <7>1, <7>2
            <6>4. CASE pc'[q] = "D4"
              <7> USE <6>4
              <7>1. q \notin Sp
                <8> SUFFICES ASSUME q \in Sp
                             PROVE  FALSE
                  OBVIOUS
                <8>1. PICK z \in DOMAIN seqp : pc[q] = "E2" /\ i[q] = seqk[z]
                  BY <3>9, <5>20 DEF TypeOK
                <8>2. CASE z # 1
                  BY <3>9, <8>1, <8>2
                <8>3. CASE z = 1
                  BY <3>9, <8>1, <8>3
                <8> QED
                  BY <8>2, <8>3
              <7>2. c.fres[q] \in PosInts \union {BOT}
                BY <3>9 DEF TypeOK, CFTypeOK
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4, Zenon
          
          <5>22. (\E B \in SUBSET UnlinearizedEnqs(c)' : (\E pi \in Perm(B) : 
                   (/\ d.sigma = Concat(c.sigma, [m \in DOMAIN pi |-> v[pi[m]]])
                    /\ \A q \in ProcSet : IF q \in B THEN d.fres[q] = ACK ELSE d.fres[q] = c.fres[q]))) => d \in M'
            BY <5>10, <5>16, <5>17, <5>21, Zenon
          
          <5>23. Sp \in SUBSET UnlinearizedEnqs(c)'
            <6> SUFFICES ASSUME NEW q \in Sp
                         PROVE  /\ q \in ProcSet
                                /\ pc'[q] = "E2" \/ pc'[q] = "E3"
                                /\ c.fres[q] = BOT
              BY DEF UnlinearizedEnqs
            <6>1. PICK z \in DOMAIN seqp : q = seqp[z]
              OBVIOUS
            <6>2. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ X = seqk[z]) \/ (pc[r] = "E2" /\ i[r] = seqk[z])
              OBVIOUS
            <6>3. seqp[z] = q
              BY <6>1
            <6>4. (q = p /\ X = seqk[z]) \/ (pc[q] = "E2" /\ i[q] = seqk[z])
              BY <5>20 ,<6>1, <6>2, <5>11, <5>13
            <6>5. q \in ProcSet
              BY <5>20
            <6>6. pc'[q] = "E2"
              BY <3>9, <6>4 DEF TypeOK
            <6> SUFFICES ASSUME TRUE
                         PROVE  c.fres[q] = BOT
              BY <6>5, <6>6
            <6>7. q = p \/ pc[q] = "E2"
              BY <6>4
            <6>8. q = p => c.fres[q] = BOT
              BY <3>9, <5>10 DEF GoodRes
            <6>9. (pc[q] = "E2" /\ i[q] \notin A_) => c.fres[q] = BOT
              BY <5>20, <5>10 DEF GoodRes
            <6> SUFFICES ASSUME pc[q] = "E2"
                         PROVE  i[q] \notin A_
              BY <6>7, <6>8, <6>9
            <6>10. i[q] = seq[z+(k-1)]
              BY <3>9, <6>1, <6>4
            <6>11. \A m \in A_ : \E n \in 1..(k-1) : m = seq[n]
              OBVIOUS
            <6>12. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
              BY <5>2, PermDistinct
            <6>13. \A m \in A_ : m # seq[z+(k-1)]
              <7> SUFFICES ASSUME NEW m \in A_,
                                  NEW n \in 1..(k-1),
                                  m = seq[n]
                           PROVE  m # seq[z+(k-1)]
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
                <8>1. seqp[y] = CHOOSE r \in ProcSet : (r = p /\ X = seqk[y]) \/ (pc[r] = "E2" /\ i[r] = seqk[y])
                  OBVIOUS
                <8>2. seqp[z] = CHOOSE r \in ProcSet : (r = p /\ X = seqk[z]) \/ (pc[r] = "E2" /\ i[r] = seqk[z])
                  OBVIOUS
                <8>3. (seqp[y] = p /\ X = seqk[y]) \/ (pc[seqp[y]] = "E2" /\ i[seqp[y]] = seqk[y])
                  BY <8>1, <5>20, <5>11, <5>13
                <8>4. (seqp[z] = p /\ X = seqk[z]) \/ (pc[seqp[z]] = "E2" /\ i[seqp[z]] = seqk[z])
                  BY <8>2, <5>20, <5>11, <5>13
                <8>5. seqp[y] = p => (pc[seqp[y]] # "E2" /\ pc[seqp[z]] # "E2")
                  BY <3>9, Isa DEF TypeOK
                <8>6. (seqp[y] = p /\ X = seqk[y]) <=> (seqp[z] = p /\ X = seqk[z])
                  BY <8>4, <8>5, <5>11, <5>13
                <8>7. seq[k] = X
                  BY <4>1, <5>2, <5>4, FS_CardinalityType
                <8>8. \A n, m \in DOMAIN seq : n # m => seq[n] # seq[m]
                  BY <5>2, PermDistinct
                <8>9. \A n, m \in DOMAIN seq : seq[n] = seq[m] => n = m
                  BY <8>8
                <8>10. \A n \in DOMAIN seq : n # k => seq[n] # X
                  BY <8>8, <5>2, <5>3, <8>7
                <8>11. \A n \in DOMAIN seqk : n # 1 => seqk[n] # X
                  BY <8>10, <5>2, <5>3, <5>4, FS_CardinalityType
                <8>12. CASE seqp[y] = p /\ X = seqk[y]
                  <9> USE <8>12
                  <9>0. seqp[z] = p /\ X = seqk[z]
                    BY <8>6
                  <9> QED
                    BY <8>11, <9>0
                <8>13. CASE pc[seqp[y]] = "E2" /\ i[seqp[y]] = seqk[y]
                  <9> USE <8>13
                  <9>1. seqp[y] # p /\ seqp[z] # p
                    BY <3>9, Isa DEF TypeOK
                  <9>2. (pc[seqp[y]] = "E2" /\ i[seqp[y]] = seqk[y]) /\ (pc[seqp[z]] = "E2" /\ i[seqp[z]] = seqk[z])
                    BY <8>3, <8>4, <9>1
                  <9>3. seqk[y] = seqk[z]
                    BY <9>2, <5>20, Zenon DEF Inv_E2
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
          
          <5>25. (/\ d.sigma = Concat(c.sigma, [m \in DOMAIN seqp |-> v[seqp[m]]])
                  /\ \A q \in ProcSet : IF q \in Sp THEN d.fres[q] = ACK ELSE d.fres[q] = c.fres[q]) => d \in M'
            BY <5>22, <5>23, <5>24, Zenon
          
          <5>26. d.sigma = Concat(c.sigma, [m \in DOMAIN seqp |-> v[seqp[m]]])
            OBVIOUS
          
          <5>27. \A q \in ProcSet : IF q \in Sp THEN d.fres[q] = ACK ELSE d.fres[q] = c.fres[q]
            OBVIOUS
          
          <5>28. d \in M'
            BY Zenon, <5>25, <5>26, <5>27
          
          <5> HIDE DEF d
          <5>30. ValuesMatchInds(seq, d.sigma)' = (d.sigma = [m \in DOMAIN seq |-> CASE Q[seq[m]] # BOT -> Q[seq[m]]
                                                                                     [] OTHER           -> v[CHOOSE q \in ProcSet : (pc'[q] = "E2" /\ i'[q] = seq[m])]])
             BY <3>9, <5>19 DEF ValuesMatchInds
          
          <5>31. ValuesMatchInds(seq, d.sigma)'
            <6> DEFINE vals == [m \in DOMAIN seq |-> CASE Q[seq[m]] # BOT -> Q[seq[m]]
                                                       [] OTHER           -> v[CHOOSE q \in ProcSet : (pc'[q] = "E2"  /\ i'[q] = seq[m])]]
            <6>1. d.sigma \in [DOMAIN seq -> PosInts]
              <7>1. d.sigma = [z \in 1..(Len(c.sigma)+Len(vseqp)) |-> IF z \leq Len(c.sigma) THEN c.sigma[z] ELSE vseqp[z-Len(c.sigma)]]
                BY Zenon DEF Concat, d
              <7>2. Len(c.sigma)+Len(vseqp) = Cardinality(A)
                <8>1. Len(c.sigma) = k-1
                  BY <5>10 DEF ValuesMatchInds, Len
                <8>2. Len(vseqp) = Cardinality(A)-(k-1)
                  BY <5>2, FS_CardinalityType DEF Len
                <8> QED
                  BY <8>1, <8>2, <5>2, FS_CardinalityType
              <7>3. DOMAIN d.sigma = 1..Cardinality(A)
                BY <7>1, <7>2, Zenon
              <7>4. \E n \in Nat : d.sigma \in [1..n -> PosInts]
                BY <5>17 DEF CDomain, Seqs
              <7>5. d.sigma \in [1..Cardinality(A) -> PosInts]
                BY <7>3, <7>4, <5>2, FS_CardinalityType
              <7> QED
                BY <5>3, <7>5 
            <6>2. vals \in [DOMAIN seq -> PosInts]
              <7>1. DOMAIN vals = DOMAIN seq
                OBVIOUS
              <7>2. \A m \in DOMAIN vals : vals[m] \in PosInts
                <8> SUFFICES ASSUME NEW m \in DOMAIN vals 
                             PROVE  vals[m] \in PosInts
                  BY Zenon
                <8>1. CASE Q[seq[m]] # BOT
                  BY <8>1 DEF Perm, TypeOK
                <8>2. CASE Q[seq[m]] = BOT
                  <9> USE <8>2
                  <9>1. vals[m] = v[CHOOSE q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m]]
                    OBVIOUS
                  <9>2. \E q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m]
                    <10>1. CASE m < k
                      <11>1. seq[m] \in A_
                        BY <10>1, <5>3
                      <11>2. PICK q \in ProcSet : pc[q] = "E2" /\ i[q] = seq[m]
                        BY <11>1, <5>7, <5>9 DEF GoodEnqSet
                      <11> QED
                        BY <3>9, <11>2 DEF TypeOK
                    <10>2. CASE m >= k
                      <11>1. m \in k..Cardinality(A)
                        BY <10>2, <5>3, FS_CardinalityType
                      <11>2. m-(k-1) \in 1..Cardinality(A)-(k-1)
                        BY <11>1, <5>2, <5>3, <5>4, FS_CardinalityType
                      <11>3. PICK q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seqk[m-(k-1)]
                        BY <11>2, <5>11
                      <11>4. seqk[m-(k-1)] = seq[m]
                        BY <11>1, <5>2, <5>3, <5>4, FS_CardinalityType
                      <11> QED
                        BY <11>3, <11>4
                    <10> QED
                      BY <10>1, <10>2, <5>3
                  <9>3. PICK q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m] /\ vals[m] = v[q]
                    BY <9>1, <9>2, Zenon
                  <9> QED
                    BY <9>3 DEF TypeOK
                <8> QED
                  BY <8>1, <8>2
              <7> QED
                BY <7>1, <7>2
            <6>3. \A m \in DOMAIN seq : d.sigma[m] = vals[m]
              <7> SUFFICES ASSUME NEW m \in DOMAIN seq
                           PROVE  d.sigma[m] = vals[m]
                OBVIOUS
              <7>1. Len(c.sigma) = k-1
                BY <5>10 DEF ValuesMatchInds, Len
              <7>2. d.sigma = [z \in 1..(Len(c.sigma)+Len(vseqp)) |-> IF z \leq Len(c.sigma) THEN c.sigma[z] ELSE vseqp[z-Len(c.sigma)]]
                BY Zenon, <5>25 DEF Concat, d
              <7>3. \E n \in Nat : DOMAIN c.sigma = 1..n
                BY DEF TypeOK, CDomain, Seqs, Len
              <7>4. DOMAIN vseqp = 1..Cardinality(A)-(k-1)
                BY FS_CardinalityType
              <7>5. Cardinality(A)-(k-1) \in Nat
                BY <5>2, <5>4, FS_CardinalityType
              <7>6. Len(vseqp) \in Nat
                BY <7>4, <7>5 DEF Len
              <7>7. Len(c.sigma) \in Nat
                BY <5>10, <7>3 DEF Len
              <7>8. m < k => d.sigma[m] = c.sigma[m]
                BY <7>1, <5>2, <5>3, <5>4, <7>6, <7>7, FS_CardinalityType DEF Concat, d
              <7>9. d.sigma = [z \in 1..(Len(c.sigma)+Len(vseqp)) |-> IF z \leq Len(c.sigma) THEN c.sigma[z] ELSE vseqp[z-Len(c.sigma)]]
                BY Zenon DEF Concat, d
              <7>10. (~(m \leq Len(c.sigma))) => d.sigma[m] = vseqp[m-Len(c.sigma)]
                BY <6>1, <7>9, Zenon
              <7>11. (m \in Nat /\ k \in Nat) => (m > k-1 => d.sigma[m] = vseqp[m-(k-1)])
                BY <7>10, <7>7, <7>1
              <7>12. m >= k => d.sigma[m] = vseqp[m-(k-1)]
                BY <7>11 DEF Perm
              <7>13. m >= k => d.sigma[m] = v[seqp[m-(k-1)]]
                BY <7>12, <5>2, <5>3, <5>4, FS_CardinalityType DEF Perm
              <7>14. CASE m < k
                <8> SUFFICES ASSUME m < k, d.sigma[m] = c.sigma[m]
                             PROVE  c.sigma[m] = vals[m]
                  BY Zenon, <7>8, <7>14
                <8>1. CASE Q[seq[m]] # BOT
                  <9>1. vals[m] = Q[seq[m]]
                    BY <8>1
                  <9>2. m \in DOMAIN seq_ => c.sigma[m] = Q[seq[m]]
                    BY Zenon, <5>10, <8>1 DEF ValuesMatchInds
                  <9>3. m \in 1..Cardinality(A)
                    BY Zenon, <5>3, <8>1
                  <9>4. m \in 1..k-1
                    BY <9>3, <5>2
                  <9>5. m \in DOMAIN seq_
                    BY Zenon, <9>4
                  <9> QED
                    BY <9>1, <9>2, <9>5
                <8>2. CASE Q[seq[m]] = BOT
                  <9> USE <8>2
                  <9>1. vals[m] = v[CHOOSE q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m]]
                    OBVIOUS
                  <9>2. \E q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m]
                    <10>1. seq[m] \in A_
                      BY <5>3 DEF Perm
                    <10>2. PICK q \in ProcSet : pc[q] = "E2" /\ i[q] = seq[m]
                      BY Zenon, <10>1, <5>7, <5>9 DEF GoodEnqSet
                    <10> QED
                      BY Zenon, <3>9, <10>2 DEF TypeOK
                  <9>3. PICK q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m] /\ vals[m] = v[q]
                    BY <9>1, <9>2, Zenon
                  <9>4. m \in 1..Cardinality(A)
                    BY Zenon, <5>3, <8>1
                  <9>5. m \in 1..k-1
                    BY <9>4, <5>2
                  <9>6. m \in DOMAIN seq_
                    BY Zenon, <9>5
                  <9>7. c.sigma[m] = v[CHOOSE r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[m]]
                    BY Isa, <5>10, <9>6, <5>3 DEF ValuesMatchInds
                  <9>8. \E r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[m]
                    <10>1. seq[m] \in A_
                      BY <5>3 DEF Perm
                    <10>2. QED
                      BY <10>1, <5>7, <5>9 DEF GoodEnqSet
                  <9>9. PICK r \in ProcSet : pc[r] = "E2" /\ i[r] = seq[m] /\ c.sigma[m] = v[r]
                    BY <9>7, <9>8, Zenon
                  <9>10. \A n, y \in DOMAIN seq : n # y => seq[n] # seq[y]
                    BY <5>2, PermDistinct
                  <9>11. seq[k] = i'[p]
                    BY <5>4
                  <9>12. i'[p] # i'[q]
                    BY <9>10, <9>11, <5>2, <5>3, <9>3 DEF Perm
                  <9>13. p # q /\ p # r
                    BY Zenon, <9>12, <9>9, <3>9 DEF TypeOK
                  <9>14. i'[q] = i[q]
                    BY Zenon, <9>13, <3>9 DEF TypeOK
                  <9>15. pc[q] = "E2"
                    BY Zenon, <3>9, <9>3, <9>13 DEF TypeOK
                  <9>16. q = r
                    BY <3>9, <9>15, <9>9, <9>3, <9>14 DEF Inv_E2
                  <9> QED
                    BY <9>3, <9>9, <9>16
                <8> QED
                  BY <8>1, <8>2
              <7>15. CASE m >= k
                <8> USE <7>15
                <8> SUFFICES ASSUME m >= k, d.sigma[m] = v[seqp[m-(k-1)]]
                             PROVE  v[seqp[m-(k-1)]] = vals[m]
                  BY Zenon, <7>13, <7>8
                <8>1. Q[seq[m]] = BOT
                  BY <5>5, <5>3 DEF Perm
                <8>2. vals[m] = v[CHOOSE q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m]]
                  BY <8>1
                <8>3. \E q \in ProcSet : (pc'[q] = "E2" /\ i'[q] = seq[m])
                  BY <5>11, <5>2, <5>3, <5>4, FS_CardinalityType DEF Perm
                <8>4. PICK q \in ProcSet : pc'[q] = "E2" /\ i'[q] = seq[m] /\ vals[m] = v[q]
                  BY <8>2, <8>3, Zenon
                <8>5. m-(k-1) \in 1..Cardinality(A)-(k-1)
                  BY <5>2, <5>3, <5>4, FS_CardinalityType DEF Perm
                <8>6. seqk[m-(k-1)] = seq[m]
                  BY <5>2, <5>3, <5>4, <8>5, FS_CardinalityType DEF Perm
                <8>7. v[seqp[m-(k-1)]] = v[CHOOSE r \in ProcSet : ((r = p /\ X = seqk[m-(k-1)]) \/ (pc[r] = "E2" /\ i[r] = seqk[m-(k-1)]))]
                  BY <8>5, <8>6, Zenon
                <8>8. \E r \in ProcSet : (pc'[r] = "E2"  /\ i'[r] = seqk[m-(k-1)])
                  BY <8>5, <5>11
                <8>9. \E r \in ProcSet : (r = p /\ seqk[m-(k-1)] = X) \/ (pc[r] = "E2" /\ i'[r] = seqk[m-(k-1)])
                  BY <8>8, <5>13, Zenon
                <8>10. \A r \in ProcSet : pc[r] = "E2" => i[r] = i'[r]
                  BY Zenon, <3>9 DEF TypeOK
                <8>11. PICK r \in ProcSet : ((r = p /\ seqk[m-(k-1)] = X) \/ (pc[r] = "E2" /\ i[r] = seqk[m-(k-1)])) /\ v[seqp[m-(k-1)]] = v[r]
                  BY <8>7, <8>9, <8>10, Zenon
                <8>12. i'[r] = seq[m]
                  BY Zenon, <3>9, <8>11, <8>6 DEF TypeOK
                <8>13. pc'[q] = "E2"
                  BY <8>4
                <8>14. pc'[r] = "E2"
                  BY <8>11, <3>9 DEF TypeOK
                <8>15. q = r
                  BY <8>13, <8>14, <8>4, <8>12, <2>2 DEF Inv_E2
                <8> QED
                  BY <8>15, <8>4, <8>11
              <7>16. m \in Nat /\ k \in Nat
                BY <5>2, <5>3, FS_CardinalityType
              <7> QED
                BY <7>14, <7>15, <7>16
            <6> QED
              BY <5>30, <6>1, <6>2, <6>3, Zenon
          
          <5>32. GoodRes(A, d.fres)'
            <6> DEFINE GoodProcRes(S, res, q) == res[q] = CASE (pc[q] = "E2" /\ i[q] \in S) -> ACK
                                                            [] pc[q] = "E3"                 -> ACK
                                                            [] pc[q] = "D4"                 -> x[q]
                                                            [] OTHER                        -> BOT
            <6> SUFFICES ASSUME NEW q \in ProcSet'
                         PROVE  GoodProcRes(A, d.fres, q)'
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
                  <9>3. PICK r \in ProcSet : /\ pc'[r] = "E2"
                                             /\ i'[r] = seqk[idx - (k - 1)]
                                             /\ \A r_ \in ProcSet : ((pc'[r_] = pc'[r] /\ i'[r_] = i'[r]) => r = r_)
                    BY <5>11, <9>2
                  <9>4. seqk[idx - (k - 1)] = seq[idx]
                    BY <9>2
                  <9>8. seqp[idx - (k - 1)] = r
                    <10>1. CASE r = p
                      <11> USE <10>1
                      <11>1. seqk[idx - (k - 1)] = X
                        BY <4>1, <9>3
                      <11>2. \A r_ \in ProcSet : pc[r_] = "E2" => i[r_] # X
                        BY DEF Inv_E2, TypeOK
                      <11>3. \A r_ \in ProcSet : pc[r_] = "E2" /\ i[r_] = seqk[idx - (k - 1)] => FALSE
                        BY <11>1, <11>2
                      <11> QED
                        BY <9>2, <11>3, <11>1, Zenon
                    <10>2. CASE r # p
                      <11> USE <10>2
                      <11>1. i'[r] = i[r]
                        BY <3>9
                      <11>2. \A r_ \in ProcSet : r_ # p => /\ pc[r_] = pc'[r_]
                                                            /\ i[r_] = i'[r_]
                        BY <3>9
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
                  <9>2. PICK z \in 1..(Cardinality(A)-(k-1)) : \/ (r = p /\ X = seqk[z]) 
                                                               \/ (pc[r] = "E2" /\ i[r] = seqk[z])
                    BY <9>1, <5>20
                  <9>3. seqk[z] = seq[z + (k - 1)]
                    OBVIOUS
                  <9>4. z + (k - 1) \in (k - 1)..Cardinality(A)
                    BY <5>2, <9>1, FS_CardinalityType
                  <9>5. seqk[z] \in A
                    BY <9>3, <9>4 DEF Perm
                  <9>6. CASE r # p
                    <10> USE <9>6
                    <10>1. i[r] = i'[r]
                      BY <3>9 DEF TypeOK
                    <10> QED
                      BY <9>5, <9>2, <9>1, <10>1
                  <9>7. CASE r = p
                    <10>1. pc[r] # "E2" /\ i'[r] = X
                      BY <9>7, <3>9 DEF TypeOK
                    <10> QED
                      BY <10>1, <9>2, <9>5, <9>1
                  <9> QED
                    BY <9>6, <9>7
                <8> QED
                  BY <8>1, <8>2
              <7> QED
                BY Zenon, <7>1, <7>2 
            <6>2. \A r \in Sp : pc'[r] = "E2"
              <7> SUFFICES ASSUME NEW r \in Sp
                           PROVE  pc'[r] = "E2"
                OBVIOUS
              <7>1. r = p \/ pc[r] = "E2"
                BY <5>20
              <7>2. r = p => pc'[r] = "E2"
                BY <3>9 DEF TypeOK
              <7>3. pc[r] = "E2" => pc'[r] = "E2"
                BY <3>9 DEF TypeOK
              <7> QED 
                BY <7>1, <7>2, <7>3
            <6>3. CASE q \notin Sp
              <7> USE <6>3
              <7>1. GoodProcRes(A_, c.fres, q)
                BY <5>10 DEF GoodRes
              <7>2. d.fres[q] = c.fres[q]
                BY <5>27
              <7>3. q # p
                <8>1. seqk[1] = seq[k]
                  BY <5>2, <5>3, <5>4, FS_CardinalityType
                <8>2. seqk[1] = i'[p]
                  BY <8>1, <5>4
                <8>3. seqk[1] = X
                  BY <8>2, <3>9 DEF TypeOK
                <8>4. seqp[1] = p
                  BY <5>2, FS_CardinalityType, <8>3
                <8>9. p \in Sp
                  BY <5>2, FS_CardinalityType, <8>4
                <8> QED
                  BY <8>9
              <7>4. pc[q] = pc'[q] /\ i[q] = i'[q] /\ x[q] = x'[q]
                BY <7>3, <3>9
              <7>5. GoodProcRes(A, d.fres, q)
                <8>1. GoodProcRes(A_, d.fres, q)
                  BY <7>1, <7>2
                <8>2. i[q] \in A_ => i[q] \in A
                  BY <6>1
                <8>3. pc[q] = "E2" /\ i[q] \in A => i[q] \in A_
                  <9> SUFFICES ASSUME pc[q] = "E2" /\ i[q] \in {i'[r] : r \in Sp} 
                               PROVE  FALSE
                    BY <6>1, Zenon
                  <9>1. PICK r \in Sp : i[q] = i'[r]
                    OBVIOUS
                  <9>2. r = p \/ pc[r] = "E2"
                    BY <5>20
                  <9>3. r = q
                    <10>1. CASE r = p
                      <11> USE <10>1
                      <11>1. i[q] < X
                        BY DEF Inv_E2
                      <11>2. i'[p] = X
                        BY <3>9 DEF TypeOK
                      <11> QED
                        BY <11>1, <11>2, <9>1, Isa
                    <10>2. CASE pc[r] = "E2"
                      <11> USE <10>2
                      <11>1. r # p
                        BY <3>9
                      <11>2. i[r] = i'[r]
                        BY <11>1, <3>9
                      <11> QED
                        BY <9>1, <11>2 DEF Inv_E2
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
              <7>1. d.fres[q] = ACK
                BY <5>27
              <7>2. i'[q] \in A
                BY <6>1
              <7>3. pc'[q] = "E2"
                BY <6>2
              <7> QED
                BY <7>1, <7>2, <7>3, <5>19
            <6> QED
              BY <6>3, <6>4
          
          \* Some ad hoc tricks to hide complex definitions for the pf to go through.
          <5> DEFINE G(w) == ValuesMatchInds(seq, w.sigma)' /\ GoodRes(A, w.fres)'       
          <5>33. (\E w \in M' : ValuesMatchInds(seq, w.sigma)' /\ GoodRes(A, w.fres)') = (\E w \in M' : G(w))
            OBVIOUS
          <5> HIDE <3>2 DEF G, d
          <5>34. d \in M' /\ G(d) => (\E w \in M' : G(w))
            OBVIOUS
          <5>35. G(d)
            BY <5>31, <5>32 DEF G
          <5> QED
            BY <5>28, <5>33, <5>34, <5>35
        <4> QED
          BY Zenon, <4>2, <4>3
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF InvNL
  <1> QED
    BY <1>1, <1>2

\* Proof of full inductive invariant
THEOREM InductiveInvariant == Spec => []Inv
  BY InductiveInvariantNL, LinearizabilityFromInvNL, PTL DEF Inv, InvNL

\* Proof of linearizability
THEOREM Linearizability == Spec => [](M # {})
  BY InductiveInvariant, PTL DEF Inv, Linearizable 

=============================================================================
\* Modification History
\* Last modified Sat Oct 07 13:00:09 EDT 2023 by uguryavuz
\* Created Mon Oct 02 00:09:31 EDT 2023 by uguryavuz
