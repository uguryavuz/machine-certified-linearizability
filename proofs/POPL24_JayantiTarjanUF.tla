----------------------- MODULE POPL24_JayantiTarjanUF -----------------------
(****************************************************************************
Authors: Prasad Jayanti, Siddhartha Jayanti, Uğur Y. Yavuz, Lizzie Hernández Videa
Date: 2023-10-07

This is the TLA+ specification of Jayanti-Tarjan concurrent union-find
algorithm [Jayanti & Tarjan, 2016; Jayanti & Tarjan, 2021] with any-try splitting
(a generalized version of two-try splitting described in the 2021 paper); 
and its proof of linearizability in TLAPS, using the tracking technique as 
described in our work "A Universal, Sound, and Complete Forward Reasoning Technique for
Machine-Verified Proofs of Linearizability", to appear in POPL 2024.
Specficially, it corresponds to the partial tracker described in
the Appendix.

[Jayanti & Tarjan, 2016]
Siddhartha V. Jayanti & Robert E. Tarjan, 2016. 
"A Randomized Concurrent Algorithm for Disjoint Set Union." 
In Proceedings of the 2016 ACM Symposium on Principles of Distributed Computing (PODC '16). 
Association for Computing Machinery, New York, NY, USA, 75–82. https://doi.org/10.1145/2933057.2933108

[Jayanti & Tarjan, 2021] 
Siddhartha V. Jayanti & Robert E. Tarjan, 2021.
"Concurrent disjoint set union."
Distrib. Comput. 34, 413–436 (2021). https://doi.org/10.1007/s00446-020-00388-x

FILE OUTLINE:
    - Lines 89-110: Preliminary definitions
    - Lines 110-372: Specification
    - Lines 372-511: Type-correctness and proof of type-correctness
    - Lines 511-801: Remaining invariants and related lemmas
    - Lines 801-4727: Proof of inductive invariance
    - Lines 4727-4731: Proof of linearizability (immediate from the proof above)
    - Lines 4731-4963: Proof of strong linearizability

TYPE:
    - Find(x) returns the maximum element in element x’s part of the partition.
      Invokable by any process.
    - Union(x, y) merges the parts of the partition containing x and y if they
      are different. Invokable by any process.

CONSTANTS: 
    - N: the number of nodes.

MODEL VALUES:
    - ACK ('ack' in the paper) is a special value that is used to indicate 
      an operation has been completed.
    - BOT (\bot in the paper) is akin to a null value.
    - ProcSet is the set of all processes.

SHARED VARIABLES:
    - Par[1..N] is an array of "parent pointers".

LOCAL VARIABLES:
    - For each process p: x_p, y_p, u_p, v_p, a_p, b_p are local variables.

ALGORITHM:
    - F1: Find(x):
          --------
          u <- x
      F2: a <- Par[u]
          if (u = a) goto F6
      F3: b <- Par[a]
      F4: CAS(Par[u], a, b); goto F2 or F5
      F5: u <- a; goto F2
      F6: return u

    - U1: Union(x, y):
          ------------
          u <- x; v <- y
      U2: if (u = v) goto U11
          else if (u > v): if (v = CAS(Par[u], u, v)): goto U11
          else if (u < v): if (u = CAS(Par[v], v, u)): goto U11
      
      U3: a <- Par[u]; if (u = a) goto U7
      U4: b <- Par[a]
      U5: CAS(Par[u], a, b); goto U3 or U6
      U6: u <- a; goto U3
              
      U7: a <- Par[v]; if (v = a) goto U2
      U8: b <- Par[a]
      U9: CAS(Par[v], a, b); goto U7 or U10
      U10: v <- a; goto U7

      U11: return ACK
            
Note: Each line has at most 1 shared memory instruction.
****************************************************************************)

EXTENDS Integers, FiniteSetTheorems, TLAPS

CONSTANTS ProcSet, N, NIL, ACK
VARIABLES Par, x, y, u, v, a, b, pc, M  \* M is the meta-configuration.
vars == <<Par, x, y, u, v, a, b, pc>>
augs == <<M>>
allvars == <<Par, x, y, u, v, a, b, pc, M>>

\* A few useful definitions.
InvocationLines  == {"F1", "U1"}
Lines            == {"F1", "F2", "F3", "F4", "F5", "F6",
                     "U1", "U2", "U3", "U4", "U5", "U6", "U7", "U8", "U9", "U10", "U11"}
NodeSet == 1..N
PowerSetNodes == SUBSET NodeSet
States      == [NodeSet -> PowerSetNodes]
Rets        == [ProcSet -> NodeSet \cup {NIL} \cup {ACK}]
AtomConfigs == [sigma: States, f: Rets] \* Set of all structures t, with t.State \in States and t.f \in Rets

\* Max operator
Max(S) == CHOOSE X \in S : \A Y \in S : Y <= X

\* SPECIFICATION

\* The initial predicate.
\* Notes:
\*   - The meta-configuration M contains atomic configurations C = (C.sigma, C.f),
\*     where C.f is a triple (op, arg, res). In the TLA+ specification, we use
\*     (sigma, f) = (C.sigma, C.f.res) as the atomic configuration; as op and arg
\*     are uniquely determined by pc, i, and v.
\*   * Alternatively, one can keep these fields in the meta-configuration and
\*     prove an invariant that, for a process p, the value of pc[p] imposes a 
\*     unique value for C.f.op[p], and the value of the variables passed in as 
\*     arguments, does so for C.f.arg[p], for all configurations C in M. Since
\*     this increases proof overhead, we opt for this simplification.
InitVars == /\ Par  = [z \in NodeSet |-> z]
            /\ x  \in [ProcSet -> NodeSet]
            /\ y  \in [ProcSet -> NodeSet]
            /\ u  \in [ProcSet -> NodeSet]
            /\ v  \in [ProcSet -> NodeSet]
            /\ a  \in [ProcSet -> NodeSet]
            /\ b  \in [ProcSet -> NodeSet]
            /\ pc \in [ProcSet -> InvocationLines]
sigmaInit   == [z \in NodeSet |-> {z}]
fInit       == [p \in ProcSet |-> NIL]
InitAug     == M = {[sigma |-> sigmaInit, f |-> fInit]}
Init == InitVars /\ InitAug

\* Line F1 | Find(x): u <- x
LineF1(p) == /\ pc[p] = "F1"
             /\ \E xnew \in NodeSet: 
                    /\ x' = [x EXCEPT ![p] = xnew]
                    /\ u' = [u EXCEPT ![p] = xnew]
             /\ pc' = [pc EXCEPT ![p] = "F2"]
             /\ UNCHANGED <<Par, y, v, a, b>>
\* No updates to the meta-configuration.
AugF1(p) == M' = M
F1(p)    == LineF1(p) /\ AugF1(p)

\* Line F2 | a <- Par[u]; if (u = a) goto F6
LineF2(p) == /\ pc[p] = "F2"
             /\ a' = [a EXCEPT ![p] = Par[u[p]]]
             /\ IF Par[u[p]] = u[p]  \* a'[p]
                   THEN pc' = [pc EXCEPT ![p] = "F6"]
                   ELSE pc' = [pc EXCEPT ![p] = "F3"]
             /\ UNCHANGED <<Par, x, y, u, v, b>>
\* Update the meta-configuration: linearize p if going to F6.
AugF2(p) == IF Par[u[p]] = u[p]
               THEN M' = {t \in AtomConfigs : \E told \in M : /\ told.f[p] = NIL
                                                              /\ t.sigma = told.sigma
                                                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]}
               ELSE M' = M
F2(p) == LineF2(p) /\ AugF2(p)

\* Line F3 | b <- Par[a]
LineF3(p) == /\ pc[p] = "F3"
             /\ b' = [b EXCEPT ![p] = Par[a[p]]]
             /\ pc' = [pc EXCEPT ![p] = "F4"]
             /\ UNCHANGED <<Par, x, y, u, v, a>>
\* No updates to the meta-configuration.
AugF3(p) == M' = M
F3(p)    == LineF3(p) /\ AugF3(p)

\* Line F4 | CAS(Par[u], a, b); goto F2 or F5
LineF4(p) == /\ pc[p] = "F4"
             /\ IF Par[u[p]] = a[p]
                   THEN Par' = [Par EXCEPT ![u[p]] = b[p]]
                   ELSE Par' = Par
             /\ \/ pc' = [pc EXCEPT ![p] = "F5"]
                \/ pc' = [pc EXCEPT ![p] = "F2"]
             /\ UNCHANGED <<x, y, u, v, a, b>>
\* No updates to the meta-configuration.
AugF4(p) == M' = M
F4(p)    == LineF4(p) /\ AugF4(p)

\* Line F5 | u <- a; goto F2
LineF5(p) == /\ pc[p] = "F5"
             /\ u' = [u EXCEPT ![p] = a[p]]
             /\ pc' = [pc EXCEPT ![p] = "F2"]
             /\ UNCHANGED <<Par, x, y, v, a, b>>
\* No updates to the meta-configuration.
AugF5(p) == M' = M
F5(p)    == LineF5(p) /\ AugF5(p)

\* Line F6 | return u
LineF6(p) == /\ pc[p] = "F6"
             /\ \E line \in InvocationLines : pc' = [pc EXCEPT ![p] = line]
             /\ UNCHANGED <<Par, x, y, u, v, a, b>>
\* Update the meta-configuration: filter out configurations that don't match
\* the return value of p's operation, and reset the return value to BOT.
AugF6(p) == M' = {t \in AtomConfigs : \E told \in M : /\ told.f[p] = u[p]
                                                      /\ t.sigma = told.sigma
                                                      /\ t.f = [told.f EXCEPT ![p] = NIL]}
F6(p) == LineF6(p) /\ AugF6(p)

\* Line U1 | Union(x, y): u <- x; v <- y
LineU1(p) == /\ pc[p] = "U1"
             /\ \E xnew \in NodeSet:
                    /\ x' = [x EXCEPT ![p] = xnew]
                    /\ u' = [u EXCEPT ![p] = xnew]
             /\ \E ynew \in NodeSet:
                    /\ y' = [y EXCEPT ![p] = ynew]
                    /\ v' = [v EXCEPT ![p] = ynew]
             /\ pc' = [pc EXCEPT ![p] = "U2"]
             /\ UNCHANGED <<Par, a, b>>
\* No updates to the meta-configuration.
AugU1(p) == M' = M
U1(p)    == LineU1(p) /\ AugU1(p)

\* Line U2 | if (u = v) goto U11; ...
LineU2(p) == /\ pc[p] = "U2"
             /\ CASE u[p] = v[p] -> (/\ pc' = [pc EXCEPT ![p] = "U11"]
                                     /\ UNCHANGED <<Par, x, y, u, v, a, b>>)
                  [] u[p] < v[p] -> (IF Par[u[p]] = u[p]
                                        THEN /\ Par' = [Par EXCEPT ![u[p]] = v[p]]
                                             /\ pc' = [pc EXCEPT ![p] = "U11"]
                                             /\ UNCHANGED <<x, y, u, v, a, b>>
                                        ELSE /\ Par' = Par
                                             /\ pc' = [pc EXCEPT ![p] = "U3"]
                                             /\ UNCHANGED <<x, y, u, v, a, b>>)
                  [] OTHER       -> (IF Par[v[p]] = v[p]
                                        THEN /\ Par' = [Par EXCEPT ![v[p]] = u[p]]
                                             /\ pc' = [pc EXCEPT ![p] = "U11"]
                                             /\ UNCHANGED <<x, y, u, v, a, b>>
                                        ELSE /\ Par' = Par
                                             /\ pc' = [pc EXCEPT ![p] = "U3"]
                                             /\ UNCHANGED <<x, y, u, v, a, b>>)
\* Update the meta-configuration: linearize p if going to U11.
\* This should also update the state; by updating the map from nodes to their parts,
\* to reflect the union of the parts of u and v.
AugU2(p) == IF u[p] = v[p] 
                THEN M' = {t \in AtomConfigs : \E told \in M: /\ told.f[p] = NIL
                                                              /\ t.sigma = told.sigma
                                                              /\ t.f = [told.f EXCEPT ![p] = ACK]
                          }
                ELSE IF (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]) 
                        THEN M' = {t \in AtomConfigs : \E told \in M: /\ told.f[p] = NIL
                                                                      /\ \A z \in NodeSet: 
                                                                         (z \in told.sigma[x[p]] \cup told.sigma[y[p]])
                                                                            => (t.sigma[z] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                                                      /\ \A z \in NodeSet:
                                                                         (z \notin told.sigma[x[p]] \cup told.sigma[y[p]])
                                                                            => (t.sigma[z] = told.sigma[z])
                                                                      /\ t.f = [told.f EXCEPT ![p] = ACK]}
                                  
                        ELSE M' = M
U2(p) == LineU2(p) /\ AugU2(p)

\* Line U3 | a <- Par[u]; if (u = a) goto U7
LineU3(p) == /\ pc[p] = "U3"
             /\ a' = [a EXCEPT ![p] = Par[u[p]]]
             /\ IF Par[u[p]] = u[p]  \* a'[p]
                   THEN pc' = [pc EXCEPT ![p] = "U7"]
                   ELSE pc' = [pc EXCEPT ![p] = "U4"]
             /\ UNCHANGED <<Par, x, y, u, v, b>>
\* No updates to the meta-configuration.
AugU3(p) == M' = M
U3(p)    == LineU3(p) /\ AugU3(p)

\* Line U4 | b <- Par[a]
LineU4(p) == /\ pc[p] = "U4"
             /\ b' = [b EXCEPT ![p] = Par[a[p]]]
             /\ pc' = [pc EXCEPT ![p] = "U5"]
             /\ UNCHANGED <<Par, x, y, u, v, a>>
\* No updates to the meta-configuration.
AugU4(p) == M' = M
U4(p)    == LineU4(p) /\ AugU4(p)

\* Line U5 | CAS(Par[u], a, b); goto U3 or U6
LineU5(p) == /\ pc[p] = "U5"
             /\ IF Par[u[p]] = a[p]
                   THEN Par' = [Par EXCEPT ![u[p]] = b[p]]
                   ELSE Par' = Par
             /\ \/ pc' = [pc EXCEPT ![p] = "U6"]
                \/ pc' = [pc EXCEPT ![p] = "U3"]
             /\ UNCHANGED <<x, y, u, v, a, b>>
\* No updates to the meta-configuration.
AugU5(p) == M' = M
U5(p)    == LineU5(p) /\ AugU5(p)

\* Line U6 | u <- a; goto U3
LineU6(p) == /\ pc[p] = "U6"
             /\ u' = [u EXCEPT ![p] = a[p]]
             /\ pc' = [pc EXCEPT ![p] = "U3"]
             /\ UNCHANGED <<Par, x, y, v, a, b>>
\* No updates to the meta-configuration.
AugU6(p) == M' = M
U6(p)    == LineU6(p) /\ AugU6(p)

\* Line U7 | a <- Par[v]; if (v = a) goto U2
LineU7(p) == /\ pc[p] = "U7"
             /\ a' = [a EXCEPT ![p] = Par[v[p]]]
             /\ IF Par[v[p]] = v[p]  \* a'[p]
                   THEN pc' = [pc EXCEPT ![p] = "U2"]
                   ELSE pc' = [pc EXCEPT ![p] = "U8"]
             /\ UNCHANGED <<Par, x, y, u, v, b>>
\* No updates to the meta-configuration.
AugU7(p) == M' = M
U7(p)    == LineU7(p) /\ AugU7(p)

\* Line U8 | b <- Par[a]
LineU8(p) == /\ pc[p] = "U8"
             /\ b' = [b EXCEPT ![p] = Par[a[p]]]
             /\ pc' = [pc EXCEPT ![p] = "U9"]
             /\ UNCHANGED <<Par, x, y, u, v, a>>
\* No updates to the meta-configuration.
AugU8(p) == M' = M
U8(p)    == LineU8(p) /\ AugU8(p)

\* Line U9 | CAS(Par[v], a, b); goto U7 or U10
LineU9(p) == /\ pc[p] = "U9"
             /\ IF Par[v[p]] = a[p]
                   THEN Par' = [Par EXCEPT ![v[p]] = b[p]]
                   ELSE Par' = Par
             /\ \/ pc' = [pc EXCEPT ![p] = "U10"]
                \/ pc' = [pc EXCEPT ![p] = "U7"]
             /\ UNCHANGED <<x, y, u, v, a, b>>
\* No updates to the meta-configuration.
AugU9(p) == M' = M
U9(p)    == LineU9(p) /\ AugU9(p)

\* Line U10 | v <- a; goto U7
LineU10(p) == /\ pc[p] = "U10"
              /\ v' = [v EXCEPT ![p] = a[p]]
              /\ pc' = [pc EXCEPT ![p] = "U7"]
              /\ UNCHANGED <<Par, x, y, u, a, b>>
\* No updates to the meta-configuration.
AugU10(p) == M' = M
U10(p)    == LineU10(p) /\ AugU10(p)

\* Line U11 | return ACK
LineU11(p) == /\ pc[p] = "U11"
              /\ \E line \in InvocationLines : pc' = [pc EXCEPT ![p] = line]
              /\ UNCHANGED <<Par, x, y, u, v, a, b>>
\* Update the meta-configuration: filter out configurations that don't match
\* the return value of p's operation, and reset the return value to BOT.
AugU11(p) == M' = {t \in AtomConfigs : \E told \in M : /\ told.f[p] = ACK
                                                       /\ t.sigma = told.sigma
                                                       /\ t.f = [told.f EXCEPT ![p] = NIL]}
U11(p) == LineU11(p) /\ AugU11(p)

\* The next-state relation.
Step(p) == \/ F1(p)
           \/ F2(p)
           \/ F3(p)
           \/ F4(p)
           \/ F5(p)
           \/ F6(p)
           \/ U1(p)
           \/ U2(p)
           \/ U3(p)
           \/ U4(p)
           \/ U5(p)
           \/ U6(p)
           \/ U7(p)
           \/ U8(p)
           \/ U9(p)
           \/ U10(p)
           \/ U11(p)
Next == \E p \in ProcSet : Step(p)

\* The specification.
Spec == Init /\ [][Next]_allvars

\* TYPE CORRECTNESS

\* Type correctness invariants for each variable
ValidPar    == Par \in [NodeSet -> NodeSet]
Validx      == x   \in [ProcSet -> NodeSet]
Validy      == y   \in [ProcSet -> NodeSet]
Validu      == u   \in [ProcSet -> NodeSet]
Validv      == v   \in [ProcSet -> NodeSet]
Valida      == a   \in [ProcSet -> NodeSet]
Validb      == b   \in [ProcSet -> NodeSet]
Validpc     == pc  \in [ProcSet -> Lines]
ValidP      == M   \in SUBSET AtomConfigs

\* Overall type-correctness invariant
TypeOK == /\ ValidPar
          /\ Validx
          /\ Validy
          /\ Validu
          /\ Validv
          /\ Valida
          /\ Validb
          /\ Validpc
          /\ ValidP

\* Proof of type-correctness
LEMMA InitTypeSafety == Init => TypeOK
  <1> USE DEF Init, InitVars, NodeSet
  <1> SUFFICES ASSUME Init
               PROVE  TypeOK
    OBVIOUS
  <1>1. ValidPar
    BY DEF ValidPar
  <1>2. Validx
    BY DEF Validx
  <1>3. Validy
    BY DEF Validy
  <1>4. Validu
    BY DEF Validu
  <1>5. Validv
    BY DEF Validv
  <1>6. Valida
    BY DEF Valida
  <1>7. Validb
    BY DEF Validb
  <1>8. Validpc
    BY DEF Validpc, InvocationLines, Lines
  <1>9. ValidP
    BY DEF ValidP, InitAug, sigmaInit, fInit, AtomConfigs, States, Rets, PowerSetNodes
  <1>10. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF TypeOK
    
LEMMA NextTypeSafety == TypeOK /\ [Next]_allvars => TypeOK'
  <1> USE DEF TypeOK, ValidPar, Validx, Validy, Validu, Validv, Valida, Validb, 
              Validpc, ValidP, Next, allvars, Step, NodeSet, Lines
  <1> SUFFICES ASSUME TypeOK,
                      [Next]_allvars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. ASSUME NEW p \in ProcSet,
               F1(p)
        PROVE  TypeOK'
    BY <1>1 DEF F1, LineF1, AugF1
  <1>2. ASSUME NEW p \in ProcSet,
               F2(p)
        PROVE  TypeOK'
    BY <1>2 DEF F2, LineF2, AugF2
  <1>3. ASSUME NEW p \in ProcSet,
               F3(p)
        PROVE  TypeOK'
    BY <1>3 DEF F3, LineF3, AugF3
  <1>4. ASSUME NEW p \in ProcSet,
               F4(p)
        PROVE  TypeOK'
    BY <1>4 DEF F4, LineF4, AugF4
  <1>5. ASSUME NEW p \in ProcSet,
               F5(p)
        PROVE  TypeOK'
    BY <1>5 DEF F5, LineF5, AugF5
  <1>6. ASSUME NEW p \in ProcSet,
               F6(p)
        PROVE  TypeOK'
    BY <1>6 DEF F6, LineF6, AugF6, InvocationLines
  <1>7. ASSUME NEW p \in ProcSet,
               U1(p)
        PROVE  TypeOK'
    BY <1>7 DEF U1, LineU1, AugU1
  <1>8. ASSUME NEW p \in ProcSet,
               U2(p)
        PROVE  TypeOK'
    BY <1>8 DEF U2, LineU2, AugU2
  <1>9. ASSUME NEW p \in ProcSet,
               U3(p)
        PROVE  TypeOK'
    BY <1>9 DEF U3, LineU3, AugU3
  <1>10. ASSUME NEW p \in ProcSet,
                U4(p)
         PROVE  TypeOK'
    BY <1>10 DEF U4, LineU4, AugU4
  <1>11. ASSUME NEW p \in ProcSet,
                U5(p)
         PROVE  TypeOK'
    BY <1>11 DEF U5, LineU5, AugU5, InvocationLines
  <1>12. ASSUME NEW p \in ProcSet,
                U6(p)
         PROVE  TypeOK'
    BY <1>12 DEF U6, LineU6, AugU6
  <1>13. ASSUME NEW p \in ProcSet,
                U7(p)
         PROVE  TypeOK'
    BY <1>13 DEF U7, LineU7, AugU7
  <1>14. ASSUME NEW p \in ProcSet,
                U8(p)
         PROVE  TypeOK'
    BY <1>14 DEF U8, LineU8, AugU8
  <1>15. ASSUME NEW p \in ProcSet,
                U9(p)
         PROVE  TypeOK'
    BY <1>15 DEF U9, LineU9, AugU9
  <1>16. ASSUME NEW p \in ProcSet,
                U10(p)
         PROVE  TypeOK'
    BY <1>16 DEF U10, LineU10, AugU10
  <1>17. ASSUME NEW p \in ProcSet,
                U11(p)
         PROVE  TypeOK'
    BY <1>17 DEF U11, LineU11, AugU11, InvocationLines
  <1>18. CASE UNCHANGED allvars
    BY <1>18
  <1>19. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, 
       <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18 DEF Step, Next

THEOREM TypeSafety == Spec => []TypeOK
  <1> SUFFICES ASSUME Spec
               PROVE  []TypeOK
    OBVIOUS             
  <1> QED
    BY PTL, InitTypeSafety, NextTypeSafety DEF Spec

\* REMAINING INVARIANTS

\* Non-line specific invariants

\* I_UF1 in the Appendix
ParPointsUp       == \A z \in NodeSet: Par[z] >= z

\* I_UF2 in the Appendix
SigmaIsPartition1 == \A z \in NodeSet: \A t \in M: 
                        z \in t.sigma[z]
                        
\* I_UF3 in the Appendix
SigmaIsPartition2 == \A w, z \in NodeSet: \A t \in M: 
                        (w \in t.sigma[z]) => (t.sigma[w] = t.sigma[z])

\* I_UF4 in the Appendix
SigmaIsCoarse     == \A w,z \in NodeSet: \A t \in M: 
                        (Par[w] = z) => (t.sigma[w] = t.sigma[z])

\* I_UF5 in the Appendix
SigmaIsFine       == \A w,z \in NodeSet: \A t \in M: 
                        (w # z /\ Par[w] = w /\ Par[z] = z) => (t.sigma[w] # t.sigma[z])

\* Lemmas regarding non-line specific invariants

\* Assumptions regarding model values

\* N is a strictly positive natural number
ASSUME NisNat == /\ N \in Nat
                 /\ N >= 1

\* ACK, NIL are distinct non-node values
ASSUME AckNilDef == /\ ACK \notin NodeSet
                    /\ NIL \notin NodeSet
                    /\ ACK # NIL


\* Mathematical fact needed for upcoming lemmas
LEMMA MaxIntegers ==
  ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
  PROVE  /\ Max(S) \in S
         /\ \A Y \in S : Y <= Max(S)
  <1>. DEFINE Pred(T) == T \in SUBSET Int /\ T # {} => \E X \in T : \A Y \in T : Y <= X
  <1>1. Pred({})
    OBVIOUS
  <1>2. ASSUME NEW T, NEW X, Pred(T), X \notin T
        PROVE  Pred(T \cup {X})
    <2>. HAVE T \cup {X} \in SUBSET Int
    <2>1. CASE \A Y \in T : Y <= X
      BY <2>1, Isa
    <2>2. CASE \E Y \in T : ~(Y <= X)
      <3> T # {}
        BY <2>2
      <3>1. PICK Y \in T : \A z \in T : z <= Y
        BY <1>2
      <3>2. X <= Y
        BY <2>2, <3>1
      <3> QED
        BY <3>1, <3>2
    <2> QED
      BY <2>1, <2>2
  <1> HIDE DEF Pred
  <1>3. Pred(S)  
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
  <1> QED
    BY <1>3, Zenon DEF Max, Pred

LEMMA MaxIsRoot == ASSUME TypeOK,
                          ParPointsUp,
                          SigmaIsPartition1,
                          SigmaIsPartition2,
                          SigmaIsCoarse,
                          SigmaIsFine,
                          NEW w \in NodeSet,
                          NEW t \in M,
                          (w = Par[w])
             PROVE Max(t.sigma[w]) = Par[Max(t.sigma[w])]
  <1> USE NisNat DEF TypeOK, ValidPar, ValidP, AtomConfigs, States, PowerSetNodes, NodeSet
  <1>1. DEFINE z == Max(t.sigma[w])
  <1>2. t.sigma[w] \in SUBSET NodeSet
    OBVIOUS  
  <1>3. IsFiniteSet(t.sigma[w])
    BY NisNat, <1>2, FS_Subset, FS_Interval
  <1>4. t.sigma[w] # {}
    BY DEF SigmaIsPartition1
  <1>5. z \in t.sigma[w]
    BY <1>3, <1>4, MaxIntegers
  <1>6. Par[z] >= z
    BY <1>5 DEF ParPointsUp
  <1>7. t.sigma[w] = t.sigma[z]
    BY <1>5 DEF SigmaIsPartition2
  <1>8. Par[z] \in NodeSet
    BY <1>5, <1>7 DEF SigmaIsCoarse, SigmaIsPartition1
  <1>9. Par[z] \in t.sigma[z]
    BY <1>5, <1>7 DEF SigmaIsPartition1, SigmaIsCoarse
  <1>10. Par[z] = z
    BY <1>6, <1>7, <1>8, <1>9 DEF Max, SigmaIsCoarse
  <1> QED     
    BY <1>10
    
LEMMA UniqueRoot == ASSUME TypeOK,
                           SigmaIsPartition2,
                           SigmaIsFine,
                           NEW t \in M,
                           NEW w \in NodeSet,
                           NEW z \in NodeSet,
                           (w = Par[w] /\ z = Par[z] /\ z \in t.sigma[w])
             PROVE w = z
  <1> USE NisNat DEF TypeOK, ValidPar, ValidP, AtomConfigs, States, PowerSetNodes, NodeSet
  <1> QED
    BY DEF SigmaIsPartition2, SigmaIsFine

LEMMA RootIsMax == ASSUME TypeOK,
                          ParPointsUp,
                          SigmaIsPartition1,
                          SigmaIsPartition2,
                          SigmaIsCoarse,
                          SigmaIsFine,
                          NEW w \in NodeSet,
                          NEW t \in M,
                          (w = Par[w])
             PROVE Max(t.sigma[w]) = w
  <1> USE NisNat DEF TypeOK, ValidPar, ValidP, AtomConfigs, States, PowerSetNodes, NodeSet
  <1>1. DEFINE z == Max(t.sigma[w])
  <1>2. (w = Par[w] /\ Par[z] = z)
    BY MaxIsRoot  
  <1>3. IsFiniteSet(t.sigma[w])
    BY NisNat, <1>2, FS_Subset, FS_Interval
  <1>4. t.sigma[w] # {}
    BY DEF SigmaIsPartition1
  <1>5. z \in t.sigma[w]
    BY <1>3, <1>4, MaxIntegers
  <1>6. (w = Par[w] /\ Par[z] = z /\ z \in t.sigma[w])
    BY <1>2, <1>5
  <1> QED     
    BY <1>6, UniqueRoot

\* Invariants for Find

\* I_{1, 7} in the paper, as it pertains to F1
InvF1  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "F1") => (t.f[p] = NIL)
             
\* I_2
InvF2  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "F2") => (/\ t.sigma[u[p]] = t.sigma[x[p]] 
                                /\ t.f[p] = NIL)
                                
\* I_3 as it pertains to atomic configurations
InvF3  == \A p \in ProcSet : \A t \in M :
             (pc[p] = "F3") => (/\ t.sigma[u[p]] = t.sigma[x[p]] 
                                /\ t.sigma[a[p]] = t.sigma[x[p]]
                                /\ t.f[p] = NIL)
 
\* I_{4, 5} as it pertains to atomic configurations and F4
InvF4  == \A p \in ProcSet : \A t \in M :
             (pc[p] = "F4") => (/\ t.sigma[u[p]] = t.sigma[x[p]] 
                                /\ t.sigma[a[p]] = t.sigma[x[p]] 
                                /\ t.sigma[b[p]] = t.sigma[x[p]]
                                /\ t.f[p] = NIL)

\* I_{4, 5} as it pertains to atomic configurations and F5
InvF5  == \A p \in ProcSet : \A t \in M :
             (pc[p] = "F5") => (/\ t.sigma[u[p]] = t.sigma[x[p]] 
                                /\ t.sigma[a[p]] = t.sigma[x[p]] 
                                /\ t.sigma[b[p]] = t.sigma[x[p]]
                                /\ t.f[p] = NIL)

\* I_6
InvF6  == \A p \in ProcSet : \A t \in M :
             (pc[p] = "F6") => (t.f[p] = u[p])

\* I_3 and I_{4, 5} as it pertains to a, b and u
InvFEx == \A p \in ProcSet : /\ (pc[p] = "F3" => a[p] >= u[p])
                             /\ (pc[p] = "F4" => (b[p] >= a[p] /\ a[p] >= u[p]))
                             /\ (pc[p] = "F5" => (b[p] >= a[p] /\ a[p] >= u[p]))
                             
\* Invariants for Unite

\* I_{1, 7} in the paper, as it pertains to U1 
InvU1  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U1") => (t.f[p] = NIL)
             
\* I_{8, 9, 13} as it pertains to U2        
InvU2  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U2") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)

\* I_{8, 9, 13} as it pertains to U3
InvU3  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U3") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)
                                
\* I_10 as it pertains to atomic configurations  
InvU4  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U4") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[a[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)
                                
\* I_{11, 12} as it pertains to atomic configurations and U5
InvU5  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U5") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[a[p]] = t.sigma[x[p]]
                                /\ t.sigma[b[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)

\* I_{11, 12} as it pertains to atomic configurations and U6
InvU6  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U6") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[a[p]] = t.sigma[x[p]]
                                /\ t.sigma[b[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)
                                
\* I_{8, 9, 13} as it pertains to U7                        
InvU7  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U7") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)
                                
\* I_14 as it pertains to atomic configurations 
InvU8  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U8") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.sigma[a[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)

\* I_{15, 16} as it pertains to atomic configurations and U9
InvU9  == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U9") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                /\ t.sigma[v[p]] = t.sigma[y[p]]
                                /\ t.sigma[a[p]] = t.sigma[y[p]]
                                /\ t.sigma[b[p]] = t.sigma[y[p]]
                                /\ t.f[p] = NIL)

\* I_{15, 16} as it pertains to atomic configurations and U10
InvU10 == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U10") => (/\ t.sigma[u[p]] = t.sigma[x[p]]
                                 /\ t.sigma[v[p]] = t.sigma[y[p]]
                                 /\ t.sigma[a[p]] = t.sigma[y[p]]
                                 /\ t.sigma[b[p]] = t.sigma[y[p]]
                                 /\ t.f[p] = NIL)

\* I_17
InvU11 == \A p \in ProcSet : \A t \in M : 
             (pc[p] = "U11") => (t.f[p] = ACK)

\* I_10, I_{11, 12}, I_14, I_{15, 16}
InvUEx == \A p \in ProcSet : /\ (pc[p] = "U4" => a[p] >= u[p])
                             /\ (pc[p] = "U5" => (b[p] >= a[p] /\ a[p] >= u[p]))
                             /\ (pc[p] = "U6" => (b[p] >= a[p] /\ a[p] >= u[p]))
                             /\ (pc[p] = "U8" => a[p] >= v[p])
                             /\ (pc[p] = "U9" => (b[p] >= a[p] /\ a[p] >= v[p]))
                             /\ (pc[p] = "U10" => (b[p] >= a[p] /\ a[p] >= v[p]))
                             
\* Linearizability
Linearizable == M # {}

\* Inductive invariant
I == /\ TypeOK
     /\ ParPointsUp
     /\ SigmaIsPartition1
     /\ SigmaIsPartition2
     /\ SigmaIsCoarse
     /\ SigmaIsFine
     /\ InvF1
     /\ InvF2
     /\ InvF3
     /\ InvF4
     /\ InvF5
     /\ InvF6
     /\ InvFEx
     /\ InvU1
     /\ InvU2
     /\ InvU3
     /\ InvU4
     /\ InvU5
     /\ InvU6
     /\ InvU7
     /\ InvU8
     /\ InvU9
     /\ InvU10
     /\ InvU11
     /\ InvUEx
     /\ Linearizable
     
\* Proof of inductive invariant

\* Show that I holds in the initial state
LEMMA InitI == Init => I
  <1> USE DEF Init, InitVars, InitAug
  <1> SUFFICES ASSUME Init
               PROVE  I
    OBVIOUS
  <1>1. TypeOK
    BY InitTypeSafety
  <1>2. ParPointsUp
    BY NisNat DEF ParPointsUp, NodeSet
  <1>3. SigmaIsPartition1
    BY DEF SigmaIsPartition1, sigmaInit
  <1>4. SigmaIsPartition2
    BY DEF SigmaIsPartition2, sigmaInit
  <1>5. SigmaIsCoarse
    BY DEF SigmaIsCoarse, sigmaInit
  <1>6. SigmaIsFine
    BY DEF SigmaIsFine, sigmaInit
  <1>7. InvF1
    BY DEF InvF1, fInit, InvocationLines, Lines
  <1>8. InvF2
    BY DEF InvF2, InvocationLines
  <1>9. InvF3
    BY DEF InvF3, InvocationLines
  <1>10. InvF4
    BY DEF InvF4, InvocationLines
  <1>11. InvF5
    BY DEF InvF5, InvocationLines
  <1>12. InvF6
    BY DEF InvF6, InvocationLines
  <1>13. InvU1
    BY DEF InvU1, fInit, InvocationLines, Lines
  <1>14. InvU2
    BY DEF InvU2, InvocationLines
  <1>15. InvU3
    BY DEF InvU3, InvocationLines
  <1>16. InvU4
    BY DEF InvU4, InvocationLines
  <1>17. InvU5
    BY DEF InvU5, InvocationLines
  <1>18. InvU6
    BY DEF InvU6, InvocationLines
  <1>19. InvU7
    BY DEF InvU7, InvocationLines
  <1>20. InvU8
    BY DEF InvU8, InvocationLines
  <1>21. InvU9
    BY DEF InvU9, InvocationLines
  <1>22. InvU10
    BY DEF InvU10, InvocationLines
  <1>23. InvU11
    BY DEF InvU11, InvocationLines
  <1>24. Linearizable
    BY DEF Linearizable, sigmaInit, fInit
  <1>25. InvFEx
    BY DEF InvFEx, InvocationLines, Lines
  <1>26. InvUEx
    BY DEF InvUEx, InvocationLines, Lines
  <1> QED
    BY <1>1, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, 
       <1>19, <1>2, <1>20, <1>21, <1>22, <1>23, <1>24, <1>3, <1>4, <1>5, 
       <1>6, <1>7, <1>8, <1>9, <1>25, <1>26 DEF I

LEMMA NextI == I /\ [Next]_allvars => I'
  <1> USE DEF I
  <1> SUFFICES ASSUME I, [Next]_allvars
               PROVE  I'
    OBVIOUS
  <1>1. ASSUME NEW p \in ProcSet,
               F1(p)
        PROVE  I'
    <2> USE <1>1 DEF F1, LineF1, AugF1
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1
    <2>8. InvF2'
      BY DEF InvF1, InvF2, TypeOK, Validx, Validu
    <2>9. InvF3'
      BY DEF InvF3
    <2>10. InvF4'
      BY DEF InvF4
    <2>11. InvF5'
      BY DEF InvF5
    <2>12. InvF6'
      BY DEF InvF6
    <2>13. InvU1'
      BY DEF InvU1
    <2>14. InvU2'
      BY DEF InvU2
    <2>15. InvU3'
      BY DEF InvU3
    <2>16. InvU4'
      BY DEF InvU4
    <2>17. InvU5'
      BY DEF InvU5
    <2>18. InvU6'
      BY DEF InvU6
    <2>19. InvU7'
      BY DEF InvU7
    <2>20. InvU8'
      BY DEF InvU8
    <2>21. InvU9'
      BY DEF InvU9
    <2>22. InvU10'
      BY DEF InvU10
    <2>23. InvU11'
      BY DEF InvU11
    <2>24. Linearizable'
      BY DEF Linearizable
    <2>25. InvFEx'
      BY DEF InvFEx
    <2>26. InvUEx'
      BY DEF InvUEx
    <2> QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, 
         <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, 
         <2>24, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>25, <2>26 DEF I
  <1>2. ASSUME NEW p \in ProcSet,
               F2(p)
        PROVE  I'
    <2> USE <1>2 DEF F2, LineF2, AugF2
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      <3> USE DEF SigmaIsPartition1
      <3> SUFFICES ASSUME NEW z \in NodeSet',
                          NEW t \in M'
                   PROVE  (z \in t.sigma[z])'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>4. SigmaIsPartition2'
      <3> USE DEF SigmaIsPartition2
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w \in t.sigma[z])'
                   PROVE  (t.sigma[w] = t.sigma[z])'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>5. SigmaIsCoarse'
      <3> USE DEF SigmaIsCoarse
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (Par[w] = z)'
                   PROVE  (t.sigma[w] = t.sigma[z])'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>6. SigmaIsFine'
      <3> USE DEF SigmaIsFine
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w # z /\ Par[w] = w /\ Par[z] = z)'
                   PROVE  (t.sigma[w] # t.sigma[z])'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>7. InvF1'
      <3> USE NextTypeSafety DEF InvF1, InvocationLines, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F1")'
                   PROVE  (t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>8. InvF2'
      <3> USE DEF InvF2, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F2")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]] 
                           /\ t.f[p_1] = NIL)'
        BY DEF InvF2
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2 DEF SigmaIsCoarse
      <3> QED
        BY <3>1, <3>2
    <2>9. InvF3'
      <3> USE DEF InvF3, TypeOK, Validpc, Valida, Validu, ValidPar
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F3")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]] 
                           /\ t.sigma[a[p_1]] = t.sigma[x[p_1]]
                           /\ t.f[p_1] = NIL)'
        BY DEF InvF3
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <2>8, <3>2 DEF SigmaIsCoarse, InvF2
      <3> QED
        BY <3>1, <3>2
    <2>10. InvF4'
      <3> USE DEF InvF4, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F4")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]] 
                           /\ t.sigma[a[p_1]] = t.sigma[x[p_1]] 
                           /\ t.sigma[b[p_1]] = t.sigma[x[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>11. InvF5'
      <3> USE DEF InvF5, TypeOK, Validpc, Valida, Validb, Validu, ValidPar
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F5")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]] 
                           /\ t.sigma[a[p_1]] = t.sigma[x[p_1]] 
                           /\ t.sigma[b[p_1]] = t.sigma[x[p_1]]
                           /\ t.f[p_1] = NIL)'
        BY DEF InvF5
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>12. InvF6'
      <3> USE DEF InvF2, InvF6, InvocationLines, 
                  TypeOK, ValidPar, Validu, Validpc, 
                  AtomConfigs, Rets
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F6")'
                   PROVE  (t.f[p_1] = u[p_1])'
        BY DEF InvF6
      <3>1. CASE Par[u[p]] = u[p]
        <4> USE <3>1
        <4>1. u'[p] = Max(t.sigma[u'[p]])
          BY Isa, RootIsMax
        <4>2. PICK told \in M: /\ told.f[p] = NIL 
                               /\ t.sigma = told.sigma 
                               /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          OBVIOUS
        <4> QED
          BY <4>1, <4>2
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2 DEF SigmaIsCoarse
      <3> QED
        BY <3>1, <3>2
    <2>13. InvU1'
      <3> USE DEF InvU1, InvocationLines, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U1")'
                   PROVE  (t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>14. InvU2'
      <3> USE DEF InvU2, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U2")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>15. InvU3'
      <3> USE DEF InvU3, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U3")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>16. InvU4'
      <3> USE DEF InvU4, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U4")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[a[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>17. InvU5'
      <3> USE DEF InvU5, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U5")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[a[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[b[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>18. InvU6'
      <3> USE DEF InvU6, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U6")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[a[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[b[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>19. InvU7'
      <3> USE DEF InvU7, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U7")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>20. InvU8'
      <3> USE DEF InvU8, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U8")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.sigma[a[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>21. InvU9'
      <3> USE DEF InvU9, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U9")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.sigma[a[p_1]] = t.sigma[y[p_1]]
                           /\ t.sigma[b[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>22. InvU10'
      <3> USE DEF InvU10, TypeOK, Validpc
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U10")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]]
                           /\ t.sigma[v[p_1]] = t.sigma[y[p_1]]
                           /\ t.sigma[a[p_1]] = t.sigma[y[p_1]]
                           /\ t.sigma[b[p_1]] = t.sigma[y[p_1]]
                           /\ t.f[p_1] = NIL)'
        OBVIOUS
      <3>1. CASE Par[u[p]] = u[p]
        <4>1. \E told \in M : /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          BY <3>1
        <4> QED
          BY <3>1, <4>1
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>23. InvU11'
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U11")'
                   PROVE  (t.f[p_1] = ACK)'
        BY DEF InvU11
      <3> USE DEF InvU2, InvU11, InvocationLines, 
                  TypeOK, ValidPar, Validu, Validpc, 
                  AtomConfigs, Rets
      <3>1. CASE Par[u[p]] = u[p]
        <4> USE <3>1
        <4>1. u'[p] = Max(t.sigma[u'[p]])
          BY Isa, RootIsMax
        <4>2. PICK told \in M: /\ told.f[p] = NIL 
                               /\ t.sigma = told.sigma 
                               /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
          OBVIOUS
        <4> QED
          BY <4>1, <4>2
      <3>2. CASE Par[u[p]] # u[p]
        BY <3>2 DEF SigmaIsCoarse
      <3> QED
        BY <3>1, <3>2
    <2>24. Linearizable'
      <3> USE NisNat DEF Linearizable, InvF2, TypeOK, ValidPar, Validx, 
                         Validy, Validu, Validv, Validpc, ValidP, AtomConfigs, 
                         Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3>1. PICK told \in M: TRUE
        BY Linearizable
      <3>2. told.f[p] = NIL
        BY <3>1
      <3>3. told.sigma[x[p]] \in PowerSetNodes
        OBVIOUS
      <3>4. told.sigma[x[p]] \in SUBSET Int
        OBVIOUS
      <3>5. x[p] \in NodeSet
        OBVIOUS
      <3>6. x[p] \in told.sigma[x[p]]
        BY DEF SigmaIsPartition1
      <3>7. told.sigma[x[p]] # {}
        BY <3>6
      <3>8. IsFiniteSet(told.sigma[x[p]])
        BY <3>3, FS_Subset, FS_Interval
      <3>9. Max(told.sigma[x[p]]) \in told.sigma[x[p]]
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, MaxIntegers DEF SigmaIsPartition1
      <3>10. Max(told.sigma[x[p]]) \in 1..N
        BY <3>9 DEF ValidP
      <3>11. [sigma |-> told.sigma, f |-> told.f] \in M
        BY <3>2
      <3>12 CASE Par[u[p]] = u[p]
        <4>1. [sigma |-> told.sigma, f |-> [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]] \in M'
          BY Zenon, <3>1, <3>12, <3>2, <3>10, <3>11
        <4> QED
          BY <4>1
      <3>13 CASE Par[u[p]] # u[p]
        <4>1. M' = M 
          BY <3>13
        <4> QED
          BY <4>1           
      <3> QED
        BY <3>12, <3>13
    <2>25. InvFEx'
      BY DEF InvFEx, ParPointsUp, TypeOK, Validpc, Valida, Validu
    <2>26. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validu
    <2> QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, 
         <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, 
         <2>24, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>25, <2>26 DEF I
  <1>3. ASSUME NEW p \in ProcSet,
               F3(p)
        PROVE  I'
    <2> USE <1>3 DEF F3, LineF3, AugF3
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1
    <2>8. InvF2'
      BY DEF InvF2
    <2>9. InvF3'
      BY DEF InvF3
    <2>10. InvF4'
      BY DEF InvF3, InvF4, TypeOK, Valida, Validb, ValidPar, SigmaIsCoarse
    <2>11. InvF5'
      BY DEF InvF5
    <2>12. InvF6'
      BY DEF InvF6
    <2>13. InvU1'
      BY DEF InvU1
    <2>14. InvU2'
      BY DEF InvU2
    <2>15. InvU3'
      BY DEF InvU3
    <2>16. InvU4'
      BY DEF InvU4
    <2>17. InvU5'
      BY DEF InvU5
    <2>18. InvU6'
      BY DEF InvU6
    <2>19. InvU7'
      BY DEF InvU7
    <2>20. InvU8'
      BY DEF InvU8
    <2>21. InvU9'
      BY DEF InvU9
    <2>22. InvU10'
      BY DEF InvU10
    <2>23. InvU11'
      BY DEF InvU11
    <2>24. Linearizable'
      BY DEF Linearizable
    <2>25. InvFEx'
      BY DEF InvFEx, ParPointsUp, TypeOK, Valida, Validb
    <2>26. InvUEx'
      BY DEF InvUEx
    <2> QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, 
         <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, 
         <2>24, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>25, <2>26 DEF I
  <1>4. ASSUME NEW p \in ProcSet,
               F4(p)
        PROVE  I'
    <2> USE <1>4 DEF F4, LineF4, AugF4
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      <3> SUFFICES ASSUME Par[u[p]] = a[p]
                   PROVE  b[p] >= u[p]
        BY DEF ParPointsUp, TypeOK, ValidPar
      <3> QED
        BY DEF InvFEx, TypeOK, Valida, Validb, Validu, NodeSet
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      <3> USE DEF SigmaIsCoarse
      <3> SUFFICES ASSUME NEW w \in NodeSet, NEW z \in NodeSet,
                          NEW t \in M,
                          Par'[w] = z,
                          Par[u[p]] = a[p],
                          Par' = [Par EXCEPT ![u[p]] = b[p]]
                   PROVE  t.sigma[w] = t.sigma[z]
        OBVIOUS
      <3>1. CASE w # u[p]
        BY <3>1
      <3>2. CASE w = u[p]
        BY <3>2 DEF InvF4
      <3> QED
        BY <3>1, <3>2
    <2>6. SigmaIsFine'
      <3> USE DEF SigmaIsFine
      <3> SUFFICES ASSUME NEW w \in NodeSet, NEW z \in NodeSet,
                          NEW t \in M,
                          (w # z /\ Par'[w] = w /\ Par'[z] = z),
                          Par[u[p]] = a[p],
                          Par' = [Par EXCEPT ![u[p]] = b[p]]
                   PROVE  (t.sigma[w] # t.sigma[z])
        OBVIOUS
      <3> QED
        BY DEF ParPointsUp, InvFEx, TypeOK, Valida, Validb, NodeSet
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, InvF4, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, InvF4, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>14. InvU2'
      BY DEF InvU2, TypeOK, Validpc
    <2>15. InvU3'
      BY DEF InvU3, TypeOK, Validpc
    <2>16. InvU4'
      BY DEF InvU4, TypeOK, Validpc
    <2>17. InvU5'
      BY DEF InvU5, TypeOK, Validpc
    <2>18. InvU6'
      BY DEF InvU6, TypeOK, Validpc
    <2>19. InvU7'
      BY DEF InvU7, TypeOK, Validpc
    <2>20. InvU8'
      BY DEF InvU8, TypeOK, Validpc
    <2>21. InvU9'
      BY DEF InvU9, TypeOK, Validpc
    <2>22. InvU10'
      BY DEF InvU10, TypeOK, Validpc
    <2>23. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>24. Linearizable'
      BY DEF Linearizable
    <2>25. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>26. InvUEx'
      BY DEF InvUEx, TypeOK, Validpc
    <2> QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, 
         <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>3, <2>4, <2>5, <2>6, 
         <2>7, <2>8, <2>9, <2>25, <2>26 DEF I
  <1>5. ASSUME NEW p \in ProcSet,
               F5(p)
        PROVE  I'
    <2> USE <1>5 DEF F5, LineF5, AugF5
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1
    <2>8. InvF2'
      BY DEF InvF2, InvF5
    <2>9. InvF3'
      BY DEF InvF3
    <2>10. InvF4'
      BY DEF InvF4
    <2>11. InvF5'
      BY DEF InvF5
    <2>12. InvF6'
      BY DEF InvF6
    <2>13. InvU1'
      BY DEF InvU1
    <2>14. InvU2'
      BY DEF InvU2
    <2>15. InvU3'
      BY DEF InvU3
    <2>16. InvU4'
      BY DEF InvU4
    <2>17. InvU5'
      BY DEF InvU5
    <2>18. InvU6'
      BY DEF InvU6
    <2>19. InvU7'
      BY DEF InvU7
    <2>20. InvU8'
      BY DEF InvU8
    <2>21. InvU9'
      BY DEF InvU9
    <2>22. InvU10'
      BY DEF InvU10
    <2>23. InvU11'
      BY DEF InvU11
    <2>24. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>24, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>2, <2>19, <2>20, <2>21, <2>22, <2>23, <2>25, <2>26, <2>3, 
         <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>6. ASSUME NEW p \in ProcSet,
               F6(p)
        PROVE  I'
    <2> USE <1>6 DEF F6, LineF6, AugF6
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY Zenon DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      <3> USE DEF SigmaIsPartition2
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w \in t.sigma[z])'
                   PROVE  (t.sigma[w] = t.sigma[z])'
        BY DEF SigmaIsPartition2
      <3>1. PICK told \in M: /\ told.f[p] = u[p]
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = NIL]
        BY Zenon
      <3> QED
        BY <3>1
    <2>5. SigmaIsCoarse'
      <3> USE DEF SigmaIsCoarse
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (Par[w] = z)'
                   PROVE  (t.sigma[w] = t.sigma[z])'
        BY DEF SigmaIsCoarse
      <3>1. PICK told \in M: /\ told.f[p] = u[p]
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = NIL]
        BY Zenon
      <3> QED
        BY <3>1
    <2>6. SigmaIsFine'
      <3> USE DEF SigmaIsFine
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w # z /\ Par[w] = w /\ Par[z] = z)'
                   PROVE  (t.sigma[w] # t.sigma[z])'
         BY DEF SigmaIsFine
      <3>1. PICK told \in M: /\ told.f[p] = u[p]
                             /\ t.sigma = told.sigma
                             /\ t.f = [told.f EXCEPT ![p] = NIL]
        BY Zenon
      <3> QED
        BY <3>1
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc, ValidP, AtomConfigs, Rets, InvocationLines
    <2>13. InvU1'
      BY DEF InvU1, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>14. InvU2'
      BY DEF InvU2, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>15. InvU3'
      BY DEF InvU3, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>16. InvU4'
      BY DEF InvU4, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>17. InvU5'
      BY DEF InvU5, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>18. InvU6'
      BY DEF InvU6, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>19. InvU7'
      BY DEF InvU7, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>20. InvU8'
      BY DEF InvU8, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>21. InvU9'
      BY DEF InvU9, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>22. InvU10'
      BY DEF InvU10, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>23. InvU11'
      BY DEF InvU11, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>24. InvFEx'
      BY DEF InvFEx, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>25. InvUEx'
      BY DEF InvUEx, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>26. Linearizable'
      <3> USE DEF Linearizable, InvF6, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
      <3>1. PICK told \in M : told.f[p] = u[p]
        OBVIOUS
      <3>3. [sigma |-> told.sigma, f |-> [told.f EXCEPT ![p] = NIL]] \in M'
        BY <3>1
      <3> QED
        BY Zenon, <3>3
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>24, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>2, <2>19, <2>20, <2>21, <2>22, <2>23, <2>25, <2>26, <2>3, 
         <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>7. ASSUME NEW p \in ProcSet,
               U1(p)
        PROVE  I'
    <2> USE <1>7 DEF U1, LineU1, AugU1
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1
    <2>8. InvF2'
      BY DEF InvF2
    <2>9. InvF3'
      BY DEF InvF3
    <2>10. InvF4'
      BY DEF InvF4
    <2>11. InvF5'
      BY DEF InvF5
    <2>12. InvF6'
      BY DEF InvF6
    <2>13. InvU1'
      BY DEF InvU1
    <2>14. InvU2'
      BY DEF InvU1, InvU2, TypeOK, Validx, Validu, Validy, Validv
    <2>15. InvU3'
      BY DEF InvU3
    <2>16. InvU4'
      BY DEF InvU4
    <2>17. InvU5'
      BY DEF InvU5
    <2>18. InvU6'
      BY DEF InvU6
    <2>19. InvU7'
      BY DEF InvU7
    <2>20. InvU8'
      BY DEF InvU8
    <2>21. InvU9'
      BY DEF InvU9
    <2>22. InvU10'
      BY DEF InvU10
    <2>23. InvU11'
      BY DEF InvU11
    <2>24. Linearizable'
      BY DEF Linearizable
    <2>25. InvFEx'
      BY DEF InvFEx
    <2>26. InvUEx'
      BY DEF InvUEx
    <2> QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, 
         <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, 
         <2>24, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>25, <2>26 DEF I
  <1>8. ASSUME NEW p \in ProcSet,
               U2(p)
        PROVE  I'
    <2> USE <1>8 DEF U2, LineU2, AugU2
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY NisNat DEF ParPointsUp, TypeOK, ValidPar, Validu, Validv, NodeSet
    <2>3. SigmaIsPartition1'
      <3> USE NisNat DEF SigmaIsPartition1, TypeOK, ValidPar, Validx, Validy, 
                         Validu, Validv, AtomConfigs, Rets, InvocationLines, 
                         States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW z \in NodeSet,
                          NEW t \in M'
                   PROVE  z \in t.sigma[z]
        BY DEF SigmaIsPartition1
      <3>1. CASE u[p] = v[p]
        <4>1 PICK told \in M: /\ told.f[p] = NIL
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = ACK]
          BY <3>1
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z] = told.sigma[z])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5> QED
            BY <5>1
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>4. SigmaIsPartition2'
      <3> USE NisNat DEF SigmaIsPartition2, TypeOK, ValidPar, Validx, Validy, Validu, Validv, 
                         AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w \in t.sigma[z])'
                   PROVE  (t.sigma[w] = t.sigma[z])'
        BY DEF SigmaIsPartition2
      <3>1. CASE u[p] = v[p]
         <4> USE <3>1
         <4>1. PICK told \in M: /\ told.f[p] = NIL
                                /\ t.sigma = told.sigma
                                /\ t.f = [told.f EXCEPT ![p] = ACK]
             OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS   
          <5> DEFINE tsigx == t.sigma[x[p]]
                     tsigy == t.sigma[y[p]]
                     tsigw == t.sigma[w]
                     tsigz == t.sigma[z]
                     toldsigx == told.sigma[x[p]]  
                     toldsigy == told.sigma[y[p]]
                     toldsigw == told.sigma[w]
                     toldsigz == told.sigma[z]
          <5>2. CASE w \in toldsigx \cup toldsigy /\ z \in toldsigx \cup toldsigy
            <6> USE <5>1, <5>2
            <6>1. tsigw = toldsigx \cup toldsigy
              OBVIOUS
            <6>2. tsigz = toldsigx \cup toldsigy
              OBVIOUS
            <6> QED
              BY <6>1, <6>2
          <5>3. CASE w \in toldsigx \cup toldsigy /\ z \notin toldsigx \cup toldsigy
            <6> USE <5>1, <5>3
            <6>1. toldsigw = toldsigz
              OBVIOUS
            <6>2. toldsigw = toldsigx \/ toldsigw = toldsigy
              OBVIOUS
            <6>3. z \notin toldsigx /\ z \notin toldsigy
              OBVIOUS
            <6>4. z \in toldsigz
              BY DEF SigmaIsPartition1 
            <6>5. toldsigz # toldsigx /\ toldsigz # toldsigy
              BY <6>3, <6>4
            <6>6. toldsigw # toldsigz
              BY <6>2, <6>5
            <6>7. FALSE
              BY <6>1, <6>6
            <6> QED
              BY <6>7
          <5>4. CASE w \notin toldsigx \cup toldsigy /\ z \in toldsigx \cup toldsigy
            <6> USE <5>1, <5>4
            <6>1. toldsigw = toldsigz
              OBVIOUS
            <6>2. toldsigw # toldsigz
              BY DEF SigmaIsPartition1
            <6> QED
              BY <6>1, <6>2
          <5>5. CASE w \notin toldsigx \cup toldsigy /\ z \notin toldsigx \cup toldsigy
            <6> USE <5>1, <5>5
            <6>1. toldsigw = toldsigz
              OBVIOUS
            <6>2. tsigw = toldsigw
              OBVIOUS
            <6>3. tsigz = toldsigz
              OBVIOUS
            <6> QED
              BY <6>2, <6>3
          <5> QED
            BY <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5> QED
            OBVIOUS
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2     
    <2>5. SigmaIsCoarse'
      <3> USE NisNat DEF SigmaIsCoarse, SigmaIsPartition1, SigmaIsPartition2, TypeOK, ValidPar, 
                         Validx, Validy, Validu, Validv, AtomConfigs, Rets, InvocationLines, 
                         States, NodeSet, PowerSetNodes,
                         InvU2
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (Par[w] = z)'
                   PROVE  (t.sigma[w] = t.sigma[z])'
        BY DEF SigmaIsCoarse
      <3>1. CASE u[p] = v[p]
         <4> USE <3>1
         <4>1. PICK told \in M: /\ told.f[p] = NIL
                                /\ t.sigma = told.sigma
                                /\ t.f = [told.f EXCEPT ![p] = ACK]
             OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p])
          <5> USE <4>1
          <5>A. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5> USE <5>A
          <5>a. DEFINE tsigx == t.sigma[x[p]]  
          <5>b. DEFINE tsigy == t.sigma[y[p]]
          <5>c. DEFINE tsigw == t.sigma[w]
          <5>d. DEFINE tsigz == t.sigma[z]
          <5>e. DEFINE toldsigx == told.sigma[x[p]]  
          <5>f. DEFINE toldsigy == told.sigma[y[p]]
          <5>g. DEFINE toldsigw == told.sigma[w]
          <5>h. DEFINE toldsigz == told.sigma[z]
          <5>1. CASE w = u[p]
            <6> USE <5>1
            <6>1. Par'[w] = v[p]
              OBVIOUS
            <6>2. w \in toldsigx
              OBVIOUS
            <6>3. w \in tsigx
              OBVIOUS
            <6>4. z = v[p]
              OBVIOUS
            <6>5. v[p] \in toldsigy
              BY <6>4
            <6>6. v[p] \in tsigy
              BY <6>5
            <6>7. tsigx = toldsigx \cup toldsigy
              OBVIOUS
            <6>8. tsigy = toldsigx \cup toldsigy
              OBVIOUS
            <6>9. tsigx = tsigy
              BY <6>7, <6>8
            <6> QED
              BY <6>5, <6>4, <6>6, <6>9
          <5>2. CASE w # u[p]
            <6> USE <5>2
            <6>1. Par'[w] = Par[w]
              OBVIOUS
            <6>2A. z \in toldsigz
              OBVIOUS
            <6>2. z \in toldsigw
              BY <6>2A
            <6>3. (w \in toldsigx \cup toldsigy) => (z \in toldsigx \cup toldsigy)
              BY <6>1, <6>2
            <6>4. (w \notin toldsigx \cup toldsigy) => (z \notin toldsigx \cup toldsigy)
              BY <6>1, <6>2
            <6>5. CASE (w \in toldsigx \cup toldsigy)
              <7> USE <6>5
              <7>1 tsigw = toldsigx \cup toldsigy
                OBVIOUS
              <7>2 tsigz = toldsigx \cup toldsigy
                BY <6>3
              <7> QED 
                BY <7>1, <7>2
            <6>6. CASE (w \notin toldsigx \cup toldsigy)
              <7> USE <6>6
              <7>1 tsigw = toldsigw
                OBVIOUS
              <7>2 tsigz = toldsigz
                BY <6>4
              <7>3 tsigz = toldsigw
                BY <6>2, <7>1, <7>2
              <7> QED
                BY <7>1, <7>3
            <6> QED
              BY <6>5, <6>6
          <5> QED
            BY <5>1, <5>2
        <4>2. CASE (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>2
          <5>A. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5> USE <5>A
          <5>a. DEFINE tsigx == t.sigma[x[p]]  
          <5>b. DEFINE tsigy == t.sigma[y[p]]
          <5>c. DEFINE tsigw == t.sigma[w]
          <5>d. DEFINE tsigz == t.sigma[z]
          <5>e. DEFINE toldsigx == told.sigma[x[p]]  
          <5>f. DEFINE toldsigy == told.sigma[y[p]]
          <5>g. DEFINE toldsigw == told.sigma[w]
          <5>h. DEFINE toldsigz == told.sigma[z]
          <5>1. CASE w = v[p]
            <6> USE <5>1
            <6>1. Par'[w] = u[p]
              OBVIOUS
            <6>2. w \in toldsigy
              OBVIOUS
            <6>3. x[p] \in toldsigx
              OBVIOUS
            <6>4. z = u[p]
              OBVIOUS
            <6>5. u[p] \in toldsigx
              BY SMTT(30), <6>3
            <6>6. u[p] \in tsigx
              BY <6>5
            <6>7. tsigy = toldsigx \cup toldsigy
              OBVIOUS
            <6>8. tsigx = toldsigx \cup toldsigy
              OBVIOUS
            <6>9. tsigx = tsigy
              BY <6>7, <6>8
            <6> QED
              BY <6>5, <6>4, <6>6, <6>9
          <5>2. CASE w # v[p]
            <6> USE <5>2
            <6>1. Par'[w] = Par[w]
              OBVIOUS
            <6>2A. z \in toldsigz
              OBVIOUS
            <6>2. z \in toldsigw
              BY <6>2A
            <6>3. (w \in toldsigx \cup toldsigy) => (z \in toldsigx \cup toldsigy)
              BY <6>1, <6>2
            <6>4. (w \notin toldsigx \cup toldsigy) => (z \notin toldsigx \cup toldsigy)
              BY <6>1, <6>2
            <6>5. CASE (w \in toldsigx \cup toldsigy)
              <7> USE <6>5
              <7>1 tsigw = toldsigx \cup toldsigy
                OBVIOUS
              <7>2 tsigz = toldsigx \cup toldsigy
                BY <6>3
              <7> QED 
                BY <7>1, <7>2
            <6>6. CASE (w \notin toldsigx \cup toldsigy)
              <7> USE <6>6
              <7>1 tsigw = toldsigw
                OBVIOUS
              <7>2 tsigz = toldsigz
                BY <6>4
              <7>3 tsigz = toldsigw
                BY <6>2, <7>1, <7>2
              <7> QED
                BY <7>1, <7>3
            <6> QED
              BY <6>5, <6>6
          <5> QED
            BY <5>1, <5>2
        <4>3. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>3
          <5> QED
            OBVIOUS
        <4> QED
          BY <4>1, <4>2, <4>3
      <3> QED
        BY <3>1, <3>2    
    <2>6. SigmaIsFine'
      <3> USE NisNat DEF SigmaIsPartition1, SigmaIsPartition2, SigmaIsCoarse, SigmaIsFine, TypeOK, ValidPar, 
                         Validx, Validy, Validu, Validv, AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes,
                         InvU2
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w # z /\ Par[w] = w /\ Par[z] = z)'
                   PROVE  (t.sigma[w] # t.sigma[z])'
        BY DEF SigmaIsFine
      <3>1. CASE u[p] = v[p]
         <4> USE <3>1
         <4>1. PICK told \in M: /\ told.f[p] = NIL
                                /\ t.sigma = told.sigma
                                /\ t.f = [told.f EXCEPT ![p] = ACK]
             OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1, <2>1, <2>2, <2>3, <2>4, <2>5
          <5>A. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5> USE <5>A
          <5>a. DEFINE tsigx == t.sigma[x[p]]  
          <5>b. DEFINE tsigy == t.sigma[y[p]]
          <5>c. DEFINE tsigw == t.sigma[w]
          <5>d. DEFINE tsigz == t.sigma[z]
          <5>e. DEFINE toldsigx == told.sigma[x[p]]  
          <5>f. DEFINE toldsigy == told.sigma[y[p]]
          <5>g. DEFINE toldsigw == told.sigma[w]
          <5>h. DEFINE toldsigz == told.sigma[z]
          <5>B. z \notin toldsigw /\ w \notin toldsigz
            OBVIOUS
          <5>1. CASE u[p] < v[p] /\ Par[u[p]] = u[p]
            <6> USE <5>1 
            <6>1. CASE w \in toldsigx \/ z \in toldsigx
              <7> USE <6>1
              <7>1. told.sigma[u[p]] = toldsigx
                OBVIOUS
              <7>2. u[p] \in toldsigx
                BY <7>1
              <7>3. Par[u[p]] = u[p]
                OBVIOUS
              <7>4. w = u[p] \/ z = u[p]
                BY UniqueRoot, <7>2, <7>3
              <7>5. Par'[u[p]] # u[p]
                OBVIOUS
              <7>6. Par'[w] # w \/ Par'[z] # z
                BY <7>4, <7>5
              <7>7 FALSE
                BY <7>6
              <7> QED
                BY <7>7
            <6>2. CASE w \in toldsigy /\ z \in toldsigy
              <7> USE <6>2
              <7>1. Par[w] = w /\ Par[z] = z
                OBVIOUS
              <7>2. w = z
                BY UniqueRoot, <7>1
              <7> QED
                BY <7>2
           <6>3 CASE w \in toldsigy /\ z \notin (toldsigx \cup toldsigy)
              <7> USE <6>3
              <7>1. tsigw = toldsigx \cup toldsigy
                OBVIOUS
              <7>2. tsigz = toldsigz
                OBVIOUS
              <7>3. tsigw # tsigz
                BY <7>1, <7>2
              <7> QED
                BY <7>3
           <6>4 CASE z \in toldsigy /\ w \notin (toldsigx \cup toldsigy)
              <7> USE <6>4
              <7>1. tsigz = toldsigx \cup toldsigy
                OBVIOUS
              <7>2. tsigw = toldsigw
                OBVIOUS
              <7>3. tsigw # tsigz
                BY <7>1, <7>2
              <7> QED
                BY <7>3
           <6>5 CASE w \notin (toldsigx \cup toldsigy) /\ z \notin (toldsigx \cup toldsigy)
              <7> USE <6>5
              <7>1. tsigw = toldsigw
                OBVIOUS
              <7>2. tsigz = toldsigz
                OBVIOUS
              <7>3. tsigw # tsigz
                BY <7>1, <7>2, <5>B
              <7> QED
                BY <7>3
           <6> QED
             BY <6>1, <6>2, <6>3, <6>4, <6>5
         <5>2. CASE u[p] > v[p] /\ Par[v[p]] = v[p]
            <6> USE <5>2
            <6>1. CASE w \in toldsigy \/ z \in toldsigy
              <7> USE <6>1
              <7>1. told.sigma[v[p]] = toldsigy
                OBVIOUS
              <7>2. v[p] \in toldsigy
                BY <7>1
              <7>3. Par[v[p]] = v[p]
                OBVIOUS
              <7>4. w = v[p] \/ z = v[p]
                BY UniqueRoot, <7>2, <7>3
              <7>5. Par'[v[p]] # v[p]
                OBVIOUS
              <7>6. Par'[w] # w \/ Par'[z] # z
                BY <7>4, <7>5
              <7>7 FALSE
                BY <7>6
              <7> QED
                BY <7>7
            <6>2. CASE w \in toldsigx /\ z \in toldsigx
              <7> USE <6>2
              <7>1. Par[w] = w /\ Par[z] = z
                OBVIOUS
              <7>2. w = z
                BY UniqueRoot, <7>1
              <7> QED
                BY <7>2
           <6>3 CASE w \in toldsigx /\ z \notin (toldsigx \cup toldsigy)
              <7> USE <6>3
              <7>1. tsigw = toldsigx \cup toldsigy
                OBVIOUS
              <7>2. tsigz = toldsigz
                OBVIOUS
              <7>3. tsigw # tsigz
                BY <7>1, <7>2
              <7> QED
                BY <7>3
           <6>4 CASE z \in toldsigx /\ w \notin (toldsigx \cup toldsigy)
              <7> USE <6>4
              <7>1. tsigz = toldsigx \cup toldsigy
                OBVIOUS
              <7>2. tsigw = toldsigw
                OBVIOUS
              <7>3. tsigw # tsigz
                BY <7>1, <7>2
              <7> QED
                BY <7>3
           <6>5 CASE w \notin (toldsigx \cup toldsigy) /\ z \notin (toldsigx \cup toldsigy)
              <7> USE <6>5
              <7>1. tsigw = toldsigw
                OBVIOUS
              <7>2. tsigz = toldsigz
                OBVIOUS
              <7>3. tsigw # tsigz
                BY <7>1, <7>2, <5>B
              <7> QED
                BY <7>3
           <6> QED
             BY <6>1, <6>2, <6>3, <6>4, <6>5
         <5> QED
           BY <5>1, <5>2
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5> QED
            OBVIOUS
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>7. InvF1'
      <3> USE DEF InvF1, TypeOK, ValidPar, Validx, Validy, Validu, Validv, 
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F1")'
                   PROVE  (t.f[p_1] = NIL)'
        BY DEF InvF1
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4>2. pc' = [pc EXCEPT ![p] = "U11"]
          OBVIOUS
        <4>3. t.f = [told.f EXCEPT ![p] = ACK]
          BY <4>1
        <4>4. CASE p_1 = p
          <5> USE <4>4
          <5>1. pc'[p_1] = "U11"
            BY <4>2
          <5> QED
            BY <5>1
        <4>5. CASE p_1 # p
          <5> USE <4>5
          <5>1. pc'[p_1] = pc[p_1]
            BY <4>2
          <5>2. t.f[p_1] = told.f[p_1]
            BY <4>3
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>4, <4>5
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. pc' = [pc EXCEPT ![p] = "U11"]
            OBVIOUS
          <5>3. t.f = [told.f EXCEPT ![p] = ACK]
            BY <5>1
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5>1. pc' = [pc EXCEPT ![p] = "U3"]
            OBVIOUS
          <5> QED
            BY <5>1
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>8. InvF2'
      <3> USE DEF InvF2, InvF4, InvF5, TypeOK, ValidPar, Validx, Validy, Validu, Validv, 
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F2")'
                   PROVE  (/\ t.sigma[u[p_1]] = t.sigma[x[p_1]] 
                           /\ t.f[p_1] = NIL)'
        BY DEF InvF2
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M : /\ told.f[p] = NIL
                                /\ t.sigma = told.sigma
                                /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4>2. pc' = [pc EXCEPT ![p] = "U11"]
          OBVIOUS
        <4>3. t.f = [told.f EXCEPT ![p] = ACK]
          BY <4>1
        <4>4. t.sigma = told.sigma
          BY <4>1
        <4>a. CASE p_1 = p
          <5> USE <4>a
          <5>1. pc'[p_1] = "U11"
            BY <4>2
          <5> QED
            BY <5>1
        <4>b. CASE p_1 # p
          <5> USE <4>b
          <5>1. pc'[p_1] = pc[p_1]
            BY <4>2
          <5>2. t.f[p_1] = told.f[p_1]
            BY <4>3
          <5>3. t.sigma = told.sigma
            BY <4>4
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>a, <4>b
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5> USE <5>1
          <5>2. pc' = [pc EXCEPT ![p] = "U11"]
            OBVIOUS
          <5>3. t.f = [told.f EXCEPT ![p] = ACK]
            BY <5>1
          <5>a. CASE x[p_1] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>a
            <6>1. t.sigma[x[p_1]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              OBVIOUS
            <6>2. pc[p_1] = "F2" => told.sigma[u[p_1]] = told.sigma[x[p_1]]
              OBVIOUS
            <6>3. pc[p_1] = "F2" => u[p_1] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. pc[p_1] = "F2" => t.sigma[u[p_1]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3
            <6>5. pc[p_1] = "F2" => t.sigma[u[p_1]] = t.sigma[x[p_1]]
              BY <6>1, <6>4
            <6> QED
              BY <5>2, <5>3, <6>5
          <5>b. CASE x[p_1] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>b
            <6>1. t.sigma[x[p_1]] = told.sigma[x[p_1]]
              OBVIOUS
            <6>2. pc[p_1] = "F2" => told.sigma[u[p_1]] = told.sigma[x[p_1]]
              OBVIOUS
            <6>3. pc[p_1] = "F2" => t.sigma[u[p_1]] = told.sigma[x[p_1]]
              BY <6>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. pc[p_1] = "F2" => t.sigma[u[p_1]] = t.sigma[x[p_1]]
              BY <6>1, <6>3
            <6> QED
              BY <5>2, <5>3, <6>5
          <5> QED
            BY <5>a, <5>b
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5>1. pc' = [pc EXCEPT ![p] = "U3"]
            OBVIOUS
          <5> QED
            BY <5>1
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>9. InvF3'
      <3> USE DEF InvF3, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "F3"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]] 
                          /\ t.sigma[a[q]] = t.sigma[x[q]]
                          /\ t.f[q] = NIL
        BY DEF InvF3
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z \in NodeSet: 
                                     (z \in told.sigma[x[p]] \cup told.sigma[y[p]])
                                        => (t.sigma[z] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z \in NodeSet:
                                     (z \notin told.sigma[x[p]] \cup told.sigma[y[p]])
                                        => (t.sigma[z] = told.sigma[z])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2
            <6>4. t.sigma[a[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6> QED
              BY <5>1, <6>3, <6>4
          <5>3. CASE x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6> HIDE <3>2
            <6>2. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6> USE <3>2
            <6>3. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[a[q]] = told.sigma[u[q]]
              OBVIOUS
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>10. InvF4'
      <3> USE DEF InvF4, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida, Validb,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "F4"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]] 
                          /\ t.sigma[a[q]] = t.sigma[x[q]]
                          /\ t.sigma[b[q]] = t.sigma[x[q]]
                          /\ t.f[q] = NIL
        BY DEF InvF4
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z \in NodeSet: 
                                     (z \in told.sigma[x[p]] \cup told.sigma[y[p]])
                                        => (t.sigma[z] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z \in NodeSet:
                                     (z \notin told.sigma[x[p]] \cup told.sigma[y[p]])
                                        => (t.sigma[z] = told.sigma[z])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3 DEF SigmaIsPartition1
            <6>5. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>4
            <6>6. t.sigma[a[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>7. t.sigma[b[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2
            <6> QED
              BY <5>1, <6>5, <6>6, <6>7
          <5>3. CASE x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>2. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[b[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[a[q]] = told.sigma[u[q]]
              OBVIOUS
            <6>6. told.sigma[b[q]] = told.sigma[u[q]]
              OBVIOUS
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>11. InvF5'
      <3> USE DEF InvF5, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida, Validb,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "F5"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]] 
                          /\ t.sigma[a[q]] = t.sigma[x[q]]
                          /\ t.sigma[b[q]] = t.sigma[x[q]]
                          /\ t.f[q] = NIL
        BY DEF InvF5
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z \in NodeSet: 
                                     (z \in told.sigma[x[p]] \cup told.sigma[y[p]])
                                        => (t.sigma[z] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z \in NodeSet:
                                     (z \notin told.sigma[x[p]] \cup told.sigma[y[p]])
                                        => (t.sigma[z] = told.sigma[z])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3 DEF SigmaIsPartition1
            <6>5. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>4
            <6>6. t.sigma[a[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>7. t.sigma[b[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2
            <6> QED
              BY <5>1, <6>5, <6>6, <6>7
          <5>3. CASE x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>2. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[b[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[a[q]] = told.sigma[u[q]]
              OBVIOUS
            <6>6. told.sigma[b[q]] = told.sigma[u[q]]
              OBVIOUS
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>12. InvF6'
      <3> USE DEF InvF6, TypeOK, ValidPar, Validx, Validy, Validu, Validv, 
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "F6")'
                   PROVE  (t.f[p_1] = u[p_1])'
        BY DEF InvU1
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4>2. pc' = [pc EXCEPT ![p] = "U11"]
          OBVIOUS
        <4>3. t.f = [told.f EXCEPT ![p] = ACK]
          BY <4>1
        <4>4. CASE p_1 = p
          <5> USE <4>4
          <5>1. pc'[p_1] = "U11"
            BY <4>2
          <5> QED
            BY <5>1
        <4>5. CASE p_1 # p
          <5> USE <4>5
          <5>1. pc'[p_1] = pc[p_1]
            BY <4>2
          <5>2. t.f[p_1] = told.f[p_1]
            BY <4>3
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>4, <4>5
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. pc' = [pc EXCEPT ![p] = "U11"]
            OBVIOUS
          <5>3. t.f = [told.f EXCEPT ![p] = ACK]
            BY <5>1
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5>1. pc' = [pc EXCEPT ![p] = "U3"]
            OBVIOUS
          <5> QED
            BY <5>1
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>13. InvU1'
      <3> USE DEF InvU1, TypeOK, ValidPar, Validx, Validy, Validu, Validv, 
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U1")'
                   PROVE  (t.f[p_1] = NIL)'
        BY DEF InvU1
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4>2. pc' = [pc EXCEPT ![p] = "U11"]
          OBVIOUS
        <4>3. t.f = [told.f EXCEPT ![p] = ACK]
          BY <4>1
        <4>4. CASE p_1 = p
          <5> USE <4>4
          <5>1. pc'[p_1] = "U11"
            BY <4>2
          <5> QED
            BY <5>1
        <4>5. CASE p_1 # p
          <5> USE <4>5
          <5>1. pc'[p_1] = pc[p_1]
            BY <4>2
          <5>2. t.f[p_1] = told.f[p_1]
            BY <4>3
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>4, <4>5
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. pc' = [pc EXCEPT ![p] = "U11"]
            OBVIOUS
          <5>3. t.f = [told.f EXCEPT ![p] = ACK]
            BY <5>1
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5>1. pc' = [pc EXCEPT ![p] = "U3"]
            OBVIOUS
          <5> QED
            BY <5>1
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>14. InvU2'
      <3> USE DEF InvU2, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          q # p,
                          NEW t \in M',
                          pc[q] = "U2"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU2
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. /\ u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                  /\ v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. /\ t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
                  /\ t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6> QED
              BY <5>1, <6>2
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>3. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>15. InvU3'
      <3> USE DEF InvU3, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U3"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU2, InvU3
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. /\ u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                  /\ v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. /\ t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
                  /\ t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6> QED
              BY <5>1, <6>2
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>3. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>16. InvU4'
      <3> USE DEF InvU4, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U4"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[a[q]] = t.sigma[x[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU4
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[u[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3
            <6>6. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>7. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>7
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4
            <6>10. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>1, <6>4
            <6>11. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[u[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3
            <6>5. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>6. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4
            <6>7. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>1, <6>4
            <6>8. t.sigma[v[q]] = t.sigma[y[q]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6> QED
              BY <5>1, <6>6, <6>7, <6>8
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6> HIDE <3>2
            <6>2. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6> USE <3>2
            <6>3. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>4. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>4
            <6>6. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>1
            <6>7. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>2
            <6>8. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4, <6>5
            <6> QED
              BY <5>1, <6>6, <6>7, <6>8
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>2. told.sigma[x[q]] = told.sigma[u[q]]
              OBVIOUS
            <6>3. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>5. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>7. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>3
            <6>9. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>5
            <6>10. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7
            <6> QED
              BY <5>1, <6>8, <6>9, <6>10
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>17. InvU5'
      <3> USE DEF InvU5, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida, Validb,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U5"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[a[q]] = t.sigma[x[q]]
                          /\ t.sigma[b[q]] = t.sigma[x[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU5
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[u[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>9. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>8 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>10. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>9
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7
            <6>12. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>13. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7, <6>9
            <6>14. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>11, <6>12, <6>13, <6>14
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[u[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7
            <6>10. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>11. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>12. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>11 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>13. t.sigma[v[q]] = t.sigma[y[q]]
              BY <5>1, <6>11, <6>12
            <6>14. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>9, <6>10, <6>13, <6>14
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>5. t.sigma[b[q]] = told.sigma[x[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>7. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>7
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>1
            <6>10. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>3
            <6>11. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7, <6>8
            <6>12. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>5
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11, <6>12
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>2. told.sigma[x[q]] = told.sigma[u[q]]
              OBVIOUS
            <6>3. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1, <6>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>5. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>7. t.sigma[b[q]] = told.sigma[x[q]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>9. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>10. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>9 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>3
            <6>12. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>5
            <6>13. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>9, <6>10
            <6>14. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7
            <6> QED
              BY <5>1, <6>11, <6>12, <6>13, <6>14
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>18. InvU6'
      <3> USE DEF InvU6, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida, Validb,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U6"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[a[q]] = t.sigma[x[q]]
                          /\ t.sigma[b[q]] = t.sigma[x[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU6
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[u[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>9. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>8 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>10. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>9
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7
            <6>12. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>13. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7, <6>9
            <6>14. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>11, <6>12, <6>13, <6>14
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[u[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7
            <6>10. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>11. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>12. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>11 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>13. t.sigma[v[q]] = t.sigma[y[q]]
              BY <5>1, <6>11, <6>12
            <6>14. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>9, <6>10, <6>13, <6>14
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>5. t.sigma[b[q]] = told.sigma[x[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>7. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>7
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>1
            <6>10. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>3
            <6>11. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7, <6>8
            <6>12. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>5
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11, <6>12
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>2. told.sigma[x[q]] = told.sigma[u[q]]
              OBVIOUS
            <6>3. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1, <6>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[x[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>5. t.sigma[a[q]] = told.sigma[x[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[x[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>7. t.sigma[b[q]] = told.sigma[x[q]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. told.sigma[v[q]] = told.sigma[y[q]]
              OBVIOUS
            <6>9. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>10. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>9 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>3
            <6>12. t.sigma[a[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>5
            <6>13. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>9, <6>10
            <6>14. t.sigma[b[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7
            <6> QED
              BY <5>1, <6>11, <6>12, <6>13, <6>14
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>19. InvU7'
      <3> USE DEF InvU7, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U7"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU7
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. /\ u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                  /\ v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. /\ t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
                  /\ t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6> QED
              BY <5>1, <6>2
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, SMTT(30) DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>1
            <6>3. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[u[q]] = told.sigma[x[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. t.sigma[x[q]] = told.sigma[x[q]]
              BY <5>1
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>20. InvU8'
      <3> USE DEF InvU8, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U8"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[a[q]] = t.sigma[y[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU8
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3
            <6>6. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>7. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>7
            <6>9. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4
            <6>10. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>1, <6>4
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. t.sigma[v[q]] = told.sigma[y[q]]
              BY <2>3, <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. t.sigma[a[q]] = told.sigma[y[q]]
              BY <2>4, <6>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>5. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5
            <6>7. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>1
            <6>8. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>3
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>5, <6>6
            <6> QED
              BY <5>1, <6>7, <6>8, <6>9
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>3
            <6>5. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>6. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4
            <6>7. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>1, <6>4
            <6>8. t.sigma[u[q]] = t.sigma[x[q]]
              BY <2>3, <2>4, <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6> QED
              BY <5>1, <6>6, <6>7, <6>8
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6>2. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>5. t.sigma[a[q]] = told.sigma[y[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>8. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>3
            <6>9. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>5
            <6>10. t.sigma[u[q]] = t.sigma[x[q]]
              BY <2>3, <2>4, <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6> QED
              BY <5>1, <6>8, <6>9, <6>10
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>21. InvU9'
      <3> USE DEF InvU9, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida, Validb,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U9"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[a[q]] = t.sigma[y[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.sigma[b[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU9
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[y[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>9. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>8 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>10. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>9
            <6>11. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7
            <6>12. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>13. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7, <6>9
            <6>14. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>11, <6>12, <6>13, <6>14
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. t.sigma[v[q]] = told.sigma[y[q]]
              BY <2>3, <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. t.sigma[a[q]] = told.sigma[y[q]]
              BY <2>4, <6>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[v[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>5. t.sigma[b[q]] = told.sigma[y[q]]
              BY <2>4, <6>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>7. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>7
            <6>9. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>1
            <6>10. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>3
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7, <6>8
            <6>12. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>5
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11, <6>12
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[y[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>9. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7
            <6>10. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY <2>3, <2>4, <5>1, <6>8 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>12. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11, <6>12
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6>2. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>5. t.sigma[a[q]] = told.sigma[y[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>7. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>3
            <6>8. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>5
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY <2>3, <2>4, <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>10. told.sigma[y[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>11. t.sigma[b[q]] = told.sigma[y[q]]
              BY <5>1, <6>10 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>12. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>11
            <6> QED
              BY <5>1, <6>7, <6>8, <6>9, <6>12
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>22. InvU10'
      <3> USE DEF InvU10, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  Valida, Validb,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          NEW t \in M',
                          pc[q] = "U10"
                   PROVE  /\ t.sigma[u[q]] = t.sigma[x[q]]
                          /\ t.sigma[a[q]] = t.sigma[y[q]]
                          /\ t.sigma[v[q]] = t.sigma[y[q]]
                          /\ t.sigma[b[q]] = t.sigma[y[q]]
                          /\ t.f[q] = NIL
        BY DEF InvU10
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. PICK told \in M: /\ told.f[p] = NIL
                               /\ t.sigma = told.sigma
                               /\ t.f = [told.f EXCEPT ![p] = ACK]
          OBVIOUS
        <4> QED
          BY <4>1
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M : /\ told.f[p] = NIL
                                  /\ \A z_1 \in NodeSet: 
                                     (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                     (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                  /\ \A z_1 \in NodeSet:
                                     (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                     (t.sigma[z_1] = told.sigma[z_1])
                                  /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>2
            <6>1. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[y[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>9. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>8 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>10. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>9
            <6>11. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7
            <6>12. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>13. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7, <6>9
            <6>14. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>11, <6>12, <6>13, <6>14
          <5>3. CASE /\ x[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>3
            <6>1. t.sigma[v[q]] = told.sigma[y[q]]
              BY <2>3, <5>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>2. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>3. t.sigma[a[q]] = told.sigma[y[q]]
              BY <2>4, <6>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[v[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>5. t.sigma[b[q]] = told.sigma[y[q]]
              BY <2>4, <6>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>7. u[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>8. t.sigma[u[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>7
            <6>9. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>1
            <6>10. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>3
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY Zenon, <5>1, <6>7, <6>8
            <6>12. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>5
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11, <6>12
          <5>4. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>4
            <6>1. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>2. a[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>1 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>3. told.sigma[y[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>4. b[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <6>3 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>5. told.sigma[v[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>6. v[q] \in told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>5 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>7. t.sigma[v[q]] = told.sigma[x[p]] \cup told.sigma[y[p]]
              BY <5>1, <6>6
            <6>8. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>9. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>7
            <6>10. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>2, <6>7
            <6>11. t.sigma[u[q]] = t.sigma[x[q]]
              BY <2>3, <2>4, <5>1, <6>8 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>12. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>4, <6>7
            <6> QED
              BY <5>1, <6>9, <6>10, <6>11, <6>12
          <5>5. CASE /\ x[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
                     /\ y[q] \notin told.sigma[x[p]] \cup told.sigma[y[p]]
            <6> USE <5>5
            <6>1. t.sigma[y[q]] = told.sigma[y[q]]
              BY <5>1
            <6>2. told.sigma[y[q]] = told.sigma[v[q]]
              OBVIOUS
            <6>3. t.sigma[v[q]] = told.sigma[y[q]]
              BY <5>1, <6>2 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>4. told.sigma[y[q]] = told.sigma[a[q]]
              OBVIOUS
            <6>5. t.sigma[a[q]] = told.sigma[y[q]]
              BY <5>1, <6>4 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>6. told.sigma[u[q]] = told.sigma[x[q]]
              OBVIOUS
            <6>7. t.sigma[v[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>3
            <6>8. t.sigma[a[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>5
            <6>9. t.sigma[u[q]] = t.sigma[x[q]]
              BY <2>3, <2>4, <5>1, <6>6 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>10. told.sigma[y[q]] = told.sigma[b[q]]
              OBVIOUS
            <6>11. t.sigma[b[q]] = told.sigma[y[q]]
              BY <5>1, <6>10 DEF SigmaIsPartition1, SigmaIsPartition2
            <6>12. t.sigma[b[q]] = t.sigma[y[q]]
              BY Zenon, <5>1, <6>11
            <6> QED
              BY <5>1, <6>7, <6>8, <6>9, <6>12
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2 
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>23. InvU11'
      <3> USE DEF InvU11, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc,
                  AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          NEW t \in M',
                          (pc[p_1] = "U11")'
                   PROVE  (t.f[p_1] = ACK)'
        BY DEF InvU5
      <3>1. CASE u[p] = v[p]
         <4> USE <3>1
         <4>1. PICK told \in M: /\ told.f[p] = NIL
                                /\ t.sigma = told.sigma
                                /\ t.f = [told.f EXCEPT ![p] = ACK]
             OBVIOUS
        <4>2. pc' = [pc EXCEPT ![p] = "U11"]
          OBVIOUS
        <4>3. t.f = [told.f EXCEPT ![p] = ACK]
          BY <4>1
        <4>a. CASE p_1 = p
          <5> USE <4>a
          <5>1. pc'[p_1] = "U11"
            BY <4>2
          <5>2. t.f[p_1] = ACK
            BY <4>3
          <5> QED
            BY <5>1, <5>2
        <4>b. CASE p_1 # p
          <5> USE <4>b
          <5>1. pc'[p_1] = pc[p_1]
            BY <4>2
          <5>2. t.f[p_1] = told.f[p_1]
            BY <4>3
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>a, <4>b
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. PICK told \in M: /\ told.f[p] = NIL
                                 /\ \A z_1 \in NodeSet: 
                                    (z_1 \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                    (t.sigma[z_1] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                                 /\ \A z_1 \in NodeSet:
                                    (z_1 \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                    (t.sigma[z_1] = told.sigma[z_1])
                                 /\ t.f = [told.f EXCEPT ![p] = ACK]
            OBVIOUS
          <5>2. pc' = [pc EXCEPT ![p] = "U11"]
            OBVIOUS
          <5>3. t.f = [told.f EXCEPT ![p] = ACK]
            BY <5>1
          <5> QED
            BY <5>2, <5>3
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          BY <4>2
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2   
    <2>24. Linearizable'
      <3> USE DEF Linearizable, InvU2, TypeOK, ValidPar, Validx, Validy, Validu, Validv, Validpc, ValidP, AtomConfigs, Rets, InvocationLines, States, NodeSet, PowerSetNodes
      <3>d. PICK told \in M: TRUE
        OBVIOUS
      <3> USE <3>d
      <3>1. CASE u[p] = v[p]
        <4> USE <3>1
        <4>1. told.f[p] = NIL
          OBVIOUS 
        <4>2. told = [sigma |-> told.sigma, f |-> told.f]
          BY <3>d DEF ValidP
        <4>3. DEFINE t == [sigma |-> told.sigma, f |-> [told.f EXCEPT ![p] = ACK]]
        <4>4. /\ told.f[p] = NIL
              /\ t.sigma = told.sigma
              /\ t.f = [told.f EXCEPT ![p] = ACK]
          BY <4>2
        <4>5. t \in AtomConfigs
          OBVIOUS
        <4>6 t \in M'
          BY <3>d, <4>2, <4>4, <4>5
        <4> QED
          BY <4>6
      <3>2. CASE u[p] # v[p]
        <4> USE <3>2
        <4>1. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
          <5> USE <4>1
          <5>1. told.f[p] = NIL
            OBVIOUS
          <5>2. told = [sigma |-> told.sigma, f |-> told.f]
            OBVIOUS
          <5>3. DEFINE tsig == [z \in NodeSet |-> IF z \in told.sigma[x[p]] \cup told.sigma[y[p]]
                                                     THEN told.sigma[x[p]] \cup told.sigma[y[p]]
                                                     ELSE told.sigma[z]]
          <5>4. DEFINE tf   == [told.f EXCEPT ![p] = ACK]
          <5>5. [sigma |-> tsig, f |-> tf] \in M'
            BY <5>1, <5>2                                        
          <5> QED
            BY <5>5
        <4>2. CASE ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
          <5> USE <4>2
          <5>1. told \in M
            OBVIOUS
          <5> QED
            BY <5>1
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2>25. InvFEx'
      BY DEF InvFEx, TypeOK, Valida, Validb, Validpc
    <2>26. InvUEx'
      BY DEF InvUEx, TypeOK, Valida, Validb, Validpc
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, 
         <2>16, <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, 
         <2>22, <2>23, <2>24, <2>25, <2>26, <2>3, <2>4, 
         <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>9. ASSUME NEW p \in ProcSet,
               U3(p)
        PROVE  I'
    <2> USE <1>9 DEF U3, LineU3, AugU3
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>14. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>15. InvU2'
      BY DEF InvU2, TypeOK, Validpc
    <2>16. InvU3'
      BY DEF InvU3, TypeOK, Validpc
    <2>17. InvU4'
      BY DEF SigmaIsCoarse, InvU3, InvU4, TypeOK, Valida, Validu, ValidPar, Validpc
    <2>18. InvU5'
      BY DEF InvU5, TypeOK, Validpc
    <2>19. InvU6'
      BY DEF InvU6, TypeOK, Validpc
    <2>20. InvU7'
      BY DEF InvU3, InvU7, TypeOK, Validpc
    <2>21. InvU8'
      BY DEF InvU8, TypeOK, Validpc
    <2>22. InvU9'
      BY DEF InvU9, TypeOK, Validpc
    <2>23. InvU10'
      BY DEF InvU10, TypeOK, Validpc
    <2>24. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validu
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, 
         <2>26, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>10. ASSUME NEW p \in ProcSet,
                U4(p)
         PROVE  I'
    <2> USE <1>10 DEF U4, LineU4, AugU4
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>14. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>15. InvU2'
      BY DEF InvU2, TypeOK, Validpc
    <2>16. InvU3'
      BY DEF InvU3, TypeOK, Validpc
    <2>17. InvU4'
      BY DEF InvU4, TypeOK, Validpc
    <2>18. InvU5'
      BY DEF InvU4, InvU5, TypeOK, Valida, Validb, ValidPar, SigmaIsCoarse
    <2>19. InvU6'
      BY DEF InvU6, TypeOK, Validpc
    <2>20. InvU7'
      BY DEF InvU7, TypeOK, Validpc
    <2>21. InvU8'
      BY DEF InvU8, TypeOK, Validpc
    <2>22. InvU9'
      BY DEF InvU9, TypeOK, Validpc
    <2>23. InvU10'
      BY DEF InvU10, TypeOK, Validpc
    <2>24. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validb
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, 
         <2>26, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>11. ASSUME NEW p \in ProcSet,
                U5(p)
         PROVE  I'
    <2> USE <1>11 DEF U5, LineU5, AugU5
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      <3> SUFFICES ASSUME Par[u[p]] = a[p]
                   PROVE  b[p] >= u[p]
        BY DEF ParPointsUp, TypeOK, ValidPar
      <3> QED
        BY DEF InvUEx, TypeOK, Valida, Validb, Validu, NodeSet
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      <3> USE DEF SigmaIsCoarse
      <3> SUFFICES ASSUME NEW w \in NodeSet, NEW z \in NodeSet,
                          NEW t \in M,
                          Par'[w] = z,
                          Par[u[p]] = a[p],
                          Par' = [Par EXCEPT ![u[p]] = b[p]]
                   PROVE  t.sigma[w] = t.sigma[z]
        OBVIOUS
      <3>1. CASE w # u[p]
        BY <3>1
      <3>2. CASE w = u[p]
        BY <3>2 DEF InvU5
      <3> QED
        BY <3>1, <3>2
    <2>6. SigmaIsFine'
      <3> USE DEF SigmaIsFine
      <3> SUFFICES ASSUME NEW w \in NodeSet, NEW z \in NodeSet,
                          NEW t \in M,
                          (w # z /\ Par'[w] = w /\ Par'[z] = z),
                          Par[u[p]] = a[p],
                          Par' = [Par EXCEPT ![u[p]] = b[p]]
                   PROVE  (t.sigma[w] # t.sigma[z])
        OBVIOUS
      <3> QED
        BY DEF ParPointsUp, InvUEx, TypeOK, Valida, Validb, NodeSet
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>14. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>15. InvU2'
      BY DEF InvU2, TypeOK, Validpc
    <2>16. InvU3'
      BY DEF InvU3, InvU5, TypeOK, Validpc
    <2>17. InvU4'
      BY DEF InvU4, TypeOK, Validpc
    <2>18. InvU5'
      BY DEF InvU5, TypeOK, Validpc
    <2>19. InvU6'
      BY DEF InvU5, InvU6, TypeOK, Validpc
    <2>20. InvU7'
      BY DEF InvU7, TypeOK, Validpc
    <2>21. InvU8'
      BY DEF InvU8, TypeOK, Validpc
    <2>22. InvU9'
      BY DEF InvU9, TypeOK, Validpc
    <2>23. InvU10'
      BY DEF InvU10, TypeOK, Validpc
    <2>24. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validb
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, 
         <2>26, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>12. ASSUME NEW p \in ProcSet,
                U6(p)
         PROVE  I'
    <2> USE <1>12 DEF U6, LineU6, AugU6
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1
    <2>8. InvF2'
      BY DEF InvF2
    <2>9. InvF3'
      BY DEF InvF3
    <2>10. InvF4'
      BY DEF InvF4
    <2>11. InvF5'
      BY DEF InvF5
    <2>12. InvF6'
      BY DEF InvF6
    <2>13. InvU1'
      BY DEF InvU1
    <2>14. InvU2'
      BY DEF InvU2
    <2>15. InvU3'
      BY DEF InvU3, InvU6
    <2>16. InvU4'
      BY DEF InvU4
    <2>17. InvU5'
      BY DEF InvU5
    <2>18. InvU6'
      BY DEF InvU6
    <2>19. InvU7'
      BY DEF InvU7
    <2>20. InvU8'
      BY DEF InvU8
    <2>21. InvU9'
      BY DEF InvU9
    <2>22. InvU10'
      BY DEF InvU10
    <2>23. InvU11'
      BY DEF InvU11
    <2>24. InvFEx'
      BY DEF InvFEx
    <2>25. InvUEx'
      BY DEF InvUEx, TypeOK, Validpc
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>24, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>2, <2>19, <2>20, <2>21, <2>22, <2>23, <2>25, <2>26, <2>3, 
         <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>13. ASSUME NEW p \in ProcSet,
                U7(p)
         PROVE  I'
    <2> USE <1>13 DEF U7, LineU7, AugU7
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>14. InvU2'
      BY DEF InvU2, InvU7, TypeOK, Validpc
    <2>15. InvU3'
      BY DEF InvU3, TypeOK, Validpc
    <2>16. InvU4'
      BY DEF InvU4, TypeOK, Validpc
    <2>17. InvU5'
      BY DEF InvU5, TypeOK, Validpc
    <2>18. InvU6'
      BY DEF InvU6, TypeOK, Validpc
    <2>19. InvU7'
      BY DEF InvU7, TypeOK, Validpc
    <2>20. InvU8'
      BY DEF SigmaIsCoarse, InvU7, InvU8, TypeOK, Valida, Validv, ValidPar, Validpc
    <2>21. InvU9'
      BY DEF InvU9, TypeOK, Validpc
    <2>22. InvU10'
      BY DEF InvU10, TypeOK, Validpc
    <2>23. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>24. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validv
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>24, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>2, <2>19, <2>20, <2>21, <2>22, <2>23, <2>25, <2>26, <2>3, 
         <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>14. ASSUME NEW p \in ProcSet,
                U8(p)
         PROVE  I'
    <2> USE <1>14 DEF U8, LineU8, AugU8
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>14. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>15. InvU2'
      BY DEF InvU2, TypeOK, Validpc
    <2>16. InvU3'
      BY DEF InvU3, TypeOK, Validpc
    <2>17. InvU4'
      BY DEF InvU4, TypeOK, Validpc
    <2>18. InvU5'
      BY DEF InvU5, TypeOK, Validpc
    <2>19. InvU6'
      BY DEF InvU6, TypeOK, Validpc
    <2>20. InvU7'
      BY DEF InvU7, TypeOK, Validpc
    <2>21. InvU8'
      BY DEF InvU8, TypeOK, Validpc
    <2>22. InvU9'
      BY DEF InvU8, InvU9, TypeOK, Valida, Validb, ValidPar, SigmaIsCoarse
    <2>23. InvU10'
      BY DEF InvU10, TypeOK, Validpc
    <2>24. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validb
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, 
         <2>26, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>15. ASSUME NEW p \in ProcSet,
                U9(p)
         PROVE  I'
    <2> USE <1>15 DEF U9, LineU9, AugU9
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      <3> SUFFICES ASSUME Par[v[p]] = a[p]
                   PROVE  b[p] >= v[p]
        BY DEF ParPointsUp, TypeOK, ValidPar
      <3> QED
        BY DEF InvUEx, TypeOK, Valida, Validb, Validv, NodeSet
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      <3> USE DEF SigmaIsCoarse
      <3> SUFFICES ASSUME NEW w \in NodeSet, NEW z \in NodeSet,
                          NEW t \in M,
                          Par'[w] = z,
                          Par[v[p]] = a[p],
                          Par' = [Par EXCEPT ![v[p]] = b[p]]
                   PROVE  t.sigma[w] = t.sigma[z]
        OBVIOUS
      <3>1. CASE w # v[p]
        BY <3>1
      <3>2. CASE w = v[p]
        BY <3>2 DEF InvU9
      <3> QED
        BY <3>1, <3>2
    <2>6. SigmaIsFine'
      <3> USE DEF SigmaIsFine
      <3> SUFFICES ASSUME NEW w \in NodeSet, NEW z \in NodeSet,
                          NEW t \in M,
                          (w # z /\ Par'[w] = w /\ Par'[z] = z),
                          Par[v[p]] = a[p],
                          Par' = [Par EXCEPT ![v[p]] = b[p]]
                   PROVE  (t.sigma[w] # t.sigma[z])
        OBVIOUS
      <3> QED
        BY DEF ParPointsUp, InvUEx, TypeOK, Valida, Validb, NodeSet
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, Validpc
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, Validpc
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, Validpc
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, Validpc
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, Validpc
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc
    <2>13. InvFEx'
      BY DEF InvFEx, TypeOK, Validpc
    <2>14. InvU1'
      BY DEF InvU1, TypeOK, Validpc
    <2>15. InvU2'
      BY DEF InvU2, TypeOK, Validpc
    <2>16. InvU3'
      BY DEF InvU3, TypeOK, Validpc
    <2>17. InvU4'
      BY DEF InvU4, TypeOK, Validpc
    <2>18. InvU5'
      BY DEF InvU5, TypeOK, Validpc
    <2>19. InvU6'
      BY DEF InvU6, TypeOK, Validpc
    <2>20. InvU7'
      BY DEF InvU7, InvU9, TypeOK, Validpc
    <2>21. InvU8'
      BY DEF InvU8, TypeOK, Validpc
    <2>22. InvU9'
      BY DEF InvU9, TypeOK, Validpc
    <2>23. InvU10'
      BY DEF InvU10, InvU9, TypeOK, Validpc
    <2>24. InvU11'
      BY DEF InvU11, TypeOK, Validpc
    <2>25. InvUEx'
      BY DEF InvUEx, ParPointsUp, TypeOK, Validpc, Valida, Validb
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, 
         <2>26, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>16. ASSUME NEW p \in ProcSet,
                U10(p)
         PROVE  I'
    <2> USE <1>16 DEF U10, LineU10, AugU10
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      BY DEF SigmaIsPartition2
    <2>5. SigmaIsCoarse'
      BY DEF SigmaIsCoarse
    <2>6. SigmaIsFine'
      BY DEF SigmaIsFine
    <2>7. InvF1'
      BY DEF InvF1
    <2>8. InvF2'
      BY DEF InvF2
    <2>9. InvF3'
      BY DEF InvF3
    <2>10. InvF4'
      BY DEF InvF4
    <2>11. InvF5'
      BY DEF InvF5
    <2>12. InvF6'
      BY DEF InvF6
    <2>13. InvU1'
      BY DEF InvU1
    <2>14. InvU2'
      BY DEF InvU2
    <2>15. InvU3'
      BY DEF InvU3
    <2>16. InvU4'
      BY DEF InvU4
    <2>17. InvU5'
      BY DEF InvU5
    <2>18. InvU6'
      BY DEF InvU6
    <2>19. InvU7'
      BY DEF InvU7, InvU10
    <2>20. InvU8'
      BY DEF InvU8
    <2>21. InvU9'
      BY DEF InvU9
    <2>22. InvU10'
      BY DEF InvU10
    <2>23. InvU11'
      BY DEF InvU11
    <2>24. InvFEx'
      BY DEF InvFEx
    <2>25. InvUEx'
      BY DEF InvUEx, TypeOK, Validpc
    <2>26. Linearizable'
      BY DEF Linearizable
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>24, <2>13, <2>14, <2>15, <2>16, <2>17, 
         <2>18, <2>2, <2>19, <2>20, <2>21, <2>22, <2>23, <2>25, <2>26, <2>3, 
         <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>17. ASSUME NEW p \in ProcSet,
                U11(p)
         PROVE  I'
    <2> USE <1>17 DEF U11, LineU11, AugU11
    <2>1. TypeOK'
      BY NextTypeSafety
    <2>2. ParPointsUp'
      BY DEF ParPointsUp
    <2>3. SigmaIsPartition1'
      BY Zenon DEF SigmaIsPartition1
    <2>4. SigmaIsPartition2'
      <3> USE DEF SigmaIsPartition2
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w \in t.sigma[z])'
                   PROVE  (t.sigma[w] = t.sigma[z])'
         BY DEF SigmaIsPartition2
       <3>1. PICK told \in M: /\ told.f[p] = ACK
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = NIL]
         BY Zenon
      <3> QED
        BY <3>1
    <2>5. SigmaIsCoarse'
      <3> USE DEF SigmaIsCoarse
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (Par[w] = z)'
                   PROVE  (t.sigma[w] = t.sigma[z])'
         BY DEF SigmaIsCoarse
       <3>1. PICK told \in M: /\ told.f[p] = ACK
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = NIL]
         BY Zenon
      <3> QED
        BY <3>1
    <2>6. SigmaIsFine'
      <3> USE DEF SigmaIsFine
      <3> SUFFICES ASSUME NEW w \in NodeSet', NEW z \in NodeSet',
                          NEW t \in M',
                          (w # z /\ Par[w] = w /\ Par[z] = z)'
                   PROVE  (t.sigma[w] # t.sigma[z])'
         BY DEF SigmaIsFine
       <3>1. PICK told \in M: /\ told.f[p] = ACK
                              /\ t.sigma = told.sigma
                              /\ t.f = [told.f EXCEPT ![p] = NIL]
         BY Zenon
      <3> QED
        BY <3>1
    <2>7. InvF1'
      BY DEF InvF1, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>8. InvF2'
      BY DEF InvF2, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>9. InvF3'
      BY DEF InvF3, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>10. InvF4'
      BY DEF InvF4, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>11. InvF5'
      BY DEF InvF5, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>12. InvF6'
      BY DEF InvF6, TypeOK, Validpc, ValidP, AtomConfigs, Rets, InvocationLines
    <2>13. InvU1'
      BY DEF InvU1, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>14. InvU2'
      BY DEF InvU2, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>15. InvU3'
      BY DEF InvU3, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>16. InvU4'
      BY DEF InvU4, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>17. InvU5'
      BY DEF InvU5, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>18. InvU6'
      BY DEF InvU6, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>19. InvU7'
      BY DEF InvU7, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>20. InvU8'
      BY DEF InvU8, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>21. InvU9'
      BY DEF InvU9, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>22. InvU10'
      BY DEF InvU10, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>23. InvU11'
      BY DEF InvU11, TypeOK, Validpc, ValidP, AtomConfigs, Rets, InvocationLines
    <2>24. InvFEx'
      BY DEF InvFEx, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>25. InvUEx'
      BY DEF InvUEx, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
    <2>26. Linearizable'
      <3> USE DEF Linearizable, InvU11, TypeOK, ValidP, AtomConfigs, Rets, InvocationLines
      <3>1. PICK told \in M : told.f[p] = ACK
        OBVIOUS
      <3>3. [sigma |-> told.sigma, f |-> [told.f EXCEPT ![p] = NIL]] \in M'
        BY <3>1
      <3> QED
        BY Zenon, <3>3
    <2>27. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, 
         <2>16, <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, 
         <2>22, <2>23, <2>24, <2>25, <2>26, <2>3, <2>4, 
         <2>5, <2>6, <2>7, <2>8, <2>9 DEF I
  <1>18. CASE UNCHANGED allvars
    BY <1>18, NextTypeSafety DEF allvars, TypeOK, ParPointsUp, SigmaIsPartition1, 
                                 SigmaIsPartition2, SigmaIsCoarse, SigmaIsFine,
                                 InvF1, InvF2, InvF3, InvF4, InvF5, InvF6, InvFEx,
                                 InvU1, InvU2, InvU3, InvU4, InvU5, InvU6, InvU7,
                                 InvU8, InvU9, InvU10, InvU11, InvUEx, Linearizable
  <1>19. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17,
       <1>18, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Step, Next

THEOREM AlwaysI == Spec => []I
  <1> SUFFICES ASSUME Spec
               PROVE  []I
    OBVIOUS             
  <1> QED
    BY PTL, InitI, NextI    DEF Spec
    
\* Proof of linearizability
THEOREM Linearizability == Spec => [](M # {})
  BY PTL, AlwaysI DEF I, Linearizable
  
\* Proof of strong linearizability
UniquePossibility == \A s, t \in M : s = t

LEMMA InitUniquePossibility == Init => UniquePossibility
  <1> SUFFICES ASSUME Init,
                      NEW s \in M, NEW t \in M
               PROVE  s = t
    BY DEF UniquePossibility
  <1> USE DEF Init, InitAug, UniquePossibility
  <1>1. s = [sigma |-> sigmaInit, f |-> fInit]
    OBVIOUS
  <1>2. t = [sigma |-> sigmaInit, f |-> fInit]
    OBVIOUS
  <1>3. s = t
    BY <1>1, <1>2
  <1> QED
    BY <1>3

LEMMA NextUniquePossibility == UniquePossibility /\ [Next]_allvars => UniquePossibility'
  <1> SUFFICES ASSUME UniquePossibility,
                      [Next]_allvars
               PROVE  UniquePossibility'
    OBVIOUS
  <1>1. ASSUME NEW p \in ProcSet,
               F1(p)
        PROVE  UniquePossibility'
    BY <1>1 DEF UniquePossibility, F1, AugF1 
  <1>2. ASSUME NEW p \in ProcSet,
               F2(p)
        PROVE  UniquePossibility'
    <2> SUFFICES ASSUME NEW s \in M', NEW t \in M'
                 PROVE  (s = t)'
      BY DEF UniquePossibility
    <2> USE <1>2, NextI DEF UniquePossibility, F2, AugF2, TypeOK, 
                            ValidP, AtomConfigs, States, Rets, PowerSetNodes
    <2>1. CASE Par[u[p]] = u[p]
      <3> USE <2>1
      <3>1. PICK sold \in M: /\ sold.f[p] = NIL 
                             /\ s.sigma = sold.sigma 
                             /\ s.f = [sold.f EXCEPT ![p] = Max(sold.sigma[x[p]])]
        OBVIOUS
      <3>2. s = [sigma |-> sold.sigma, f |-> [sold.f EXCEPT ![p] = Max(sold.sigma[x[p]])]]
        BY <3>1
      <3>3. PICK told \in M: /\ told.f[p] = NIL 
                             /\ t.sigma = told.sigma 
                             /\ t.f = [told.f EXCEPT ![p] = Max(told.sigma[x[p]])]
        OBVIOUS
      <3>4. told = sold
        OBVIOUS
      <3>5. t = [sigma |-> sold.sigma, f |-> [sold.f EXCEPT ![p] = Max(sold.sigma[x[p]])]]
        BY <3>3, <3>4
      <3> QED
        BY <3>2, <3>5
    <2>2. CASE Par[u[p]] # u[p]
      <3> USE <2>2
      <3> QED
        OBVIOUS
    <2> QED
      BY <2>1, <2>2
  <1>3. ASSUME NEW p \in ProcSet,
               F3(p)
        PROVE  UniquePossibility'
    BY <1>3 DEF UniquePossibility, F3, AugF3
  <1>4. ASSUME NEW p \in ProcSet,
               F4(p)
        PROVE  UniquePossibility'
    BY <1>4 DEF UniquePossibility, F4, AugF4
  <1>5. ASSUME NEW p \in ProcSet,
               F5(p)
        PROVE  UniquePossibility'
    BY <1>5 DEF UniquePossibility, F5, AugF5
  <1>6. ASSUME NEW p \in ProcSet,
               F6(p)
        PROVE  UniquePossibility'
    <2> SUFFICES ASSUME NEW s \in M', NEW t \in M'
                 PROVE  (s = t)'
      BY DEF UniquePossibility
    <2> USE <1>6, NextI DEF UniquePossibility, F6, AugF6, 
                            TypeOK, ValidP, AtomConfigs, States, Rets, PowerSetNodes
    <2>1. PICK sold \in M: /\ sold.f[p] = u[p]
                           /\ s.sigma = sold.sigma
                           /\ s.f = [sold.f EXCEPT ![p] = NIL]
      OBVIOUS
    <2>2. PICK told \in M: /\ told.f[p] = u[p]
                           /\ t.sigma = told.sigma
                           /\ t.f = [told.f EXCEPT ![p] = NIL]
      OBVIOUS
    <2>3. sold = told
      OBVIOUS
    <2>4. t = s
      BY <2>1, <2>2, <2>3
    <2> QED
      BY <2>4
  <1>7. ASSUME NEW p \in ProcSet,
               U1(p)
        PROVE  UniquePossibility'
    BY <1>7 DEF UniquePossibility, U1, AugU1
  <1>8. ASSUME NEW p \in ProcSet,
               U2(p)
        PROVE  UniquePossibility'
    <2> USE <1>8, NextI DEF UniquePossibility, U2, AugU2, TypeOK, 
                            ValidP, AtomConfigs, States, Rets, PowerSetNodes
    <2> SUFFICES ASSUME NEW s \in M', NEW t \in M'
                 PROVE  (s = t)'
      BY DEF UniquePossibility
    <2>1. CASE u[p] = v[p]
      <3> USE <2>1
      <3>1. PICK sold \in M: /\ sold.f[p] = NIL
                             /\ s.sigma = sold.sigma
                             /\ s.f = [sold.f EXCEPT ![p] = ACK]
        OBVIOUS
      <3>2. PICK told \in M: /\ told.f[p] = NIL
                             /\ t.sigma = told.sigma
                             /\ t.f = [told.f EXCEPT ![p] = ACK]
        OBVIOUS
      <3>3. sold = told
        OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. CASE (u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p])
      <3> USE <2>2
      <3>1. PICK sold \in M: /\ sold.f[p] = NIL
                             /\ \A z \in NodeSet: 
                                (z \in sold.sigma[x[p]] \cup sold.sigma[y[p]]) => 
                                (s.sigma[z] = sold.sigma[x[p]] \cup sold.sigma[y[p]]) 
                             /\ \A z \in NodeSet:
                                (z \notin sold.sigma[x[p]] \cup sold.sigma[y[p]]) =>
                                (s.sigma[z] = sold.sigma[z])
                             /\ s.f = [sold.f EXCEPT ![p] = ACK]
        OBVIOUS
      <3>2. PICK told \in M: /\ told.f[p] = NIL
                             /\ \A z \in NodeSet: 
                                (z \in told.sigma[x[p]] \cup told.sigma[y[p]]) => 
                                (t.sigma[z] = told.sigma[x[p]] \cup told.sigma[y[p]]) 
                             /\ \A z \in NodeSet:
                                (z \notin told.sigma[x[p]] \cup told.sigma[y[p]]) =>
                                (t.sigma[z] = told.sigma[z])
                             /\ t.f = [told.f EXCEPT ![p] = ACK]
        OBVIOUS
      <3>3. sold = told
        OBVIOUS
      <3>4. DEFINE newsigma == [z \in NodeSet |-> IF z \in sold.sigma[x[p]] \cup sold.sigma[y[p]] 
                                                    THEN sold.sigma[x[p]] \cup sold.sigma[y[p]]
                                                    ELSE sold.sigma[z]]
      <3>5. DEFINE newf     == [sold.f EXCEPT ![p] = ACK]
      <3>6. s = [sigma |-> newsigma, f |-> newf]
        BY <3>1
      <3>7. t = [sigma |-> newsigma, f |-> newf]
        BY <3>2, <3>3
      <3> QED
        BY <3>6, <3>7
    <2>3. CASE ~(u[p] = v[p]) /\ ~((u[p] < v[p] /\ Par[u[p]] = u[p]) \/ (u[p] > v[p] /\ Par[v[p]] = v[p]))
      <3> USE <2>3
      <3> QED
        OBVIOUS
    <2> QED
      BY <2>1, <2>2, <2>3
  <1>9. ASSUME NEW p \in ProcSet,
               U3(p)
        PROVE  UniquePossibility'
    BY <1>9 DEF UniquePossibility, U3, AugU3
  <1>10. ASSUME NEW p \in ProcSet,
                U4(p)
         PROVE  UniquePossibility'
    BY <1>10 DEF UniquePossibility, U4, AugU4
  <1>11. ASSUME NEW p \in ProcSet,
                U5(p)
         PROVE  UniquePossibility'
    BY <1>11 DEF UniquePossibility, U5, AugU5
  <1>12. ASSUME NEW p \in ProcSet,
                U6(p)
         PROVE  UniquePossibility'
    BY <1>12 DEF UniquePossibility, U6, AugU6
  <1>13. ASSUME NEW p \in ProcSet,
                U7(p)
         PROVE  UniquePossibility'
    BY <1>13 DEF UniquePossibility, U7, AugU7
  <1>14. ASSUME NEW p \in ProcSet,
                U8(p)
         PROVE  UniquePossibility'
    BY <1>14 DEF UniquePossibility, U8, AugU8
  <1>15. ASSUME NEW p \in ProcSet,
                U9(p)
         PROVE  UniquePossibility'
    BY <1>15 DEF UniquePossibility, U9, AugU9
  <1>16. ASSUME NEW p \in ProcSet,
                U10(p)
         PROVE  UniquePossibility'
    BY <1>16 DEF UniquePossibility, U10, AugU10
  <1>17. ASSUME NEW p \in ProcSet,
                U11(p)
         PROVE  UniquePossibility'
    <2> USE <1>17, NextI DEF UniquePossibility, U11, AugU11, 
                   TypeOK, ValidP, AtomConfigs, States, Rets, PowerSetNodes
    <2> SUFFICES ASSUME NEW s \in M', NEW t \in M'
                 PROVE  (s = t)'
      BY DEF UniquePossibility
    <2>1. PICK sold \in M: /\ sold.f[p] = ACK
                           /\ s.sigma = sold.sigma
                           /\ s.f = [sold.f EXCEPT ![p] = NIL]
      OBVIOUS                       
    <2>2. PICK told \in M: /\ told.f[p] = ACK
                           /\ t.sigma = told.sigma
                           /\ t.f = [told.f EXCEPT ![p] = NIL]
      OBVIOUS                       
    <2>3. sold = told
      OBVIOUS
    <2> QED
      BY <2>1, <2>2, <2>3
  <1>18. CASE UNCHANGED allvars
    BY <1>18 DEF UniquePossibility, allvars
  <1>19. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, 
    <1>18, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Step, Next

LEMMA AlwaysUniquePossibility == Spec => []UniquePossibility
  BY PTL, InitUniquePossibility, NextUniquePossibility DEF Spec

LEMMA Cardinality1 == ASSUME Linearizable,
                             UniquePossibility
                      PROVE  Cardinality(M) = 1
<1> USE DEF Linearizable, UniquePossibility, Cardinality
<1>1. PICK t \in M: TRUE
  OBVIOUS
<1>2. M = {t}
  BY <1>1
<1>3. Cardinality(M) = 1
  BY <1>2, FS_Singleton
<1> QED
  BY <1>3

THEOREM StrongLinearizability == Spec => [](Cardinality(M) = 1)
  BY PTL, Linearizability, AlwaysUniquePossibility, Cardinality1 DEF Linearizable

=============================================================================
\* Modification History
\* Last modified Sat Oct 07 17:18:58 EDT 2023 by uguryavuz
\* Created Sat Oct 07 14:19:49 EDT 2023 by uguryavuz
