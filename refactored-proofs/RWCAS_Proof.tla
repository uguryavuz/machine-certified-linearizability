---------------------------- MODULE RWCAS_Proof ----------------------------
EXTENDS RWCAS_Implementation,
        Integers, Sequences, FiniteSets, Permutations,
        TLAPS, NaturalsInduction, FiniteSetTheorems
INSTANCE Augmentation \* Sets constants BOT, ConfigDomain, Delta(_, _, _), ProcSet 
                      \* in Augmentation, to those specified in RWCAS_Type
                      \* which itself is imported by extending RWCAS_Implementation

VARIABLE P
vars == algvars \o <<pc, arg, ret, P>>

\* Needed assumptions
ASSUME RemDef == RemainderID = "L0"
ASSUME NonEmptyStateDomain == StateDomain # {}
ASSUME AckBotDef == /\ BOT \notin {"R", "W", ACK}
                    /\ BOT \notin StateDomain

AInit == /\ Init
         /\ P = {[state |-> X,
                  op    |-> [p \in ProcSet |-> BOT],
                  arg   |-> [p \in ProcSet |-> BOT],
                  res   |-> [p \in ProcSet |-> BOT]]}
                  
L0(p) == /\ pc[p] = RemainderID
         /\ \E op \in OpNames :
            /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
            /\ \E arg_val \in ArgsOf(op) : 
               /\ IF arg_val # BOT 
                     THEN arg' = [arg EXCEPT ![p] = arg_val]
                     ELSE arg' = arg  \* Very useful not to set arg to BOT.
                                      \* Otherwise you'd have to deal with line numbers in TypeOK.
               /\ P' = Evolve(Invoke(P, p, op, arg_val))
         /\ UNCHANGED algvars
         /\ UNCHANGED ret

IntLine(p) == \E Line \in IntLines(p) : /\ Line
                                        /\ P' = Evolve(P)
                                        
RetLine(p) == \E Line \in RetLines(p) : /\ Line
                                        /\ P' = Filter(Evolve(P), p, ret'[p])

Next == \E p \in ProcSet : \/ L0(p)
                           \/ IntLine(p)
                           \/ RetLine(p)

Spec == AInit /\ [][Next]_vars

\* Type correctness
PTypeOK == P \in SUBSET ConfigDomain

LEMMA InitPTypeOK == AInit => PTypeOK
  <1> SUFFICES ASSUME AInit
               PROVE  PTypeOK
    OBVIOUS
  <1> QED
    BY DEF AInit, Init, InitState, PTypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
  
  
LEMMA NextPTypeOK == PTypeOK /\ [Next]_vars => PTypeOK'
  <1> USE DEF PTypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
  <1> SUFFICES ASSUME PTypeOK,
                      [Next]_vars
               PROVE  PTypeOK'
    OBVIOUS
  <1>1. ASSUME NEW p \in ProcSet,
               L0(p)
        PROVE  PTypeOK'
    BY <1>1 DEF L0, Invoke, Evolve 
  <1>2. ASSUME NEW p \in ProcSet,
               L1(p),
               P' = Evolve(P)
        PROVE  PTypeOK'
    BY <1>2 DEF L1, Evolve
  <1>3. ASSUME NEW p \in ProcSet,
               L2(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  PTypeOK'
    BY <1>3 DEF L2, Evolve, Filter
  <1>4. ASSUME NEW p \in ProcSet,
               L3(p),
               P' = Evolve(P)
        PROVE  PTypeOK'
    BY <1>4 DEF L3, Evolve
  <1>5. ASSUME NEW p \in ProcSet,
               L4(p),
               P' = Evolve(P)
        PROVE  PTypeOK'
    BY <1>5 DEF L4, Evolve
  <1>6. ASSUME NEW p \in ProcSet,
               L5(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  PTypeOK'
    BY <1>6 DEF L5, Evolve, Filter
  <1>7. CASE UNCHANGED vars
    BY <1>7 DEF vars
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next, IntLine, IntLines, RetLine, RetLines

TypeOK == /\ PTypeOK
          /\ X \in StateDomain
          /\ x \in [ProcSet -> StateDomain]
          /\ arg \in [ProcSet -> StateDomain]
          /\ ret \in [ProcSet -> RetDomain]
          /\ pc \in [ProcSet -> LineIDs]

LEMMA InitTypeOK == AInit => TypeOK
  BY InitPTypeOK, NonEmptyStateDomain DEF AInit, Init, InitState, TypeOK, LineIDs

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
  <1> USE RemDef, NonEmptyStateDomain DEF TypeOK, ArgsOf, LineIDs, OpNames, OpToInvocLine, 
                                          ConfigDomain, OpDomain, ArgDomain, ResDomain, RetDomain, algvars
  <1> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. ASSUME NEW p \in ProcSet,
               L0(p)
        PROVE  TypeOK'
    BY <1>1, NextPTypeOK DEF L0
  <1>2. ASSUME NEW p \in ProcSet,
               L1(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    BY <1>2, NextPTypeOK DEF L1
  <1>3. ASSUME NEW p \in ProcSet,
               L2(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  TypeOK'
    BY <1>3, NextPTypeOK DEF L2
  <1>4. ASSUME NEW p \in ProcSet,
               L3(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    BY <1>4, NextPTypeOK DEF L3
  <1>5. ASSUME NEW p \in ProcSet,
               L4(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    BY <1>5, NextPTypeOK DEF L4
  <1>6. ASSUME NEW p \in ProcSet,
               L5(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE TypeOK'
    BY <1>6, NextPTypeOK DEF L5
  <1>7. CASE UNCHANGED vars
    BY <1>7, NextPTypeOK DEF vars
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next, IntLine, IntLines, RetLine, RetLines

S == {c \in ConfigDomain : /\ c.state = X
                           /\ \A p \in ProcSet : /\ (pc[p] = "L0" => /\ c.op[p]  = BOT
                                                                     /\ c.arg[p] = BOT
                                                                     /\ c.res[p] = BOT)
                                                 /\ (pc[p] = "L1" => /\ c.op[p]  = "R"
                                                                     /\ c.arg[p] = BOT
                                                                     /\ c.res[p] = BOT)
                                                 /\ (pc[p] = "L2" => /\ c.op[p]  = "R"
                                                                     /\ c.arg[p] = BOT
                                                                     /\ c.res[p] = x[p])
                                                 /\ (pc[p] = "L3" => /\ c.op[p]  = "W"
                                                                     /\ c.arg[p] = arg[p]
                                                                     /\ c.res[p] = BOT)
                                                 /\ (pc[p] = "L4" => \/ /\ c.op[p]  = "W"
                                                                        /\ c.arg[p] = arg[p]
                                                                        /\ c.res[p] = BOT
                                                                     \/ /\ X # x[p]
                                                                        /\ c.op[p]  = "W"
                                                                        /\ c.arg[p] = arg[p]
                                                                        /\ c.res[p] = ACK)
                                                 /\ (pc[p] = "L5" => /\ c.op[p]  = "W"
                                                                     /\ c.arg[p] = arg[p]
                                                                     /\ c.res[p] = ACK)}

Inv0 == IsFiniteSet({q \in ProcSet : pc[q] # "L0"})                                                     
Inv1 == S \in SUBSET P
Inv2 == S # {}

Inv == /\ TypeOK
       /\ Inv0
       /\ Inv1
       /\ Inv2

THEOREM Spec => []Inv
  <1>1. AInit => Inv
    <2> USE RemDef, NonEmptyStateDomain DEF Inv, AInit, Init
    <2> SUFFICES ASSUME AInit
                 PROVE  Inv
      OBVIOUS
    <2>1. TypeOK
      BY InitTypeOK
    <2>2. Inv0
      BY Isa DEF Inv0, IsFiniteSet
    <2>3. Inv1
      BY DEF Inv1, S, ConfigDomain
    <2>4. Inv2
      <3> DEFINE c == [state |-> X, 
                       op    |-> [p \in ProcSet |-> BOT], 
                       arg   |-> [p \in ProcSet |-> BOT], 
                       res   |-> [p \in ProcSet |-> BOT]]
      <3>1. \A p \in ProcSet : /\ pc[p] = "L0"
                               /\ c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
        OBVIOUS
      <3>2. c \in ConfigDomain
        BY DEF ConfigDomain, OpDomain, ArgDomain, ResDomain, InitState
      <3>3. c \in S
        BY <3>1, <3>2 DEF S
      <3> QED
        BY <3>3 DEF Inv2
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4
  <1>2. Inv /\ [Next]_vars => Inv'
    <2> USE RemDef DEF Inv, LineIDs
    <2> SUFFICES ASSUME Inv /\ [Next]_vars
                 PROVE  Inv'
      OBVIOUS
    <2>1. TypeOK'
      BY NextTypeOK
    <2>2. Inv0'
      <3> USE DEF Inv0
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv0'
        <4> USE <3>1 DEF L0
        <4>1. \A q \in ProcSet : pc'[q] # "L0" => (p = q \/ pc[q] # "L0")
          BY DEF TypeOK
        <4>2. \A r \in ProcSet : r \in {q \in ProcSet : pc'[q] # "L0"} => r \in {q \in ProcSet : pc[q] # "L0"} \/ r \in {p}
          BY <4>1
        <4>3. \A r \in ProcSet : r \in {q \in ProcSet : pc'[q] # "L0"} => r \in {q \in ProcSet : pc[q] # "L0" \/ q = p}
          BY <4>2
        <4>4. {q \in ProcSet : pc'[q] # "L0"} \in SUBSET {q \in ProcSet : pc[q] # "L0" \/ q = p}
          BY <4>3
        <4>5. {q \in ProcSet : pc[q] # "L0" \/ q = p} = {q \in ProcSet : pc[q] # "L0"} \union {p}
          OBVIOUS
        <4>6. IsFiniteSet({q \in ProcSet : pc[q] # "L0"} \union {p})
          BY Zenon, FS_Union, FS_Singleton
        <4>7. IsFiniteSet({q \in ProcSet : pc'[q] # "L0"})
          BY FS_Subset, <4>4, <4>6
        <4> QED
          BY <4>7
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p)
            PROVE  Inv0'
        BY <3>2 DEF L1
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p)
            PROVE  Inv0'
        BY <3>3, FS_Subset DEF L2
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  Inv0'
        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  Inv0'
        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  Inv0'
        BY <3>6, FS_Subset DEF L5
      <3>7. CASE UNCHANGED vars
        BY <3>7 DEF vars, algvars
      <3>8. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>3. Inv1'
      <3> USE DEF Inv1
      <3>0. SUFFICES ASSUME NEW c \in S'
                     PROVE  c \in P'
        BY DEF Inv1
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  c \in P'
        <4> USE <3>1 DEF L0
        <4>1. CASE pc'[p] = "L1"
          <5> USE <4>1
          <5>1. c \in ConfigDomain
            BY DEF S
          <5>2. \A q \in ProcSet :
                  /\ ((pc[q] = "L0" /\ q # p) => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ ((pc[q] = "L1" \/ q = p) => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                  /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                  /\ (pc[q] = "L4" => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                       \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                  /\ (pc[q] = "L5" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
            BY DEF S, OpToInvocLine, TypeOK, algvars
          <5> DEFINE c_prev == [state |-> c.state,
                                op    |-> [c.op EXCEPT ![p] = BOT],
                                arg   |-> [c.arg EXCEPT ![p] = BOT],
                                res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>3. c_prev \in ConfigDomain
            BY <5>1 DEF ConfigDomain, OpDomain, ArgDomain, ResDomain
          <5>4. c_prev.state = X
            BY <5>1 DEF S, OpToInvocLine, OpNames, ArgsOf, TypeOK, algvars
          <5>5. \A q \in ProcSet : (pc[q] = "L0" => (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
            BY <5>1, <5>2 DEF TypeOK, ConfigDomain
          <5>6. \A q \in ProcSet : /\ (pc[q] = "L1" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
                                   /\ (pc[q] = "L2" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = x[q]))
                                   /\ (pc[q] = "L3" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT))
                                   /\ (pc[q] = "L4" => (\/ (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                                        \/ (X # x[q] /\ c_prev.op[q]  = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)))
                                   /\ (pc[q] = "L5" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK))
            BY <5>2
          <5>7. c_prev \in S
            BY Zenon, <5>3, <5>4, <5>5, <5>6 DEF S
          <5>8. c_prev \in P
            BY <5>7 DEF Inv1
          <5>9. c_prev.op[p] = BOT /\ c_prev.arg[p] = BOT /\ c_prev.res[p] = BOT
            BY <5>1 DEF ConfigDomain
          <5>10. c.op = [c_prev.op EXCEPT ![p] = "R"]
            BY Zenon, <5>1, <5>2 DEF ConfigDomain
          <5>11. c.arg = [c_prev.arg EXCEPT ![p] = BOT]
            BY Zenon, <5>1, <5>2 DEF ConfigDomain
          <5>12. c.res = [c_prev.res EXCEPT ![p] = BOT]
            BY Zenon, <5>1, <5>2 DEF ConfigDomain
          <5>13. c \in Invoke(P, p, "R", BOT)
            BY Zenon, <5>1, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Invoke
          <5> DEFINE alpha == << >>
          <5> DEFINE beta  == <<c>>
          <5> DEFINE n     == 0
          <5>14. c \in ConfigDomain
            BY <5>1
          <5>15. c \in Invoke(P, p, "R", BOT)
            BY <5>13
          <5>16. n \in Nat
            OBVIOUS
          <5>17. alpha \in Seq(ProcSet)
            OBVIOUS
          <5>18. beta \in Seq(ConfigDomain)
            BY <5>1
          <5>19. Len(alpha) = n
            OBVIOUS
          <5>20. Len(beta) = n+1
            OBVIOUS
          <5>21. beta[1] = c
            OBVIOUS
          <5>22. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
            OBVIOUS
          <5>23. beta[n+1] = c
            OBVIOUS
          <5>24. c \in Evolve(Invoke(P, p, "R", BOT))
            <6> SUFFICES ASSUME TRUE
                         PROVE  /\ c \in ConfigDomain
                                /\ \E poss_old \in Invoke(P, p, "R", BOT) : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY DEF Evolve
            <6> QED
              BY ZenonT(10), <5>14, <5>15, <5>16, <5>17, <5>18, <5>19, <5>20, <5>21, <5>22, <5>23
          <5> QED
            BY <5>24 DEF OpNames, ArgsOf, OpToInvocLine
        <4>2. CASE pc'[p] = "L3"
          <5> USE <4>2
          <5>A. PICK op \in {"R", "W"} : /\ pc' = [pc EXCEPT ![p] = CASE op = "R" -> "L1"
                                                                      [] op = "W" -> "L3"]
                                         /\ \E arg_val \in ArgsOf(op) : /\ P' = Evolve(Invoke(P, p, op, arg_val))
                                                                        /\ IF arg_val # BOT
                                                                              THEN arg' = [arg EXCEPT ![p] = arg_val]
                                                                              ELSE arg' = arg
            BY Zenon DEF OpNames, OpToInvocLine
          <5>0. PICK arg_val \in StateDomain : /\ P' = Evolve(Invoke(P, p, op, arg_val))
                                               /\ arg' = [arg EXCEPT ![p] = arg_val]
            BY <5>A, AckBotDef DEF ArgsOf
          <5>1. c \in ConfigDomain
            BY DEF S
          <5>2. \A q \in ProcSet :
                  /\ ((pc[q] = "L0" /\ q # p) => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                  /\ ((pc[q] = "L3" \/ q = p) => (c.op[q] = "W" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT))
                  /\ (pc[q] = "L4" => (\/ (c.op[q] = "W" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
                                       \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg'[q] /\ c.res[q] = ACK)))
                  /\ (pc[q] = "L5" => (c.op[q] = "W" /\ c.arg[q] = arg'[q] /\ c.res[q] = ACK))
            BY Zenon DEF S, OpToInvocLine, TypeOK, algvars
          <5> DEFINE c_prev == [state |-> c.state,
                                op    |-> [c.op EXCEPT ![p] = BOT],
                                arg   |-> [c.arg EXCEPT ![p] = BOT],
                                res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>3. c_prev \in ConfigDomain
            BY <5>1 DEF ConfigDomain, OpDomain, ArgDomain, ResDomain, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5>4. c_prev.state = X
            BY <5>1 DEF S, algvars
          <5>5. \A q \in ProcSet : (pc[q] = "L0" => (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
            BY <5>1, <5>2 DEF TypeOK, ConfigDomain, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5>6. \A q \in ProcSet : /\ (pc[q] = "L1" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
                                   /\ (pc[q] = "L2" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = x[q]))
                                   /\ (pc[q] = "L3" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT))
                                   /\ (pc[q] = "L4" => (\/ (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                                        \/ (X # x[q] /\ c_prev.op[q]  = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)))
                                   /\ (pc[q] = "L5" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK))
            BY <5>0, <5>2
          <5>7. c_prev \in S
            BY Zenon, <5>3, <5>4, <5>5, <5>6 DEF S, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5>8. c_prev \in P
            BY <5>7 DEF Inv1
          <5>9. c_prev.op[p] = BOT /\ c_prev.arg[p] = BOT /\ c_prev.res[p] = BOT
            BY <5>1 DEF ConfigDomain, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5>10. c.op = [c_prev.op EXCEPT ![p] = "W"]
            BY Zenon, <5>1, <5>2 DEF ConfigDomain
          <5>11. c.arg = [c_prev.arg EXCEPT ![p] = arg_val]
            BY Zenon, <5>0, <5>1, <5>2 DEF ConfigDomain, TypeOK
          <5>12. c.res = [c_prev.res EXCEPT ![p] = BOT]
            BY Zenon, <5>1, <5>2 DEF ConfigDomain
          <5>13. c \in Invoke(P, p, "W", arg_val)
            BY Zenon, <5>1, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Invoke, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> DEFINE alpha == << >>
          <5> DEFINE beta  == <<c>>
          <5> DEFINE n     == 0
          <5>14. c \in ConfigDomain
            BY <5>1
          <5>15. c \in Invoke(P, p, "W", arg_val)
            BY <5>13
          <5>16. n \in Nat
            OBVIOUS
          <5>17. alpha \in Seq(ProcSet)
            OBVIOUS
          <5>18. beta \in Seq(ConfigDomain)
            BY <5>1
          <5>19. Len(alpha) = n
            OBVIOUS
          <5>20. Len(beta) = n+1
            OBVIOUS
          <5>21. beta[1] = c
            OBVIOUS
          <5>22. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
            OBVIOUS
          <5>23. beta[n+1] = c
            OBVIOUS
          <5>24. c \in Evolve(Invoke(P, p, "W", arg_val))
            <6> SUFFICES ASSUME TRUE
                         PROVE  /\ c \in ConfigDomain
                                /\ \E poss_old \in Invoke(P, p, "W", arg_val) : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY DEF Evolve
            <6> QED
              BY ZenonT(10), <5>14, <5>15, <5>16, <5>17, <5>18, <5>19, <5>20, <5>21, <5>22, <5>23
          <5> QED
            BY <5>A, <5>0, <5>24 DEF OpNames, ArgsOf, OpToInvocLine
        <4> QED
          BY <4>1, <4>2 DEF OpNames, OpToInvocLine, TypeOK
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>2 DEF L1
        <4>1. c \in ConfigDomain
          BY DEF S
        <4>2. \A q \in ProcSet :
                  /\ (pc[q] = "L0" => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ ((pc[q] = "L1" /\ p # q) => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ ((pc[q] = "L2" \/ p = q) => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x'[q]))
                  /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                  /\ (pc[q] = "L4" => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                        \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                  /\ (pc[q] = "L5" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
          BY DEF S, TypeOK
        <4> DEFINE c_prev == [state |-> c.state,
                              op    |-> c.op,
                              arg   |-> c.arg,
                              res   |-> [c.res EXCEPT ![p] = BOT]]
        <4>3. c_prev \in ConfigDomain
          BY <4>1 DEF ConfigDomain, ResDomain
        <4>4. c_prev.state = X
          BY DEF S
        <4>5. \A q \in ProcSet : /\ (pc[q] = "L0" => (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L2" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = x[q]))
                                 /\ (pc[q] = "L3" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L4" => (\/ (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                                      \/ (X # x[q] /\ c_prev.op[q]  = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)))
                                 /\ (pc[q] = "L5" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK))
          BY <4>2 DEF TypeOK
        <4>6. \A q \in ProcSet : (pc[q] = "L1" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
          BY <4>1, <4>2 DEF ConfigDomain, ResDomain
        <4>7. c_prev \in S
          BY Zenon, <4>3, <4>4, <4>5, <4>6 DEF S
        <4>8. c_prev \in P
          BY <4>7 DEF Inv1
        <4> DEFINE alpha == <<p>>
        <4> DEFINE beta  == <<c_prev, c>>
        <4> DEFINE n     == 1
        <4>9. n \in Nat
          OBVIOUS
        <4>10. alpha \in Seq(ProcSet)
          OBVIOUS
        <4>11. beta \in Seq(ConfigDomain)
          BY <4>1, <4>3
        <4>12. Len(alpha) = n
          OBVIOUS
        <4>13. Len(beta) = n+1
          OBVIOUS
        <4>14. beta[1] = c_prev
          OBVIOUS
        <4>15. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
          <5>1. SUFFICES ASSUME TRUE
                         PROVE  Delta(c_prev, p, c)
            OBVIOUS
          <5> USE <5>1
          <5>2. c_prev.op[p] = "R" /\ c_prev.arg[p] = BOT /\ c_prev.res[p] = BOT
            BY <4>1, <4>2 DEF ConfigDomain, ResDomain
          <5>3. c.state = c_prev.state /\ c.op = c_prev.op /\ c.arg = c_prev.arg 
            OBVIOUS
          <5>4. c.res[p] = c.state
            BY <4>2, <4>4 DEF TypeOK
          <5>5. c.res = [c_prev.res EXCEPT ![p] = c.state]
            BY Zenon, <5>4, <4>3, <4>1 DEF ConfigDomain, ResDomain
          <5> QED
            BY <5>2, <5>4, <5>5 DEF Delta, ArgsOf
        <4>16. beta[n+1] = c
          OBVIOUS
        <4>17. c \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  /\ c \in ConfigDomain
                              /\ \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
            BY Zenon DEF Evolve
          <5> QED
            BY Zenon, <4>1, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16
        <4> QED
          BY <4>17
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p), 
                   P' = Filter(Evolve(P), p, (ret')[p])
            PROVE  c \in P'
        <4> USE <3>3 DEF L2
        <4>0. ret'[p] = x[p]
          BY DEF TypeOK
        <4> USE <4>0
        <4>1. c \in ConfigDomain
          BY DEF S
        <4>2. \A q \in ProcSet :
                  /\ ((pc[q] = "L0" \/ p = q) => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ ((pc[q] = "L2" /\ p # q) => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                  /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                  /\ (pc[q] = "L4" => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                        \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                  /\ (pc[q] = "L5" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
          BY DEF S, TypeOK
        <4> DEFINE c_prev == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "R"],
                              arg   |-> c.arg,
                              res   |-> [c.res EXCEPT ![p] = x[p]]]
        <4>3. c_prev \in ConfigDomain
          BY <4>1 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
        <4>4. c_prev.state = X
          BY DEF S
        <4>5. \A q \in ProcSet : /\ (pc[q] = "L0" => (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L1" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L3" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L4" => (\/ (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                                      \/ (X # x[q] /\ c_prev.op[q]  = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)))
                                 /\ (pc[q] = "L5" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK))
         BY <4>2
        <4>6. \A q \in ProcSet : pc[q] = "L2" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = x[q])
          BY <4>1, <4>2 DEF TypeOK, ConfigDomain
        <4>7. c_prev \in S
          BY Zenon, <4>3, <4>4, <4>5, <4>6 DEF S
        <4>8. c_prev \in P
          BY <4>7 DEF Inv1
        <4> DEFINE alpha == << >>
        <4> DEFINE beta  == <<c_prev>>
        <4> DEFINE n     == 0
        <4>9. n \in Nat
          OBVIOUS
        <4>10. alpha \in Seq(ProcSet)
          OBVIOUS
        <4>11. beta \in Seq(ConfigDomain)
          BY <4>3
        <4>12. Len(alpha) = n
          OBVIOUS
        <4>13. Len(beta) = n+1
          OBVIOUS
        <4>14. beta[1] = c_prev
          OBVIOUS
        <4>15. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
          OBVIOUS
        <4>16. beta[n+1] = c_prev
          OBVIOUS
        <4>17. c_prev \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c_prev
            BY <4>3, Zenon DEF Evolve
          <5> QED
            BY Zenon, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16
        <4>18. c_prev.res[p] = x[p]
          BY <4>1 DEF ConfigDomain
        <4>19. c.op = [c_prev.op EXCEPT ![p] = BOT]
          BY <4>2, <4>3 DEF ConfigDomain
        <4>20. c.arg = [c_prev.arg EXCEPT ![p] = BOT]
          BY <4>2, <4>3 DEF ConfigDomain
        <4>21. c.res = [c_prev.res EXCEPT ![p] = BOT]
          BY <4>2, <4>3 DEF ConfigDomain
        <4>22. c.state = c_prev.state
          OBVIOUS
        <4>23. c \in Filter(Evolve(P), p, x[p])
          BY Zenon, <4>1, <4>17, <4>18, <4>19, <4>20, <4>21, <4>22 DEF Filter
        <4> QED
          BY <4>23
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>4 DEF L3
        <4>1. c \in ConfigDomain
          BY DEF S
        <4>2. \A q \in ProcSet :
                  /\ (pc[q] = "L0" => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                  /\ ((pc[q] = "L3" /\ q # p) => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                  /\ ((pc[q] = "L4" \/ q = p) => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                                  \/ (X # x'[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                  /\ (pc[q] = "L5" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
          BY DEF S, TypeOK
        <4>3. X = x'[p]
          BY DEF TypeOK
        <4>4. c.op[p] = "W" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
          BY <4>2, <4>3
        <4>5. \A q \in ProcSet :
                  /\ (pc[q] = "L0" => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                  /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                  /\ (pc[q] = "L4" => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                       \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                  /\ (pc[q] = "L5" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
          BY <4>2, <4>4
        <4>6. c \in S
          BY <4>5 DEF S
        <4>7. c \in P
          BY <4>6 DEF Inv1
        <4> DEFINE alpha == << >>
        <4> DEFINE beta  == <<c>>
        <4> DEFINE n     == 0
        <4>8. n \in Nat
          OBVIOUS
        <4>9. alpha \in Seq(ProcSet)
          OBVIOUS
        <4>10. beta \in Seq(ConfigDomain)
          BY <4>1
        <4>11. Len(alpha) = n
          OBVIOUS
        <4>12. Len(beta) = n+1
          OBVIOUS
        <4>13. beta[1] = c
          OBVIOUS
        <4>14. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
          OBVIOUS
        <4>15. beta[n+1] = c
          OBVIOUS
        <4>16. c \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
            BY <4>1 DEF Evolve
          <5> QED
            BY Zenon, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
        <4> QED
          BY <4>16
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>5 DEF L4
        <4>1. CASE X = x[p] 
          <5> USE <4>1
          <5> DEFINE c_prev == [state |-> X,
                                op    |-> c.op,
                                arg   |-> c.arg,
                                res   |-> [q \in ProcSet |-> IF pc[q] = "L4" THEN BOT ELSE c.res[q]]]
          <5>1. c_prev \in ConfigDomain
            BY DEF ConfigDomain, ResDomain, S, TypeOK
          <5>2. \A q \in ProcSet :
                    /\ (pc[q] = "L0" => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                    /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                    /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                    /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                    /\ ((pc[q] = "L4" /\ p # q) => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                                    \/ (X' # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                    /\ ((pc[q] = "L5" \/ p = q) => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
            BY DEF S, TypeOK
          <5>3. \A q \in ProcSet : 
                    /\ (pc[q] = "L0" => (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = BOT))
                    /\ (pc[q] = "L1" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = BOT))
                    /\ (pc[q] = "L2" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = x[q]))
                    /\ (pc[q] = "L3" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT))
                    /\ (pc[q] = "L4" => (\/ (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                         \/ (X # x[q] /\ c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)))
                    /\ (pc[q] = "L5" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK))
            BY <5>2 DEF TypeOK
          <5>4. c_prev \in S
            BY <5>1, <5>3 DEF S
          <5>5. c_prev \in P
            BY <5>4 DEF Inv1
          <5> LinProcSet == {q \in ProcSet : pc[q] = "L4" /\ c.res[q] # BOT /\ q # p}
          <5>6. IsFiniteSet(LinProcSet)
            BY FS_Subset DEF Inv0, TypeOK
          <5>7. PICK seq \in Seq(LinProcSet) : /\ Len(seq) = Cardinality(LinProcSet)
                                               /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
            BY Zenon, FS_Permutation, <5>6 DEF Perm
          <5> DEFINE alpha == seq \o <<p>>
          <5> DEFINE n == Len(alpha)
          <5> DEFINE bseq == [i \in 1..n+1 |-> CASE i = 1 -> c_prev
                                                 [] OTHER -> [state |-> arg[alpha[i-1]], 
                                                              op    |-> c_prev.op,
                                                              arg   |-> c_prev.arg,
                                                              res   |-> [q \in ProcSet |-> IF q \in Range(SubSeq(alpha, 1, i-1))
                                                                                              THEN ACK
                                                                                              ELSE c_prev.res[q]]]]
          <5>8. bseq \in Seq(ConfigDomain)
            BY <5>1 DEF ConfigDomain, ResDomain, TypeOK
          <5>9. bseq[1] = c_prev
            OBVIOUS
          <5>10. Len(bseq) = n+1
            OBVIOUS
          <5>11. \A j \in 1..n : /\ bseq[j+1].state = arg[alpha[j]]
                                 /\ bseq[j+1].op = bseq[j].op
                                 /\ bseq[j+1].arg = bseq[j].arg
                                 /\ bseq[j+1].res = [bseq[j].res EXCEPT ![alpha[j]] = ACK]
            <6> SUFFICES ASSUME NEW j \in 1..n
                         PROVE  /\ bseq[j+1].state = arg[alpha[j]]
                                /\ bseq[j+1].op = bseq[j].op
                                /\ bseq[j+1].arg = bseq[j].arg
                                /\ bseq[j+1].res = [bseq[j].res EXCEPT ![alpha[j]] = ACK]
              BY Zenon
            <6>1. bseq[j].op = c_prev.op /\ bseq[j].arg = c_prev.arg
              OBVIOUS
            <6>2. c_prev.op[alpha[j]] = "W" /\ c_prev.arg[alpha[j]] = arg[alpha[j]] /\ c_prev.arg[alpha[j]] \in ArgDomain
              BY <5>3 DEF ArgDomain, TypeOK
            <6>3. alpha[j] \notin Range(SubSeq(alpha, 1, j-1)) => bseq[j].res[alpha[j]] = BOT
              BY <5>3 
            <6>4. alpha[j] \notin Range(SubSeq(alpha, 1, j-1))
              BY <5>7 DEF Range, SubSeq
            <6>5. bseq[j].res[alpha[j]] = BOT
              BY <6>3, <6>4, Zenon
            <6>6. bseq[j+1].state = arg[alpha[j]]
              OBVIOUS
            <6>7. bseq[j+1].state = bseq[j].arg[alpha[j]]
              <7> HIDE DEF alpha, bseq
              <7> QED 
                BY <6>1, <6>2, <6>6
            <6>8. bseq[j+1].op = bseq[j].op
              OBVIOUS
            <6>9. bseq[j+1].arg = bseq[j].arg
              OBVIOUS
            <6>10. bseq[j+1].res = [bseq[j].res EXCEPT ![alpha[j]] = ACK]
              <7>0. j+1 # 1
                OBVIOUS
              <7>1. bseq[j+1].res = [q \in ProcSet |-> IF q \in Range(SubSeq(alpha, 1, j)) THEN ACK ELSE c_prev.res[q]]
                <8> HIDE DEF c_prev
                <8> QED  BY <7>0
              <7>2. CASE j = 1
                <8> USE <7>2
                <8>1. bseq[j] = c_prev
                  OBVIOUS
                <8>2. Range(SubSeq(alpha, 1, 1)) = {alpha[j]}
                  BY DEF Range, SubSeq
                <8>3. bseq[j+1].res = [q \in ProcSet |-> IF q = alpha[j] THEN ACK ELSE c_prev.res[q]]
                  BY <7>1, <8>2, Zenon
                <8>4. bseq[j+1].res = [c_prev.res EXCEPT ![alpha[j]] = ACK]
                  BY <5>8, <8>1, <8>3 DEF ConfigDomain, ResDomain, Zenon
                <8>5. c_prev = bseq[j]
                  OBVIOUS
                <8> QED
                  BY <8>4, <8>5, Zenon
              <7>3. CASE j # 1
                <8> USE <7>3
                <8>1. bseq[j].res = [q \in ProcSet |-> IF q \in Range(SubSeq(alpha, 1, j-1)) THEN ACK ELSE c_prev.res[q]]
                  OBVIOUS
                <8>2. bseq[j+1].res = [q \in ProcSet |-> IF q \in Range(SubSeq(alpha, 1, j)) THEN ACK ELSE c_prev.res[q]]
                  BY <7>1
                <8>3. SubSeq(alpha, 1, j) = [i \in 1..j |-> alpha[i]]
                  OBVIOUS
                <8>4. SubSeq(alpha, 1, j-1) = [i \in 1..j-1 |-> alpha[i]]
                  OBVIOUS
                <8>5. Range(SubSeq(alpha, 1, j)) = {alpha[i] : i \in 1..j}
                  BY <8>3, Zenon DEF Range
                <8>6. Range(SubSeq(alpha, 1, j-1)) = {alpha[i] : i \in 1..j-1}
                  BY <8>4, Zenon DEF Range
                <8>7. Range(SubSeq(alpha, 1, j-1)) \in SUBSET Range(SubSeq(alpha, 1, j))
                  BY <8>5, <8>6
                <8>8. \A q \in Range(SubSeq(alpha, 1, j)) : q \notin Range(SubSeq(alpha, 1, j-1)) => q = alpha[j]
                  BY <8>5, <8>6
                <8>9. \A q \in ProcSet : (q \in Range(SubSeq(alpha, 1, j)) /\ q \notin Range(SubSeq(alpha, 1, j-1))) => q = alpha[j]
                  BY <8>8
                <8>10. \A q \in ProcSet : (q \in Range(SubSeq(alpha, 1, j-1)) => q \in Range(SubSeq(alpha, 1, j)))
                  BY <8>7
                <8>11. \A q \in ProcSet : q # alpha[j] => bseq[j].res[q] = bseq[j+1].res[q]
                  BY <8>9, <8>10
                <8>12. bseq[j+1].res[alpha[j]] = ACK
                  <9> HIDE DEF c_prev
                  <9> QED  BY Z3T(10) DEF Range, SubSeq
                <8> HIDE DEF alpha, bseq
                <8>13. bseq[j+1].res = [bseq[j].res EXCEPT ![alpha[j]] = ACK]
                  BY <8>1, <8>2, <8>11, <8>12
                <8> QED
                  BY <8>13
              <7> HIDE DEF alpha, bseq
              <7> QED
                BY <7>2, <7>3
            <6> HIDE DEF alpha, bseq
            <6> QED
              BY <6>6, <6>8, <6>9, <6>10
          <5>12. \A j \in 1..n : Delta(bseq[j], alpha[j], bseq[j+1])
            <6> SUFFICES ASSUME NEW j \in 1..n
                         PROVE  Delta(bseq[j], alpha[j], bseq[j+1])
              BY Zenon
            <6>1. bseq[j].op = c_prev.op /\ bseq[j].arg = c_prev.arg
              OBVIOUS
            <6>2. c_prev.op[alpha[j]] = "W" /\ c_prev.arg[alpha[j]] = arg[alpha[j]] /\ c_prev.arg[alpha[j]] \in ArgsOf("W")
              BY <5>3 DEF ArgDomain, TypeOK, ArgsOf
            <6>3. alpha[j] \notin Range(SubSeq(alpha, 1, j-1)) => bseq[j].res[alpha[j]] = BOT
              BY <5>3 
            <6>4. alpha[j] \notin Range(SubSeq(alpha, 1, j-1))
              BY <5>7 DEF Range, SubSeq
            <6>5. bseq[j].res[alpha[j]] = BOT
              BY <6>3, <6>4, Zenon
            <6> HIDE DEF alpha, bseq
            <6>6. Delta(bseq[j], alpha[j], bseq[j+1])
              BY <6>1, <6>2, <6>5, <5>11 DEF Delta
            <6> QED
              BY <6>6
          <5>13. n \in 1..n => bseq[n+1].state = arg[alpha[n]]
            OBVIOUS
          <5>14. n \in 1..n
            OBVIOUS
          <5>15. bseq[n+1].state = arg[p]
            BY <5>13, <5>14
          <5>16. c \in ConfigDomain /\ c.state = arg[p]
            BY DEF S
          <5>17. c.op = bseq[n+1].op /\ c.arg = bseq[n+1].arg
            OBVIOUS
          <5>18. Range(SubSeq(alpha, 1, n)) = LinProcSet \cup {p}
            <6>1. SubSeq(alpha, 1, n-1) = [i \in 1..n-1 |-> alpha[i]]
              OBVIOUS
            <6>2. Range(SubSeq(alpha, 1, n-1)) = {alpha[i] : i \in 1..n-1}
              BY <6>1, Zenon DEF Range
            <6>3. \A z \in {alpha[i] : i \in 1..n-1} : z \in LinProcSet
              BY DEF Seq
            <6>4. \A z \in LinProcSet : z \in {alpha[i] : i \in 1..n-1}
              <7> SUFFICES ASSUME NEW q \in LinProcSet,
                                  \A i \in 1..n-1 : q # alpha[i]
                           PROVE  FALSE
                OBVIOUS
              <7>1. /\ IsFiniteSet(Range(seq)) 
                    /\ IsFiniteSet(LinProcSet) 
                    /\ Cardinality(Range(seq)) < Cardinality(LinProcSet)
                BY FS_CardinalityType, FS_Subset, Inv0 DEF Inv0, Range 
              <7>2. Cardinality(Range(seq)) < Len(seq)
                BY <5>7, <7>1
              <7>3. seq \in [1..Len(seq) -> Range(seq)]
                BY DEF Range
              <7>4. IsFiniteSet(1..Len(seq))
                BY FS_Interval
              <7>5. Cardinality(1..Len(seq)) = Len(seq)
                BY FS_Interval
              <7>6. Cardinality(Range(seq)) < Cardinality(1..Len(seq))
                BY <7>2, <7>5
              <7>7. IsFiniteSet(Range(seq))
                BY <7>1
              <7>8. \E z,y \in 1..Len(seq) : z # y /\ seq[z] = seq[y]
                BY <7>4, <7>7, <7>6, <7>3, FS_PigeonHole
              <7> QED
                BY <5>7, <7>8
            <6>5. Range(SubSeq(alpha, 1, n-1)) = LinProcSet 
              BY <6>2, <6>3, <6>4
            <6>6. SubSeq(alpha, 1, n) = [i \in 1..n |-> alpha[i]]
              OBVIOUS
            <6>7. Range(SubSeq(alpha, 1, n)) = {alpha[i] : i \in 1..n}
              BY <6>6, Zenon DEF Range
            <6>8. Range(SubSeq(alpha, 1, n)) = {alpha[i] : i \in 1..n-1} \cup {alpha[n]}
              BY <6>7
            <6> QED
              BY <6>4, <6>8
          <5>19. \A q \in LinProcSet \cup {p} : (q \in LinProcSet \/ q \in {p})
            OBVIOUS
          <5>20. c.res[p] # BOT
            BY AckBotDef DEF S, TypeOK
          <5>21. LinProcSet \cup {p} = {r \in ProcSet : pc[r] = "L4" /\ c.res[r] # BOT}
            BY <5>19, <5>20
          <5>22. bseq[n+1].res = [q \in ProcSet |-> IF q \in {r \in ProcSet : pc[r] = "L4" /\ c.res[r] # BOT} THEN ACK ELSE c_prev.res[q]]
            BY <5>18, <5>21
          <5>23. bseq[n+1].res = [q \in ProcSet |-> IF pc[q] = "L4" /\ c.res[q] # BOT THEN ACK ELSE c_prev.res[q]]
            BY <5>22
          <5>24. \A q \in ProcSet : pc[q] = "L4" /\ c.res[q] # BOT => c.res[q] = ACK
            BY DEF S
          <5> HIDE DEF bseq
          <5>25. bseq \in Seq(ConfigDomain)
            BY <5>8
          <5>26. bseq \in [1..n+1 -> ConfigDomain]
            BY <5>25, <5>10 DEF Seq
          <5>27. bseq[n+1].res \in [ProcSet -> ResDomain]
            BY <5>26 DEF ConfigDomain
          <5>28. c.res \in [ProcSet -> ResDomain]
            BY DEF S, ConfigDomain
          <5>29. bseq[n+1].res = c.res
            BY <5>27, <5>28, <5>23 DEF S
          <5>30. (bseq[n+1] \in ConfigDomain) => bseq[n+1] = c
            BY <5>15, <5>16, <5>17, <5>29 DEF ConfigDomain
          <5>31. bseq[n+1] = c
            BY <5>30, <5>26
          <5>32. c \in ConfigDomain
            BY DEF S
          <5>33. alpha \in Seq(ProcSet)
            BY <5>7
          <5>34. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                         PROVE  /\ c \in ConfigDomain
                                /\ \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY Zenon DEF Evolve
            <6> HIDE DEF alpha, bseq
            <6> QED
              BY Z3T(10), <5>32, <5>5, <5>33, <5>25, <5>10, <5>9, <5>12, <5>31
          <5> QED
            BY <5>34
        <4>2. CASE X # x[p]
          <5> USE <4>2
          <5>1. c \in ConfigDomain
            BY DEF S
          <5>2. \A q \in ProcSet :
                    /\ (pc[q] = "L0" => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                    /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                    /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                    /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                    /\ ((pc[q] = "L4" /\ p # q) => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                                    \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                    /\ ((pc[q] = "L5" \/ p = q) => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
            BY DEF S, TypeOK
          <5>3. c \in S
            BY <5>1, <5>2 DEF S
          <5>4. c \in P
            BY <5>3 DEF Inv1 
          <5> DEFINE alpha == << >>
          <5> DEFINE beta  == <<c>>
          <5> DEFINE n     == 0
          <5>5. n \in Nat
            OBVIOUS
          <5>6. alpha \in Seq(ProcSet)
            OBVIOUS
          <5>7. beta \in Seq(ConfigDomain)
            BY <5>1
          <5>8. Len(alpha) = n
            OBVIOUS
          <5>9. Len(beta) = n+1
            OBVIOUS
          <5>10. beta[1] = c
            OBVIOUS
          <5>11. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
            OBVIOUS
          <5>12. beta[n+1] = c
            OBVIOUS
          <5>13. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                         PROVE  \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                      /\ Len(alpha_) = n_
                                      /\ Len(beta_) = n_ + 1
                                      /\ beta_[1] = poss_old
                                      /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                      /\ beta_[n_+1] = c
              BY Zenon, <5>1 DEF Evolve
            <6> QED
              BY Zenon, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10, <5>11, <5>12
          <5> QED
            BY <5>13
        <4> QED
          BY <4>1, <4>2
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p),
                   P' = Filter(Evolve(P), p, (ret')[p])
            PROVE  c \in P'
        <4> USE <3>6 DEF L5
        <4>0 ret'[p] = ACK
          BY DEF TypeOK
        <4> USE <4>0
        <4>1. c \in ConfigDomain
          BY DEF S
        <4>2. \A q \in ProcSet :
                  /\ ((pc[q] = "L0" \/ p = q) => (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L1" => (c.op[q] = "R" /\ c.arg[q] = BOT /\ c.res[q] = BOT))
                  /\ (pc[q] = "L2" => (c.op[q] = "R" /\ c.arg[q] = BOT  /\ c.res[q] = x[q]))
                  /\ (pc[q] = "L3" => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT))
                  /\ (pc[q] = "L4" => (\/ (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                       \/ (X # x[q] /\ c.op[q]  = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)))
                  /\ ((pc[q] = "L5" /\ p # q) => (c.op[q] = "W" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK))
          BY DEF S, TypeOK
        <4> DEFINE c_prev == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "W"],
                              arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                              res   |-> [c.res EXCEPT ![p] = ACK]]
        <4>3. c_prev \in ConfigDomain
          BY <4>1 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
        <4>4. c_prev.state = X
          BY DEF S
        <4>5. \A q \in ProcSet : /\ (pc[q] = "L0" => (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L1" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L2" => (c_prev.op[q] = "R" /\ c_prev.arg[q] = BOT  /\ c_prev.res[q] = x[q])) 
                                 /\ (pc[q] = "L3" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT))
                                 /\ (pc[q] = "L4" => (\/ (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                                      \/ (X # x[q] /\ c_prev.op[q]  = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)))
         BY <4>2
        <4>6. \A q \in ProcSet : pc[q] = "L5" => (c_prev.op[q] = "W" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
          BY <4>1, <4>2 DEF TypeOK, ConfigDomain
        <4>7. c_prev \in S
          BY Zenon, <4>3, <4>4, <4>5, <4>6 DEF S
        <4>8. c_prev \in P
          BY <4>7 DEF Inv1
        <4> DEFINE alpha == << >>
        <4> DEFINE beta  == <<c_prev>>
        <4> DEFINE n     == 0
        <4>9. n \in Nat
          OBVIOUS
        <4>10. alpha \in Seq(ProcSet)
          OBVIOUS
        <4>11. beta \in Seq(ConfigDomain)
          BY <4>3
        <4>12. Len(alpha) = n
          OBVIOUS
        <4>13. Len(beta) = n+1
          OBVIOUS
        <4>14. beta[1] = c_prev
          OBVIOUS
        <4>15. \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
          OBVIOUS
        <4>16. beta[n+1] = c_prev
          OBVIOUS
        <4>17. c_prev \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c_prev
            BY Zenon, <4>3 DEF Evolve
          <5> QED
            BY Zenon, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16
        <4>18. c_prev.res[p] = ACK
          BY <4>1 DEF ConfigDomain
        <4>19. c.op = [c_prev.op EXCEPT ![p] = BOT]
          BY <4>2, <4>3 DEF ConfigDomain
        <4>20. c.arg = [c_prev.arg EXCEPT ![p] = BOT]
          BY <4>2, <4>3 DEF ConfigDomain
        <4>21. c.res = [c_prev.res EXCEPT ![p] = BOT]
          BY <4>2, <4>3 DEF ConfigDomain
        <4>22. c.state = c_prev.state
          OBVIOUS
        <4>23. c \in Filter(Evolve(P), p, ACK)
          BY Zenon, <4>1, <4>17, <4>18, <4>19, <4>20, <4>21, <4>22 DEF Filter
        <4> QED
          BY <4>23
      <3>7. CASE UNCHANGED vars
        BY <3>7 DEF vars, algvars, Inv1, S
      <3>8. QED
        BY <3>0, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next, IntLine, IntLines, RetLine, RetLines   
    <2>4. Inv2'
      <3> SUFFICES ASSUME TRUE
                   PROVE  S' # {}
        BY DEF Inv2
      <3>1. PICK val \in StateDomain : val = X'
        BY <2>1 DEF TypeOK
      <3> DEFINE op == [p \in ProcSet |-> CASE pc'[p] = "L0" -> BOT
                                            [] pc'[p] = "L1" -> "R"
                                            [] pc'[p] = "L2" -> "R"
                                            [] pc'[p] = "L3" -> "W"
                                            [] pc'[p] = "L4" -> "W"
                                            [] pc'[p] = "L5" -> "W"]
      <3>2. op \in [ProcSet -> OpDomain]
        BY <2>1 DEF OpDomain, TypeOK
      <3>3. \A p \in ProcSet : /\ pc'[p] = "L0" => op[p] = BOT
                               /\ pc'[p] = "L1" => op[p] = "R"
                               /\ pc'[p] = "L2" => op[p] = "R"
                               /\ pc'[p] = "L3" => op[p] = "W"
                               /\ pc'[p] = "L4" => op[p] = "W"
                               /\ pc'[p] = "L5" => op[p] = "W"
        OBVIOUS
      <3> DEFINE carg == [p \in ProcSet |-> CASE pc'[p] = "L0" -> BOT
                                              [] pc'[p] = "L1" -> BOT
                                              [] pc'[p] = "L2" -> BOT
                                              [] pc'[p] = "L3" -> arg'[p]
                                              [] pc'[p] = "L4" -> arg'[p]
                                              [] pc'[p] = "L5" -> arg'[p]]
      <3>4. carg \in [ProcSet -> ArgDomain]
        BY <2>1 DEF ArgDomain, TypeOK
      <3>5. \A p \in ProcSet : /\ pc'[p] = "L0" => carg[p] = BOT
                               /\ pc'[p] = "L1" => carg[p] = BOT
                               /\ pc'[p] = "L2" => carg[p] = BOT
                               /\ pc'[p] = "L3" => carg[p] = arg'[p]
                               /\ pc'[p] = "L4" => carg[p] = arg'[p]
                               /\ pc'[p] = "L5" => carg[p] = arg'[p]
        OBVIOUS
      <3> DEFINE res == [p \in ProcSet |-> CASE pc'[p] = "L0" -> BOT
                                             [] pc'[p] = "L1" -> BOT
                                             [] pc'[p] = "L2" -> x'[p]
                                             [] pc'[p] = "L3" -> BOT
                                             [] pc'[p] = "L4" -> BOT
                                             [] pc'[p] = "L5" -> ACK]
      <3>6. res \in [ProcSet -> ResDomain]
        BY <2>1 DEF ResDomain, TypeOK
      <3>7. \A p \in ProcSet : /\ pc'[p] = "L0" => res[p] = BOT
                               /\ pc'[p] = "L1" => res[p] = BOT
                               /\ pc'[p] = "L2" => res[p] = x'[p]
                               /\ pc'[p] = "L3" => res[p] = BOT
                               /\ pc'[p] = "L4" => res[p] = BOT
                               /\ pc'[p] = "L5" => res[p] = ACK
        OBVIOUS
      <3> DEFINE poss == [state |-> val,
                          op    |-> op,
                          arg   |-> carg,
                          res   |-> res]
      <3>8. poss \in ConfigDomain
        BY Zenon, <3>1, <3>2, <3>4, <3>6 DEF ConfigDomain
      <3>9. \A p \in ProcSet : /\ (pc'[p] = "L0" => /\ poss.op[p]  = BOT
                                                    /\ poss.arg[p] = BOT
                                                    /\ poss.res[p] = BOT)
                               /\ (pc'[p] = "L1" => /\ poss.op[p]  = "R"
                                                    /\ poss.arg[p] = BOT
                                                    /\ poss.res[p] = BOT)
                               /\ (pc'[p] = "L2" => /\ poss.op[p]  = "R"
                                                    /\ poss.arg[p] = BOT
                                                    /\ poss.res[p] = x'[p])
                               /\ (pc'[p] = "L3" => /\ poss.op[p]  = "W"
                                                    /\ poss.arg[p] = arg'[p]
                                                    /\ poss.res[p] = BOT)
                               /\ (pc'[p] = "L4" => /\ poss.op[p]  = "W"
                                                    /\ poss.arg[p] = arg'[p]
                                                    /\ poss.res[p] = BOT)
                               /\ (pc'[p] = "L5" => /\ poss.op[p]  = "W"
                                                    /\ poss.arg[p] = arg'[p]
                                                    /\ poss.res[p] = ACK)
        OBVIOUS
      <3>10. poss.state = X'
        BY <3>1
      <3> QED
        BY <3>8, <3>9, <3>10 DEF S
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 17:20:43 EDT 2024 by uguryavuz
\* Created Sat Jan 06 12:39:30 EST 2024 by uguryavuz
