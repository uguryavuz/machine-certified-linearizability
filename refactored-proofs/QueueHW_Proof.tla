--------------------------- MODULE QueueHW_Proof ---------------------------
EXTENDS QueueHW_Implementation,Permutations,
        FiniteSets, FiniteSetTheorems,
        Functions, SequenceTheorems, TLAPS, NaturalsInduction
INSTANCE Augmentation

VARIABLE P
vars == algvars \o <<pc, arg, ret, P>>

\* Needed assumptions
ASSUME RemDef == RemainderID = "L0" \* CHANGE: RemainderID \notin {"L1", "L2" ...}
ASSUME NonEmptyEltDomain == EltDomain # {}
ASSUME BotDef == /\ BOT \notin EltDomain

AInit == /\ Init
         /\ P = {[state |-> << >>,
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
  BY DEF AInit, Init, PTypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain, StateDomain

LEMMA NextPTypeOK == PTypeOK /\ [Next]_vars => PTypeOK'
  <1> USE DEF PTypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain, StateDomain
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
               P' = Evolve(P)
        PROVE  PTypeOK'
    BY <1>3 DEF L2, Evolve
  <1>4. ASSUME NEW p \in ProcSet,
               L3(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  PTypeOK'
    BY <1>4 DEF L3, Evolve, Filter
  <1>5. ASSUME NEW p \in ProcSet,
               L4(p),
               P' = Evolve(P)
        PROVE  PTypeOK'
    BY <1>5 DEF L4, Evolve
  <1>6. ASSUME NEW p \in ProcSet,
               L5(p),
               P' = Evolve(P)
        PROVE  PTypeOK'
    BY <1>6 DEF L5, Evolve
  <1>7. ASSUME NEW p \in ProcSet,
               L6(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  PTypeOK'
    BY <1>7 DEF L6, Evolve, Filter
  <1>8. CASE UNCHANGED vars
    BY <1>8 DEF vars
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 
       DEF Next, IntLine, IntLines, RetLine, RetLines

TypeOK == /\ PTypeOK
          /\ A \in [Nat -> EltDomain \union {BOT}]
          /\ L \in Nat
          /\ l \in [ProcSet -> Nat]
          /\ j \in [ProcSet -> Nat]
          /\ v \in [ProcSet -> EltDomain \union {BOT}]
          /\ \A p \in ProcSet : pc[p] = "L6" => v[p] # BOT
          /\ arg \in [ProcSet -> EltDomain]
          /\ ret \in [ProcSet -> RetDomain]
          /\ pc \in [ProcSet -> LineIDs]

LEMMA InitTypeOK == AInit => TypeOK
  BY InitPTypeOK, RemDef DEF AInit, Init, TypeOK, LineIDs

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
  <1> USE RemDef, NonEmptyEltDomain, NextPTypeOK 
          DEF TypeOK, ArgsOf, LineIDs, OpNames, OpToInvocLine, 
              ConfigDomain, OpDomain, ArgDomain, ResDomain, RetDomain, algvars
  <1> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. ASSUME NEW p \in ProcSet,
               L0(p)
        PROVE  TypeOK'
    BY <1>1 DEF L0, Invoke, Evolve 
  <1>2. ASSUME NEW p \in ProcSet,
               L1(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    BY <1>2 DEF L1, Evolve
  <1>3. ASSUME NEW p \in ProcSet,
               L2(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    BY <1>3 DEF L2, Evolve
  <1>4. ASSUME NEW p \in ProcSet,
               L3(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  TypeOK'
    BY <1>4 DEF L3, Evolve, Filter
  <1>5. ASSUME NEW p \in ProcSet,
               L4(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    BY <1>5 DEF L4, Evolve
  <1>6. ASSUME NEW p \in ProcSet,
               L5(p),
               P' = Evolve(P)
        PROVE  TypeOK'
    <2>1. CASE (j[p] = l[p])
      BY <1>6, <2>1 DEF L5, Evolve
    <2>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
      <3>1. A = A'
        BY <1>6, <2>2 DEF L5, TypeOK
      <3> QED 
        BY <1>6, <2>2, <3>1 DEF L5, Evolve
    <2>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
      BY <1>6, <2>3, Zenon DEF L5, Evolve
    <2> QED
      BY <2>1, <2>2, <2>3 DEF L5
  <1>7. ASSUME NEW p \in ProcSet,
               L6(p),
               P' = Filter(Evolve(P), p, ret'[p])
        PROVE  TypeOK'
    BY <1>7 DEF L6, Evolve, Filter
  <1>8. CASE UNCHANGED vars
    BY <1>8 DEF vars
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 
       DEF Next, IntLine, IntLines, RetLine, RetLines

Val(m) == CASE A[m] # BOT 
               -> A[m]
            [] (A[m] = BOT /\ \E p \in ProcSet : pc[p] = "L2" /\ l[p] = m) 
               -> arg[CHOOSE p \in ProcSet : pc[p] = "L2" /\ l[p] = m]
            [] OTHER
               -> BOT
               
Justified(alpha) == \A m, n \in 1..Len(alpha) : 
                       m < n => (\/ alpha[m] < alpha[n]
                                 \/ /\ (A[alpha[n]] # BOT => 
                                          (\E p \in ProcSet : /\ pc[p] = "L5"
                                                              /\ alpha[n] < j[p]
                                                              /\ alpha[m] < l[p])))

WellFormed(c, IdxSet) == \A p \in ProcSet : 
                            CASE pc[p] = "L0" 
                                   -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                              [] pc[p] = "L1"
                                   -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
                              [] pc[p] = "L2" /\ l[p] \notin IdxSet
                                   -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
                              [] pc[p] = "L2" /\ l[p] \in IdxSet
                                   -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK)
                              [] pc[p] = "L3"
                                   -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK)
                              [] pc[p] = "L4"
                                   -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                              [] pc[p] = "L5"
                                   -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                              [] pc[p] = "L6"
                                   -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = v[p])

S == {c \in ConfigDomain : 
        \E IdxSet \in SUBSET 0..(L-1) :
            /\ \A m \in IdxSet : Val(m) # BOT
            /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
            /\ \E alpha \in Perm(IdxSet) : 
               /\ Justified(alpha)
               /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
               /\ WellFormed(c, IdxSet)}


Inv0 == IsFiniteSet({q \in ProcSet : pc[q] # "L0"})
Inv1 == \A p \in ProcSet : pc[p] \in {"L2", "L3"} => l[p] \in 0..(L-1)
Inv2 == \A p, q \in ProcSet : (/\ p # q 
                               /\ pc[p] \in {"L2", "L3"}
                               /\ pc[q] \in {"L2", "L3"}) => l[p] # l[q]
Inv3 == \A p \in ProcSet : pc[p] = "L5" => /\ j[p] \in 0..l[p]
                                           /\ l[p] \in j[p]..L
Inv4 == \A i \in Nat : i \geq L => A[i] = BOT
InvE == \A p \in ProcSet : pc[p] = "L2" => A[l[p]] = BOT
Lin1 == S \in SUBSET P
Lin2 == S # {}

Inv == /\ TypeOK
       /\ Inv0
       /\ Inv1
       /\ Inv2
       /\ Inv3
       /\ Inv4
       /\ InvE
       /\ Lin1
       /\ Lin2
       
THEOREM Spec => []Inv
  <1>1. AInit => Inv
    <2> USE RemDef DEF Inv, AInit, Init
    <2> SUFFICES ASSUME AInit
                 PROVE  Inv
      OBVIOUS
    <2>1. TypeOK
      BY InitTypeOK
    <2>2. Inv0
      BY Isa DEF Inv0, IsFiniteSet
    <2>3. Inv1
      BY DEF Inv1
    <2>4. Inv2
      BY DEF Inv2
    <2>5. Inv3
      BY DEF Inv3
    <2>6. Inv4
      BY DEF Inv4
    <2>7. InvE
      BY DEF InvE
    <2>8. Lin1
      <3> SUFFICES ASSUME NEW c \in S
                   PROVE  c \in P
        BY DEF Lin1
      <3>1. PICK IdxSet \in SUBSET 0..(L-1) : /\ \E alpha \in Perm(IdxSet) : 
                                                  /\ Justified(alpha)
                                                  /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
                                                  /\ \A p \in ProcSet : 
                                                        CASE pc[p] = "L0" 
                                                               -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                                                          [] pc[p] = "L1"
                                                               -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
                                                          [] pc[p] = "L2" /\ l[p] \notin IdxSet
                                                               -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
                                                          [] pc[p] = "L2" /\ l[p] \in IdxSet
                                                               -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK)
                                                          [] pc[p] = "L3"
                                                               -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK)
                                                          [] pc[p] = "L4"
                                                               -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                                                          [] pc[p] = "L5"
                                                               -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                                                          [] pc[p] = "L6"
                                                               -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = v[p])
        BY Zenon DEF S, WellFormed
      <3>2. PICK alpha \in Perm(IdxSet) : /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
                                          /\ \A p \in ProcSet : 
                                                CASE pc[p] = "L0" 
                                                       -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
        BY <3>1
      <3>3. IdxSet = {}
        OBVIOUS
      <3>4. alpha = << >>
        BY <3>3, FS_EmptySet DEF Perm, Len
      <3>5. c.state = << >>
        BY <3>2, <3>4 
      <3>6. \A p \in ProcSet : (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
        BY <3>2 DEF TypeOK
      <3>7. c \in ConfigDomain
        BY DEF S
      <3> QED
        BY <3>5, <3>6, <3>7 DEF ConfigDomain
    <2>9. Lin2
      <3> DEFINE c == [state |-> << >>, 
                       op    |-> [p \in ProcSet |-> BOT], 
                       arg   |-> [p \in ProcSet |-> BOT], 
                       res   |-> [p \in ProcSet |-> BOT]]
      <3>1. \A p \in ProcSet : /\ pc[p] = "L0"
                               /\ c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
        OBVIOUS
      <3>2. c \in ConfigDomain
        BY DEF OpDomain, ArgDomain, ResDomain, ConfigDomain, StateDomain, Seq
      <3>3. c \in S
        <4> DEFINE IdxSet == {}
        <4> DEFINE alpha == << >>
        <4>1. IdxSet \in SUBSET 0..(L-1)
          OBVIOUS
        <4>2. \A m \in IdxSet : Val(m) # BOT
          OBVIOUS
        <4>3. \A m \in 0..L - 1 : A[m] # BOT => m \in IdxSet
          OBVIOUS
        <4>4. alpha \in Perm(IdxSet)
          BY FS_EmptySet DEF Seq, Len, Perm
        <4>5. Justified(alpha)
          BY DEF Justified
        <4> SUFFICES ASSUME TRUE
                     PROVE  /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
                            /\ \A p \in ProcSet : pc[p] = "L0" => (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
          BY Zenon, <3>2, <4>1, <4>2, <4>3, <4>4, <4>5 DEF S, WellFormed, TypeOK 
        <4>6. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          BY DEF Len
        <4>7. \A p \in ProcSet : pc[p] = "L0" => c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
          OBVIOUS
        <4> QED
          BY <4>4, <4>5, <4>6, <4>7 DEF S
      <3> QED
        BY <3>3 DEF Lin2
    <2>10. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Inv
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
        BY <3>3 DEF L2
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  Inv0'
        BY <3>4, FS_Subset DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  Inv0'
        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  Inv0'
        <4>1. CASE (j[p] = l[p])
          BY <3>6, <4>1, Zenon DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          BY <3>6, <4>2, Zenon DEF L5, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          BY <3>6, <4>3, Zenon DEF L5, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet,
                   L6(p)
            PROVE  Inv0'
        BY <3>7, FS_Subset DEF L6
      <3>8. CASE UNCHANGED vars
        BY <3>8 DEF vars, algvars
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>3. Inv1'
      <3> USE DEF Inv1
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv1'
        BY <3>1 DEF Inv1, L0, TypeOK, OpNames, OpToInvocLine, algvars
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p)
            PROVE  Inv1'
        BY <3>2 DEF L1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p)
            PROVE  Inv1'
        BY <3>3 DEF L2
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  Inv1'
        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  Inv1'
        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  Inv1'
        <4>1. CASE (j[p] = l[p])
          BY <3>6, <4>1, Zenon DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          BY <3>6, <4>2, Zenon DEF L5, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          BY <3>6, <4>3, Zenon DEF L5, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet,
                   L6(p)
            PROVE  Inv1'
        BY <3>7 DEF L6
      <3>8. CASE UNCHANGED vars
        BY <3>8 DEF vars, algvars
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>4. Inv2'
      <3> USE DEF Inv2
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv2'
        BY <3>1 DEF Inv2, L0, TypeOK, OpNames, OpToInvocLine, algvars
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p)
            PROVE  Inv2'
        BY <3>2 DEF Inv2, L1, TypeOK, Inv1
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p)
            PROVE  Inv2'
        BY <3>3 DEF L2
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  Inv2'
        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  Inv2'
        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  Inv2'
        <4>1. CASE (j[p] = l[p])
          BY <3>6, <4>1, Zenon DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          BY <3>6, <4>2, Zenon DEF L5, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          BY <3>6, <4>3, Zenon DEF L5, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet,
                   L6(p)
            PROVE  Inv2'
        BY <3>7 DEF L6
      <3>8. CASE UNCHANGED vars
        BY <3>8 DEF vars, algvars
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>5. Inv3'
      <3> USE DEF Inv3
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv3'
        BY <3>1 DEF Inv3, L0, TypeOK, OpNames, OpToInvocLine, algvars
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p)
            PROVE  Inv3'
        BY <3>2 DEF L1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p)
            PROVE  Inv3'
        BY <3>3 DEF L2
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  Inv3'
        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  Inv3'
        BY <3>5 DEF Inv3, L4, TypeOK
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  Inv3'
        <4>1. CASE (j[p] = l[p])
          BY <3>6, <4>1 DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          BY <3>6, <4>2 DEF L5, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          BY <3>6, <4>3, Zenon DEF L5, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet,
                   L6(p)
            PROVE  Inv3'
        BY <3>7 DEF L6
      <3>8. CASE UNCHANGED vars
        BY <3>8 DEF vars, algvars
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>6. Inv4'
      <3> USE DEF Inv4
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  Inv4'
        BY <3>1 DEF Inv4, L0, TypeOK, OpNames, OpToInvocLine, algvars
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p)
            PROVE  Inv4'
        BY <3>2 DEF L1, TypeOK
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p)
            PROVE  Inv4'
        BY <3>3 DEF L2, TypeOK, Inv1
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  Inv4'
        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  Inv4'
        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  Inv4'
        <4>1. CASE (j[p] = l[p])
          BY <3>6, <4>1, Zenon DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          BY <3>6, <4>2, Zenon DEF L5, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          BY <3>6, <4>3, Zenon DEF L5, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet,
                   L6(p)
            PROVE  Inv4'
        BY <3>7 DEF L6
      <3>8. CASE UNCHANGED vars
        BY <3>8 DEF vars, algvars
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>7. InvE'
      <3> USE DEF InvE
      <3>1. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  InvE'
        BY <3>1 DEF InvE, L0, TypeOK, OpNames, OpToInvocLine, algvars
      <3>2. ASSUME NEW p \in ProcSet,
                   L1(p)
            PROVE  InvE'
        BY <3>2 DEF L1, TypeOK, Inv4
      <3>3. ASSUME NEW p \in ProcSet,
                   L2(p)
            PROVE  InvE'
        BY <3>3 DEF L2, TypeOK, Inv2
      <3>4. ASSUME NEW p \in ProcSet,
                   L3(p)
            PROVE  InvE'
        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet,
                   L4(p)
            PROVE  InvE'
        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet,
                   L5(p)
            PROVE  InvE'
        <4>1. CASE (j[p] = l[p])
          BY <3>6, <4>1, Zenon DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          <5> USE <3>6, <4>2 DEF L5
          <5>1. \A q \in ProcSet : A[l[q]] = BOT => A'[l[q]] = BOT
            BY DEF TypeOK
          <5> QED
            BY <5>1 DEF InvE, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          <5> USE <3>6, <4>3 DEF L5
          <5>1. A' = [A EXCEPT ![j[p]] = BOT]
            BY Zenon
          <5>2. \A q \in ProcSet : A[l[q]] = BOT => A'[l[q]] = BOT
            BY <5>1 DEF TypeOK
          <5> QED
            BY <5>2 DEF InvE, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet,
                   L6(p)
            PROVE  InvE'
        BY <3>7 DEF L6
      <3>8. CASE UNCHANGED vars
        BY <3>8 DEF vars, algvars
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>8. Lin1'
      <3> USE DEF Lin1
      <3>1. SUFFICES ASSUME NEW c \in S'
                     PROVE  c \in P'
        BY DEF Lin1
      <3>2. c \in ConfigDomain
        BY DEF S
      <3>3. ASSUME NEW p \in ProcSet,
                   L0(p)
            PROVE  c \in P'
        <4> USE <3>3 DEF L0, algvars
        <4> DEFINE c_prev == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = BOT],
                              arg   |-> [c.arg EXCEPT ![p] = BOT],
                              res   |-> [c.res EXCEPT ![p] = BOT]]
        <4>1. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>2. IdxSet \in SUBSET 0..(L-1)
          BY <4>1 DEF TypeOK
        <4>3. /\ \A m \in IdxSet : Val(m) # BOT
              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          BY <4>1, Z3T(10) DEF Val, OpNames, OpToInvocLine, TypeOK
        <4>4. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>1
        <4>5. Justified(alpha)
          <5> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                              m < n
                       PROVE  \/ alpha[m] < alpha[n]
                              \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                         /\ alpha[n] < j[q]
                                                                         /\ alpha[m] < l[q]
            BY DEF Justified
          <5>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
            BY <4>2, <4>4 DEF Perm
          <5>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
            BY <4>2, <5>1, Zenon
          <5> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                       PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <4>2, <5>2 DEF Perm
          <5>3. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
            BY <4>4, <5>2 DEF Justified
          <5>4. q # p
            BY <5>2, <5>3 DEF OpNames, OpToInvocLine, TypeOK
          <5>5. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <5>3, <5>4 DEF TypeOK
          <5> QED
            BY <5>5 
        <4>6. c_prev \in ConfigDomain
          BY <3>2 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
        <4>7. c_prev.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          BY <4>4 DEF Val, OpNames, OpToInvocLine, TypeOK
        <4>8. WellFormed(c_prev, IdxSet)
          <5> USE DEF OpNames, OpToInvocLine, TypeOK
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  CASE pc[q] = "L0" 
                                     -> (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L1"
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \notin IdxSet
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \in IdxSet
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                [] pc[q] = "L3"
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                [] pc[q] = "L4"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L5"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L6"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q])
            BY Zenon DEF WellFormed
          <5>1. CASE pc[q] = "L0"
            <6> USE <5>1
            <6>1. CASE p = q
              <7>1. c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <6>1, <4>6 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
              <7> QED
                BY <7>1
            <6>2. CASE p # q
              <7>1. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <4>4, <6>2, Zenon DEF WellFormed, TypeOK
              <7>2. c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <6>2, <7>1
              <7> QED
                BY <7>2
            <6> QED
              BY <6>1, <6>2
          <5>2. CASE pc[q] = "L1"
            <6> USE <5>2
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <4>4, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet
            <6> USE <5>3
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <4>4, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2, Zenon
          <5>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet
            <6> USE <5>4
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
              BY <4>4, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
              BY <6>0, <6>1
            <6> QED
              BY <6>2, Zenon
          <5>5. CASE pc[q] = "L3"
            <6> USE <5>5
            <6>1. CASE p = q
              <7>1. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <6>1, <4>6 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
              <7> QED
                BY <7>1
            <6>2. CASE p # q
              <7>1. c.op[q] = "ENQ" /\ c.arg[q] = arg'[q] /\ c.res[q] = ACK
                BY <4>4, <6>2, Zenon DEF WellFormed, TypeOK
              <7>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <6>2, <7>1
              <7> QED
                BY <7>2
            <6> QED
              BY <6>1, <6>2
          <5>6. CASE pc[q] = "L4"
            <6> USE <5>6
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>4, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>7. CASE pc[q] = "L5"
            <6> USE <5>7
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>4, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>8. CASE pc[q] = "L6"
            <6> USE <5>8
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
              BY <4>4, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q]
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5> QED
            BY RemDef, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, ZenonT(15) DEF TypeOK
        
        <4>9. c_prev \in S
          BY Zenon, <4>6, <4>1, <4>2, <4>3, <4>4, <4>5, <4>5, <4>7, <4>8 DEF S
        <4>10. c_prev \in P
          BY <4>9
        <4>11. c_prev.op[p] = BOT /\ c_prev.arg[p] = BOT /\ c_prev.res[p] = BOT
          BY <4>6 DEF ConfigDomain, OpToInvocLine, OpNames, ArgsOf, TypeOK
        <4>12. CASE pc'[p] = "L1"
          <5> USE <4>12
          <5> PICK op \in OpNames : /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                                    /\ \E arg_val \in ArgsOf(op) : 
                                       /\ IF arg_val # BOT 
                                             THEN arg' = [arg EXCEPT ![p] = arg_val]
                                             ELSE arg' = arg  
                                       /\ P' = Evolve(Invoke(P, p, op, arg_val))
            BY Zenon
          <5> op = "ENQ"
            BY DEF OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> PICK arg_val \in ArgsOf("ENQ") : /\ IF arg_val # BOT 
                                                     THEN arg' = [arg EXCEPT ![p] = arg_val]
                                                     ELSE arg' = arg  
                                               /\ P' = Evolve(Invoke(P, p, op, arg_val))
            BY DEF OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> arg' = [arg EXCEPT ![p] = arg_val]
            BY BotDef DEF OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5>1. c.op = [c_prev.op EXCEPT ![p] = "ENQ"]
            BY Zenon, <3>2, <4>1 DEF WellFormed, ConfigDomain, OpNames, TypeOK
          <5>2. c.arg = [c_prev.arg EXCEPT ![p] = arg_val]
            BY Zenon, <3>2, <4>1 DEF WellFormed, ConfigDomain, OpNames, TypeOK
          <5>3. c.res = [c_prev.res EXCEPT ![p] = BOT]
            BY Zenon, <3>2, <4>1 DEF WellFormed, ConfigDomain, OpNames, TypeOK
          <5>4. c \in Invoke(P, p, "ENQ", arg_val)
            BY Zenon, <3>2, <4>10, <4>11, <5>1, <5>2, <5>3 DEF Invoke, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> DEFINE pseq == << >>
          <5> DEFINE beta  == <<c>>
          <5> DEFINE n     == 0
          <5>5. c \in ConfigDomain
            BY <3>2
          <5>6. c \in Invoke(P, p, "ENQ", arg_val)
            BY <5>4
          <5>7. n \in Nat
            OBVIOUS
          <5>8. pseq \in Seq(ProcSet)
            OBVIOUS
          <5>9. beta \in Seq(ConfigDomain)
            BY <3>2
          <5>10. Len(pseq) = n
            OBVIOUS
          <5>11. Len(beta) = n+1
            OBVIOUS
          <5>12. beta[1] = c
            OBVIOUS
          <5>13. \A i \in 1..n : Delta(beta[i], pseq[i], beta[i+1])
            OBVIOUS
          <5>14. beta[n+1] = c
            OBVIOUS
          <5>15. c \in Evolve(Invoke(P, p, "ENQ", arg_val))
            <6>1. \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Len(alpha_) = n
                                    /\ Len(beta_) = n+1
                                    /\ beta_[1] = c
                                    /\ \A i \in 1..n : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n+1] = c
              BY <5>8, <5>9, <5>10, <5>11, <5>12, <5>13, <5>14, Zenon
            <6>2. \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = c
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY <5>7, <6>1, Zenon
            <6> DEFINE Q(beta_) ==  \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : /\ Len(alpha_) = n_
                                                                                 /\ Len(beta_) = n_ + 1
                                                                                 /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                                                                 /\ beta_[n_+1] = c
            <6>3. \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Q(beta_)
                                    /\ beta_[1] = c
              BY <6>2
            <6> HIDE DEF Q
            <6>4. \E poss_old \in Invoke(P, p, "ENQ", arg_val) : \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Q(beta_)
                                    /\ beta_[1] = poss_old
              BY <5>6, <6>3
            <6>5. \E poss_old \in Invoke(P, p, "ENQ", arg_val) : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                      /\ Len(alpha_) = n_
                      /\ Len(beta_) = n_ + 1
                      /\ beta_[1] = poss_old
                      /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                      /\ beta_[n_+1] = c
              BY <6>4 DEF Q
            <6> SUFFICES ASSUME TRUE
                         PROVE  \E poss_old \in Invoke(P, p, "ENQ", arg_val) : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY <5>5 DEF Evolve  
            <6> QED
              BY <6>5
          <5> QED
            BY <5>15 DEF OpNames, ArgsOf, OpToInvocLine
        <4>13. CASE pc'[p] = "L4"
          <5> USE <4>13
          <5> PICK op \in OpNames : /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                                    /\ \E arg_val \in ArgsOf(op) : 
                                       /\ IF arg_val # BOT 
                                             THEN arg' = [arg EXCEPT ![p] = arg_val]
                                             ELSE arg' = arg  
                                       /\ P' = Evolve(Invoke(P, p, op, arg_val))
            BY Zenon
          <5> op = "DEQ"
            BY DEF OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> PICK arg_val \in ArgsOf("DEQ") : /\ IF arg_val # BOT 
                                                     THEN arg' = [arg EXCEPT ![p] = arg_val]
                                                     ELSE arg' = arg  
                                               /\ P' = Evolve(Invoke(P, p, op, arg_val))
            BY DEF OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> arg' = arg
            BY BotDef DEF OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5>1. c.op = [c_prev.op EXCEPT ![p] = "DEQ"]
            BY Zenon, <3>2, <4>1 DEF WellFormed, ConfigDomain, OpNames, TypeOK
          <5>2. c.arg = [c_prev.arg EXCEPT ![p] = BOT]
            BY Zenon, <3>2, <4>1 DEF WellFormed, ConfigDomain, OpNames, TypeOK
          <5>3. c.res = [c_prev.res EXCEPT ![p] = BOT]
            BY Zenon, <3>2, <4>1 DEF WellFormed, ConfigDomain, OpNames, TypeOK
          <5>4. c \in Invoke(P, p, "DEQ", BOT)
            BY Zenon, <3>2, <4>10, <4>11, <5>1, <5>2, <5>3 DEF Invoke, OpToInvocLine, OpNames, ArgsOf, TypeOK
          <5> DEFINE pseq == << >>
          <5> DEFINE beta  == <<c>>
          <5> DEFINE n     == 0
          <5>5. c \in ConfigDomain
            BY <3>2
          <5>6. c \in Invoke(P, p, "DEQ", BOT)
            BY <5>4
          <5>7. n \in Nat
            OBVIOUS
          <5>8. pseq \in Seq(ProcSet)
            OBVIOUS
          <5>9. beta \in Seq(ConfigDomain)
            BY <3>2
          <5>10. Len(pseq) = n
            OBVIOUS
          <5>11. Len(beta) = n+1
            OBVIOUS
          <5>12. beta[1] = c
            OBVIOUS
          <5>13. \A i \in 1..n : Delta(beta[i], pseq[i], beta[i+1])
            OBVIOUS
          <5>14. beta[n+1] = c
            OBVIOUS
          <5>15. c \in Evolve(Invoke(P, p, "DEQ", BOT))
            <6>1. \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Len(alpha_) = n
                                    /\ Len(beta_) = n+1
                                    /\ beta_[1] = c
                                    /\ \A i \in 1..n : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n+1] = c
              BY <5>8, <5>9, <5>10, <5>11, <5>12, <5>13, <5>14, Zenon
            <6>2. \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = c
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY <5>7, <6>1, Zenon
            <6> DEFINE Q(beta_) ==  \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : /\ Len(alpha_) = n_
                                                                                 /\ Len(beta_) = n_ + 1
                                                                                 /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                                                                 /\ beta_[n_+1] = c
            <6>3. \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Q(beta_)
                                    /\ beta_[1] = c
              BY <6>2
            <6> HIDE DEF Q
            <6>4. \E poss_old \in Invoke(P, p, "DEQ", BOT) : \E beta_ \in Seq(ConfigDomain) : 
                                    /\ Q(beta_)
                                    /\ beta_[1] = poss_old
              BY <5>6, <6>3
            <6>5. \E poss_old \in Invoke(P, p, "DEQ", BOT) : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                      /\ Len(alpha_) = n_
                      /\ Len(beta_) = n_ + 1
                      /\ beta_[1] = poss_old
                      /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                      /\ beta_[n_+1] = c
              BY <6>4 DEF Q
            <6> SUFFICES ASSUME TRUE
                         PROVE  \E poss_old \in Invoke(P, p, "DEQ", BOT) : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY <5>5 DEF Evolve  
            <6> QED
              BY <6>5
          <5> QED
            BY <5>15 DEF OpNames, ArgsOf, OpToInvocLine
        <4> QED
          BY <4>12, <4>13 DEF OpNames, OpToInvocLine, TypeOK
      <3>4. ASSUME NEW p \in ProcSet,
                   L1(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>4 DEF L1
        <4>1. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>2. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>1
        <4>3. CASE l'[p] \notin IdxSet
          <5> USE <4>3
          <5>1. IdxSet \in SUBSET 0..L-1
            BY <4>1 DEF TypeOK
          <5>2. \A m \in IdxSet : Val(m) # BOT
            BY <4>1 DEF Val, TypeOK
          <5>3. \A m \in 0..L-1 : A[m] # BOT => m \in IdxSet
            BY <4>1 DEF TypeOK
          <5>4. alpha \in Perm(IdxSet)
            BY <4>1
          <5>5. Justified(alpha)
            <6> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                                m < n
                         PROVE  \/ (alpha[m] < alpha[n])
                                \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                           /\ alpha[n] < j[q]
                                                                           /\ alpha[m] < l[q]
              BY DEF Justified
            <6>1. m # n => alpha[m] # alpha[n]
              BY <5>4, Zenon DEF Perm
            <6>2. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
              BY <5>4 DEF Perm
            <6>3. \A x \in IdxSet : x \in 0..L-1
              BY <5>1 
            <6>4. alpha[m] \in 0..L-1 /\ alpha[n] \in 0..L-1
              BY <6>2, <6>3, Zenon 
            <6> SUFFICES ASSUME alpha[m] > alpha[n], A[alpha[n]] # BOT
                         PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <6>1, <6>4 DEF TypeOK
            <6>6. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
              BY <4>1, <4>2, <6>4 DEF Justified
            <6>7. q # p
              BY <6>6 DEF TypeOK
            <6>8. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <6>6, <6>7 DEF TypeOK
            <6> QED
              BY <6>8
          <5>6. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
            <6> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                         PROVE  Val(alpha[i])' = Val(alpha[i])
              BY <4>1, <4>2
            <6>1. CASE A[alpha[i]] # BOT
              BY <6>1, <4>2 DEF Val
            <6>2. CASE A[alpha[i]] = BOT /\ ~(\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>2, <4>2 DEF Val
            <6>3. CASE A[alpha[i]] = BOT /\ (\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>3, <4>3 DEF Val
            <6> QED
              BY <6>1, <6>2, <6>3 DEF Val
          <5>7. WellFormed(c, IdxSet)
            BY <4>2, ZenonT(15) DEF WellFormed, TypeOK
          <5>8. c \in S
            BY Zenon, <3>2, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7 DEF S
          <5>9. c \in P
            BY <5>8
          <5> DEFINE aseq == << >>
          <5> DEFINE beta == <<c>>
          <5> DEFINE n    == 0
          <5>10. n \in Nat
            OBVIOUS
          <5>11. aseq \in Seq(ProcSet)
            OBVIOUS
          <5>12. beta \in Seq(ConfigDomain)
            BY <3>2
          <5>13. Len(aseq) = n
            OBVIOUS
          <5>14. Len(beta) = n+1
            OBVIOUS
          <5>15. beta[1] = c
            OBVIOUS
          <5>16. \A i \in 1..n : Delta(beta[i], aseq[i], beta[i+1])
            OBVIOUS
          <5>17. beta[n+1] = c
            OBVIOUS
          <5>18. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                          PROVE  \E poss_old \in P : \E n_ \in Nat : \E aseq_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                      /\ Len(aseq_) = n_
                                      /\ Len(beta_) = n_ + 1
                                      /\ beta_[1] = poss_old
                                      /\ \A i \in 1..n_ : Delta(beta_[i], aseq_[i], beta_[i+1])
                                      /\ beta_[n_+1] = c
              BY <5>1 DEF Evolve
            <6> QED
              BY Zenon, <5>9, <5>10, <5>11, <5>12, <5>13, <5>14, <5>15, <5>16, <5>17
          <5> QED
            BY <5>18
        <4>4. CASE l'[p] \in IdxSet
          <5> USE <4>4
          <5>1. IsFiniteSet(0..L'-1)
            BY <4>1, FS_Interval DEF TypeOK
          <5>2. IsFiniteSet(IdxSet)
            BY <5>1, FS_Subset, Zenon
          <5>3. PICK k \in 1..Len(alpha) : alpha[k] = l'[p]
            BY <5>2, FS_PermutationIndex DEF Perm
          <5>4. \A z \in k..Len(alpha) : A[alpha[z]] = BOT
            <6>1. A[l'[p]] = BOT
              BY <2>7 DEF TypeOK, InvE
            <6> SUFFICES ASSUME NEW z \in (k+1)..Len(alpha), A[alpha[z]] # BOT
                         PROVE  FALSE
              BY <5>3, <6>1
            <6>2. alpha[z] < alpha[k]
              <7>1. alpha[z] \in IdxSet
                BY DEF Perm
              <7>2. \A b \in IdxSet : b <= L
                BY DEF TypeOK
              <7>3. alpha[z] <= L
                BY <7>1, <7>2, Zenon
              <7>4. \A y, q \in DOMAIN alpha : y # q => alpha[y] # alpha[q]
                BY <4>2 DEF Perm
              <7>5. alpha[k] # alpha[z]
                BY <5>3, <7>4
              <7>6. L = alpha[k]
                BY <5>3 DEF TypeOK
              <7> QED
                BY <7>3, <7>5, <7>6, Isa
            <6>3. alpha[k] \in Nat
              BY <4>1, <5>3, FS_Subset DEF TypeOK
            <6>4. alpha[z] \in IdxSet
              BY <4>1 DEF Perm
            <6>5. \A x \in IdxSet : x \in 0..L'-1
              BY <4>1
            <6>6. alpha[z] \in 0..L'-1
              BY <6>4, <6>5, Zenon
            <6>7. alpha[z] \in Nat
              BY <6>6 DEF TypeOK
            <6>8. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[k] < l'[q] /\ alpha[z] < j'[q]
              BY <4>2, <5>3, <6>2, <6>3, <6>7 DEF Justified
            <6>9. l'[q] <= L
              BY <2>5, <6>8 DEF Inv3
            <6>10. alpha[k] < L
              BY <5>3, <6>8, <6>9 DEF TypeOK
            <6> QED
              BY <5>3, <6>10 DEF TypeOK
                
          \* These are the indices in A that contain the former state, in the order of the state.
          <5> alpha_prev == SubSeq(alpha, 1, k-1)
          
          \* This is the set of indices in A that contain the former state.
          <5> IdxSet_prev == {alpha_prev[z] : z \in 1..k-1}
          
          \* This is the set of conjectured linearizing enqueue processes.
          <5> pset == {q \in ProcSet : \E n \in k..Len(alpha) : pc'[q] = "L2" /\ l'[q] = alpha[n]}
          
          \* These are the conjectured linearizing enqueue processes, in the linearization order.
          <5> pseq == [m \in 1..Len(alpha)-(k-1) |-> CHOOSE q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[m+(k-1)]]
                   
          <5> c_prev == [state |-> SubSeq(c.state, 1, k-1),
                         op    |-> c.op,
                         arg   |-> c.arg,
                         res   |-> [q \in ProcSet |-> IF q \in pset THEN BOT ELSE c.res[q]]]
          
          <5>5. c_prev \in ConfigDomain
            <6>1. c_prev.state \in Seq(EltDomain)
              <7>1. c.state \in Seq(EltDomain)
                BY <3>2 DEF ConfigDomain, StateDomain
              <7>2. c_prev.state \in Seq(EltDomain)
                BY <4>2, <5>3, <7>1, SubSeqProperties
              <7> QED
                BY <7>2
            <6>2. c_prev.op \in [ProcSet -> OpDomain]
              BY <3>2 DEF ConfigDomain
            <6>3. c_prev.arg \in [ProcSet -> ArgDomain]
              BY <3>2 DEF ConfigDomain
            <6>4. c_prev.res \in [ProcSet -> ResDomain]
              BY <3>2 DEF ConfigDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain, StateDomain
          <5>6. IdxSet_prev \in SUBSET 0..(L-1)
            <6>1. IdxSet_prev \in SUBSET IdxSet
              BY <4>2 DEF Perm
            <6>2. IdxSet_prev \in SUBSET 0..L'-1
              BY <4>1, <6>1, Zenon
            <6>3. IdxSet_prev \in SUBSET 0..l'[p]
              BY <6>2 DEF TypeOK
            <6>4. \A n \in 1..k-1 : alpha[n] # l'[p]
              BY <4>2, <5>3 DEF Perm
            <6>5. IdxSet_prev \in SUBSET 0..l'[p]-1
              BY <6>3, <6>4 DEF TypeOK
            <6> QED
              BY <6>5 DEF TypeOK
          <5>7. \A m \in IdxSet_prev : Val(m) # BOT
            <6> SUFFICES ASSUME NEW m \in IdxSet_prev, A[m] = BOT
                         PROVE  Val(m) # BOT
              BY Zenon DEF Val
            <6>1. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = m
              BY <4>1, <4>2, Z3T(30) DEF Val, Perm
            <6>2. q # p
              BY <5>6, <6>1 DEF TypeOK
            <6>3. pc[q] = "L2" /\ l[q] = m
              BY <6>1, <6>2
            <6>A. \A r \in ProcSet : (pc[r] = "L2" /\ l[r] = m) <=> (r = q)
              BY <6>3 DEF Inv2
            <6>4. Val(m) = arg[q]
              BY <6>1, <6>3, <6>A DEF Val
            <6> QED
              BY BotDef, <6>4 DEF TypeOK
          <5>8. \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet_prev
            <6> SUFFICES ASSUME NEW m \in 0..(L-1), A[m] # BOT
                         PROVE  m \in IdxSet_prev
              OBVIOUS
            <6>1. m \in IdxSet
              BY <4>1 DEF TypeOK
            <6>2. PICK z \in 1..Len(alpha) : alpha[z] = m
              BY <4>2, <5>2, <6>1, FS_PermutationIndex
            <6>3. z \in 1..k-1
              BY <5>4, <6>2
            <6>4. m \in IdxSet_prev
              BY <6>1, <6>2, <6>3
            <6> QED
              BY <6>4
          <5>9. alpha_prev \in Perm(IdxSet_prev)
            <6>0. alpha_prev = [i \in 1..(k-1) |-> alpha[i]]
              BY DEF SubSeq
            <6>1. alpha_prev \in Seq(IdxSet_prev)
              <7>1. \A z \in 1..k-1 : alpha[z] \in IdxSet_prev
                OBVIOUS
              <7> QED
                BY <7>1, <6>0 DEF Seq
            <6>2. Len(alpha_prev) = k-1
              OBVIOUS
            <6>3. Cardinality(IdxSet_prev) = k-1
              <7>1. alpha_prev \in Injection(1..k-1, IdxSet_prev)
                <8> SUFFICES ASSUME NEW a \in 1..k-1, NEW b \in 1..k-1,
                                    alpha_prev[a] = alpha_prev[b]
                             PROVE  a = b
                  BY <6>0, Zenon DEF Injection
                <8> QED
                  BY <4>2 DEF Perm, SubSeq
              <7>2. alpha_prev \in Surjection(1..k-1, IdxSet_prev)
                BY <6>0, Zenon DEF Surjection
              <7>3. ExistsBijection(1..k-1, IdxSet_prev)
                BY <7>1, <7>2 DEF Bijection, ExistsBijection
              <7> HIDE DEF alpha_prev
              <7> QED
                BY <5>3, <7>3, FS_CountingElements
            <6>4. \A x, y \in 1..Len(alpha_prev) : x # y => alpha_prev[x] # alpha_prev[y]
              BY <4>2, <5>1 DEF Perm
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4, Zenon DEF Perm
          <5>10. Justified(alpha_prev)
            <6> SUFFICES ASSUME NEW m \in 1..Len(alpha_prev), NEW n \in 1..Len(alpha_prev),
                                m < n
                         PROVE  \/ alpha_prev[m] < alpha_prev[n]
                                \/ A[alpha_prev[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                                /\ alpha_prev[n] < j[q]
                                                                                /\ alpha_prev[m] < l[q]
              BY DEF Justified
            <6>1. m # n => alpha_prev[m] # alpha_prev[n]
              BY <4>1 DEF Perm
            <6>2. alpha_prev[m] \in IdxSet_prev /\ alpha_prev[n] \in IdxSet_prev
              OBVIOUS
            <6>3. alpha_prev[m] \in 0..L-1 /\ alpha_prev[n] \in 0..L-1
              BY <6>2, <5>6, Zenon
            <6> SUFFICES ASSUME alpha[m] > alpha[n], A[alpha_prev[n]] # BOT
                         PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <6>1, <6>3 DEF TypeOK
            <6>4. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
              BY <4>1, <4>2, <6>3 DEF Justified
            <6>5. q # p
              BY <6>4 DEF TypeOK
            <6>6. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <6>4, <6>5 DEF TypeOK
            <6> QED
              BY <6>6
          <5>11. c_prev.state = [i \in 1..Len(alpha_prev) |-> Val(alpha_prev[i])]
            <6> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                         PROVE  Val(alpha[i])' = Val(alpha[i])
              BY <4>1, <4>2
            <6>1. CASE A[alpha[i]] # BOT
              BY <6>1, <4>2 DEF Val
            <6>2. CASE A[alpha[i]] = BOT /\ ~(\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>2, <4>2 DEF Val
            <6>3. CASE A[alpha[i]] = BOT /\ (\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>3, <4>3 DEF Val
            <6> QED
              BY <6>1, <6>2, <6>3 DEF Val
          <5>12. WellFormed(c_prev, IdxSet_prev)
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc[q] = "L0" 
                                       -> (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L1"
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \notin IdxSet_prev
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \in IdxSet_prev
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                  [] pc[q] = "L3"
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                  [] pc[q] = "L4"
                                       -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L5"
                                       -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L6"
                                       -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q])
              BY Zenon DEF WellFormed
            <6>1. CASE pc[q] = "L0"
              <7> USE <6>1
              <7>1. pc'[q] = "L0" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>2. CASE pc[q] = "L1"
              <7> USE <6>2
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. pc'[q] = "L2"
                  BY DEF TypeOK
                <8>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
                  BY <4>2, <5>3, <8>1, Zenon DEF WellFormed
                <8>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
                  BY <5>3, <8>2 DEF TypeOK
                <8> QED
                  BY <8>3
              <7>2. CASE q # p
                <8>1. pc'[q] = "L1" /\ q # p
                  BY <7>2 DEF TypeOK
                <8>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <4>2, <7>2, <8>1, Zenon DEF WellFormed
                <8>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
                  BY <8>2 DEF TypeOK
                <8> QED
                  BY <8>3
              <7> QED
                BY <7>1, <7>2
            <6>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet_prev
              <7> USE <6>3
              <7>1. CASE l[q] \in IdxSet
                <8> USE <7>1
                <8>1. pc'[q] = "L2" /\ q # p
                  BY Zenon DEF TypeOK
                <8>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
                  BY <4>2, Zenon DEF WellFormed, TypeOK
                <8>3. PICK i \in 1..Len(alpha) : alpha[i] = l[q]
                  BY <4>2, <5>2, FS_PermutationIndex
                <8>4. i \in k..Len(alpha)
                  BY <8>3
                <8>5. q \in pset
                  BY <8>3, <8>4
                <8>6. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
                  BY <8>2, <8>5
                <8> QED
                  BY <8>6, Zenon
              <7>2. CASE l[q] \notin IdxSet
                <8> USE <7>2
                <8>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <4>2, Zenon DEF WellFormed, TypeOK
                <8>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
                  BY <8>1
                <8> QED
                  BY <8>2, Zenon
              <7> QED
                BY <7>1, <7>2
            <6>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet_prev
              <7> USE <6>4
              <7>1. l[q] \in IdxSet
                BY <4>2 DEF Perm
              <7>2. pc'[q] = "L2" /\ q # p
                BY Zenon DEF TypeOK
              <7>3. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
                BY <4>2, <7>1, Zenon DEF WellFormed, TypeOK
              <7>4. q \notin pset
                BY DEF Perm
              <7>5. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <7>2, <7>3, <7>4
              <7> QED
                BY <7>5, Zenon
            <6>5. CASE pc[q] = "L3"
              <7> USE <6>5
              <7>1. pc'[q] = "L3" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>6. CASE pc[q] = "L4"
              <7> USE <6>6
              <7>1. pc'[q] = "L4" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>7. CASE pc[q] = "L5"
              <7> USE <6>7
              <7>1. pc'[q] = "L5" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>8. CASE pc[q] = "L6"
              <7> USE <6>8
              <7>1. pc'[q] = "L6" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
                BY <4>2, <7>1, Zenon DEF WellFormed, TypeOK
              <7>3. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q]
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6> QED
              BY RemDef, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, ZenonT(15) DEF TypeOK
          <5>13. c_prev \in S
            BY Zenon, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10, <5>11, <5>12 DEF S
          <5>14. c_prev \in P
            BY <5>13
          
          <5> DEFINE n == Len(alpha)-(k-1)
          
          <5>15. n \in Nat
            BY <5>3
            
          <5>16. pseq \in Seq(ProcSet)
            <6> SUFFICES ASSUME NEW m \in 1..Len(alpha)-(k-1)
                         PROVE  \E q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[m+(k-1)]
              BY DEF Seq
            <6> DEFINE z == m+(k-1)
            <6>1. z \in k..Len(alpha)
              OBVIOUS
            <6>2. alpha[z] \in IdxSet
              BY <4>2 DEF Perm
            <6>3. Val(alpha[z])' # BOT
              BY <4>1, <6>2, Zenon
            <6>4. A[alpha[z]] = BOT
              BY <5>4
            <6>5. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[z]
              BY <6>3, <6>4 DEF Val, TypeOK
            <6> QED
              BY <6>5
            
          <5>17. pseq \in Seq(pset)
            <6>1. DOMAIN pseq = 1..Len(alpha)-(k-1)
              OBVIOUS
            <6>2. \E u \in Nat : DOMAIN pseq = 1..u 
              OBVIOUS
            <6>3. \A x \in DOMAIN pseq : pseq[x] \in pset
              <7> SUFFICES ASSUME NEW x \in DOMAIN pseq
                           PROVE  pseq[x] \in pset
                OBVIOUS
              <7>1. x \in 1..Len(alpha)-(k-1)
                OBVIOUS
              <7> DEFINE y == x+(k-1)
              <7>2. y \in k..Len(alpha)
                OBVIOUS
              <7>3. alpha[y] \in IdxSet
                BY <4>2 DEF Perm
              <7>4. Val(alpha[y])' # BOT
                BY <4>1, <7>3, Zenon
              <7>5. A[alpha[y]] = BOT
                BY <5>4
              <7>6. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[y]
                BY <7>4, <7>5 DEF Val, TypeOK
              <7>7. q \in pset
                BY <7>6
              <7> QED
                BY <7>6, <7>7, Zenon
            <6>4. Seq(pset) = UNION {[1..u -> pset] : u \in Nat}
              BY DEF Seq
            <6>5. (\E u \in Nat : pseq \in [1..u -> pset]) => pseq \in Seq(pset)
              BY <6>4 DEF Seq
            <6>6. QED
              BY <6>2, <6>3, <6>5, Zenon
          
          <5>18. pseq \in Perm(pset)
            <6>2. Len(pseq) = Len(alpha)-(k-1)
              OBVIOUS
            <6>3. \A x, y \in 1..Len(pseq) : x # y => pseq[x] # pseq[y]
              <7> SUFFICES ASSUME NEW x \in 1..Len(pseq), NEW y \in 1..Len(pseq),
                                  x # y, pseq[x] = pseq[y]
                           PROVE  FALSE
                BY Zenon
              <7>1. alpha[x+(k-1)] \in IdxSet /\ alpha[y+(k-1)] \in IdxSet
                BY <4>2 DEF Perm
              <7>2. Val(alpha[x+(k-1)])' # BOT /\ Val(alpha[y+(k-1)])' # BOT
                BY <4>1, <7>1, Zenon
              <7>3. A[alpha[x+(k-1)]] = BOT /\ A[alpha[y+(k-1)]] = BOT
                BY <5>4
              <7>4. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[x+(k-1)]
                BY <7>2, <7>3 DEF Val, TypeOK 
              <7>5. PICK z \in ProcSet : pc'[z] = "L2" /\ l'[z] = alpha[y+(k-1)]
                BY <7>2, <7>3 DEF Val, TypeOK 
              <7>6. pseq[x] = q
                BY <7>4 
              <7>7. pseq[y] = z
                BY <7>5
              <7>8. alpha[x+(k-1)] # alpha[y+(k-1)]
                BY <4>2 DEF Perm
              <7>9. q # z
                BY <7>4, <7>5, <7>8
              <7> QED
                BY <7>6, <7>7, <7>9, Zenon
            <6>1. Len(pseq) = Cardinality(pset)
              <7>1. Len(pseq) = Len(alpha)-(k-1)
                OBVIOUS
              <7>2. pseq \in [1..Len(alpha)-(k-1) -> pset]
                BY <5>17 DEF Seq
              <7>3. pseq \in Injection(1..Len(alpha)-(k-1), pset)
                <8> SUFFICES ASSUME NEW a \in 1..Len(alpha)-(k-1), NEW b \in 1..Len(alpha)-(k-1),
                                    a # b
                             PROVE  pseq[a] # pseq[b]
                  BY <7>2, Zenon DEF Injection
                <8> QED
                  BY <7>1, <6>3, Zenon
              <7>4. pseq \in Surjection(1..Len(alpha)-(k-1), pset)
                <8> SUFFICES ASSUME NEW q \in pset
                             PROVE  \E z \in 1..Len(alpha)-(k-1) : pseq[z] = q
                  BY <7>2, Zenon DEF Surjection
                <8>2. PICK m \in k..Len(alpha) : pc'[q] = "L2" /\ l'[q] = alpha[m]
                  OBVIOUS
                <8> DEFINE z == m-(k-1)
                <8>3. z \in 1..Len(alpha)-(k-1)  
                  BY <8>2
                <8>4. pc'[q] = "L2" /\ l'[q] = alpha[z+(k-1)]
                  BY <8>2, <8>3
                <8>5. pseq[z] = q
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>3, <8>5, Zenon
              <7>5. ExistsBijection(1..Len(alpha)-(k-1), pset)
                BY <7>3, <7>4 DEF Bijection, ExistsBijection
              <7>6. Cardinality(pset) = Len(alpha)-(k-1)
                BY <7>5, FS_CountingElements
              <7> QED
                BY <7>1, <7>6
            <6> QED
              BY <5>17, <6>1, <6>3, Zenon DEF Perm
          
          <5> DEFINE bseq == [i \in 1..n+1 |-> CASE i = 1 -> c_prev
                                                 [] OTHER -> [state |-> c_prev.state \o [z \in 1..i-1 |-> arg[pseq[z]]],
                                                              op    |-> c_prev.op,
                                                              arg   |-> c_prev.arg,
                                                              res   |-> [q \in ProcSet |-> IF q \in Range(SubSeq(pseq, 1, i-1))
                                                                                              THEN ACK
                                                                                              ELSE c_prev.res[q]]]]
          
          <5>19. \A i \in 1..n : /\ bseq[i+1].state = bseq[i].state \o <<arg[pseq[i]]>>
                                 /\ bseq[i+1].op = bseq[i].op
                                 /\ bseq[i+1].arg = bseq[i].arg
                                 /\ bseq[i+1].res = [bseq[i].res EXCEPT ![pseq[i]] = ACK]
            <6> SUFFICES ASSUME NEW i \in 1..n
                         PROVE  /\ bseq[i+1].state = bseq[i].state \o <<arg[pseq[i]]>>
                                /\ bseq[i+1].op = bseq[i].op
                                /\ bseq[i+1].arg = bseq[i].arg
                                /\ bseq[i+1].res = [bseq[i].res EXCEPT ![pseq[i]] = ACK]
              BY Zenon
            <6>1. bseq[i+1].state = bseq[i].state \o <<arg[pseq[i]]>>
              <7> HIDE DEF pseq
              <7>1. bseq[i+1].state = c_prev.state \o [z \in 1..i |-> arg[pseq[z]]]
                BY Z3T(30)
              <7>2. bseq[i].state = c_prev.state \o [z \in 1..i-1 |-> arg[pseq[z]]]
                BY Z3T(30)
              <7> HIDE DEF bseq, pseq, c_prev
              <7>3. Len(bseq[i+1].state) = Len(c_prev.state) + i
                BY <7>1
              <7>4. Len(bseq[i].state \o <<arg[pseq[i]]>>) = Len(c_prev.state) + i
                BY <7>2
              <7>5. c_prev.state \in Seq(EltDomain)
                BY <5>5 DEF ConfigDomain, StateDomain
              <7> USE DEF pseq
              <7>6. \A z \in 1..i : pseq[z] \in ProcSet
                BY <5>16 DEF Seq
              <7>7. \A z \in 1..i : arg[pseq[z]] \in EltDomain
                BY <7>6, Zenon DEF TypeOK
              <7> HIDE DEF pseq
              <7>8. [z \in 1..i |-> arg[pseq[z]]] \in Seq(EltDomain)
                BY <7>7
              <7>9. [z \in 1..i-1 |-> arg[pseq[z]]] \in Seq(EltDomain)
                BY <7>7
              <7>10. bseq[i].state \in Seq(EltDomain)
                BY <7>2, <7>5, <7>9
              <7>11. <<arg[pseq[i]]>> \in Seq(EltDomain)
                BY <7>7
              <7>12. bseq[i].state \o <<arg[pseq[i]]>> \in Seq(EltDomain)
                BY <7>10, <7>11
              <7>13. bseq[i+1].state \in Seq(EltDomain)
                BY <7>1, <7>5, <7>8
              <7>A. [z \in 1..i |-> arg[pseq[z]]] = ([z \in 1..i-1 |-> arg[pseq[z]]] \o <<arg[pseq[i]]>>)
                OBVIOUS
              <7>B. bseq[i+1].state = c_prev.state \o ([z \in 1..i-1 |-> arg[pseq[z]]] \o <<arg[pseq[i]]>>)
                BY <7>1, <7>A
              <7>C. c_prev.state \o ([z \in 1..i-1 |-> arg[pseq[z]]] \o <<arg[pseq[i]]>>) = (c_prev.state \o [z \in 1..i-1 |-> arg[pseq[z]]]) \o <<arg[pseq[i]]>>
                BY <7>5, <7>9, <7>11, ConcatAssociative, Isa
              <7>D. bseq[i+1].state = c_prev.state \o [z \in 1..i-1 |-> arg[pseq[z]]] \o <<arg[pseq[i]]>>
                BY <7>B, <7>C, Zenon
              <7>E. bseq[i+1].state = bseq[i].state \o <<arg[pseq[i]]>>
                BY <7>2, <7>D
              <7> QED
                BY <7>E
            <6>2. bseq[i+1].op = bseq[i].op
              BY Z3T(15)
            <6>3. bseq[i+1].arg = bseq[i].arg
              BY Z3T(15)
            <6>4. bseq[i+1].res = [bseq[i].res EXCEPT ![pseq[i]] = ACK]
              <7>1. i # 1 => bseq[i].res = [q \in ProcSet |-> IF q \in Range(SubSeq(pseq, 1, i-1)) THEN ACK ELSE c_prev.res[q]]
                <8> HIDE DEF c_prev, pseq
                <8> QED  OBVIOUS
              <7>2. i = 1 => bseq[i].res = [q \in ProcSet |-> IF q \in  Range(SubSeq(pseq, 1, i-1)) THEN ACK ELSE c_prev.res[q]]
                <8>1. i = 1 => Range(SubSeq(pseq, 1, i-1)) = {}
                  BY DEF SubSeq, Range
                <8>2. i = 1 => [q \in ProcSet |-> IF q \in Range(SubSeq(pseq, 1, i-1)) THEN ACK ELSE c_prev.res[q]] = c_prev.res
                  BY <8>1
                <8>3. i = 1 => bseq[i].res = c_prev.res
                  OBVIOUS
                <8> QED
                  BY <8>2, <8>3, Zenon
              <7>3. bseq[i].res = [q \in ProcSet |-> IF q \in Range(SubSeq(pseq, 1, i-1)) THEN ACK ELSE c_prev.res[q]]
                BY <7>1, <7>2
              <7>4. bseq[i+1].res = [q \in ProcSet |-> IF q \in Range(SubSeq(pseq, 1, i)) THEN ACK ELSE c_prev.res[q]]
                <8> HIDE DEF c_prev, pseq
                <8>1. i+1 # 1
                  OBVIOUS
                <8> QED BY <8>1
              <7>5. \A q \in ProcSet : q \in Range(SubSeq(pseq, 1, i-1)) => q \in Range(SubSeq(pseq, 1, i))
                BY DEF Range, SubSeq
              <7>6. \A q \in ProcSet : (q \notin Range(SubSeq(pseq, 1, i-1)) /\ q \in Range(SubSeq(pseq, 1, i))) => q = pseq[i]
                BY DEF Range, SubSeq
              <7>7. \A q \in ProcSet : q \in Range(SubSeq(pseq, 1, i)) => q \in Range(SubSeq(pseq, 1, i-1)) \/ q = pseq[i]
                BY <7>5, <7>6
              <7>8. pseq \in Seq(ProcSet)
                BY <5>16, Zenon
              <7>9. \A h \in 1..i : pseq[h] \in ProcSet
                BY <5>17 DEF Seq
              <7>10. SubSeq(pseq, 1, i) \in Seq(ProcSet)
                <8> HIDE DEF pseq
                <8> QED  BY <7>9, SubSeqProperties
              <7>11. Range(SubSeq(pseq, 1, i)) \in SUBSET ProcSet
                <8> HIDE DEF pseq
                <8> QED  BY <7>10 DEF Range
              <7>12. \A q \in Range(SubSeq(pseq, 1, i)) : q \in Range(SubSeq(pseq, 1, i-1)) \/ q = pseq[i]
                <8> HIDE DEF pseq
                <8> QED  BY <7>7, <7>11
              <7>13. pseq[i] \in Range(SubSeq(pseq, 1, i))
                <8>1. SubSeq(pseq, 1, i) = [z \in 1..i |-> pseq[z]]
                  BY DEF SubSeq
                <8>2. Range(SubSeq(pseq, 1, i)) = {pseq[z] : z \in 1..i}
                  <9> HIDE DEF pseq
                  <9> QED  BY <8>1, Zenon DEF Range
                <8> QED
                  BY <8>2
              <7>14. Range(SubSeq(pseq, 1, i)) = Range(SubSeq(pseq, 1, i-1)) \union {pseq[i]}
                <8> HIDE DEF pseq, bseq
                <8> QED  BY <7>12, <7>13 DEF Range, SubSeq
              <7>15. \A q \in ProcSet : q # pseq[i] => bseq[i+1].res[q] = bseq[i].res[q]
                <8> HIDE DEF pseq, bseq, c_prev
                <8> QED  BY <7>3, <7>4, <7>12, <7>14
              <7>16. bseq[i+1].res[pseq[i]] = ACK
                <8> HIDE DEF pseq, bseq, c_prev
                <8>1. pseq[i] \in ProcSet
                  BY <7>9
                <8>2. pseq[i] \in Range(SubSeq(pseq, 1, i))
                  BY <7>13
                <8>3. bseq[i+1].res[pseq[i]] = ACK
                  BY <7>4, <8>1, <8>2
                <8> QED 
                  BY <8>3
              <7>17. bseq[i+1].res = [bseq[i].res EXCEPT ![pseq[i]] = ACK]
                <8> HIDE DEF bseq, pseq
                <8> QED  BY <7>3, <7>4, <7>15, <7>16, Zenon
              <7> QED
                BY <7>17, Zenon
            <6>5. QED
              BY <6>1, <6>2, <6>3, <6>4, Zenon
          
          <5>20. \A i \in 1..n : Delta(bseq[i], pseq[i], bseq[i+1])
            <6> SUFFICES ASSUME NEW i \in 1..n
                         PROVE  Delta(bseq[i], pseq[i], bseq[i+1])
              BY Zenon
            <6>1. bseq[i].op = c_prev.op /\ bseq[i].arg = c_prev.arg
              OBVIOUS
            <6>2. WellFormed(c_prev, IdxSet_prev)
              BY <5>12, Zenon
            <6>3. pseq[i] \in pset
              BY <5>18 DEF Perm
            <6>4. PICK m \in k..Len(alpha) : pc'[pseq[i]] = "L2" /\ l'[pseq[i]] = alpha[m]
              BY <6>3
            <6>5. c_prev.op[pseq[i]] = "ENQ" /\ c_prev.arg[pseq[i]] = arg[pseq[i]] /\ c_prev.res[pseq[i]] = BOT
              <7>1. CASE pseq[i] = p
                <8> USE <7>1
                <8>1. pc[pseq[i]] = "L1"
                  BY DEF TypeOK
                <8> QED
                  BY <5>12, <8>1, Zenon DEF WellFormed, TypeOK
              <7>2. CASE pseq[i] # p
                <8> USE <7>2
                <8>1. pc[pseq[i]] = "L2"
                  BY <6>4 DEF TypeOK
                <8>2. l[pseq[i]] = alpha[m]
                  BY <6>4 DEF TypeOK
                <8>3. \A z \in 1..Len(alpha) : z # m => alpha[z] # alpha[m]
                  BY DEF Perm
                <8>4. \A z \in 1..k-1 : alpha[z] # alpha[m]
                  BY <8>3
                <8>5. alpha[m] \notin IdxSet_prev
                  BY <8>4 DEF SubSeq
                <8>6. l[pseq[i]] \notin IdxSet_prev
                  BY <8>2, <8>5
                <8>7. pseq[i] \in ProcSet
                  OBVIOUS
                <8> HIDE DEF pseq
                <8> QED
                  BY <5>12, <8>1, <8>6, <8>7 DEF WellFormed
              <7> QED
                BY <7>1, <7>2
            <6>6. pseq[i] \in ProcSet
              BY <5>16 DEF Perm
            <6>7. arg[pseq[i]] \in EltDomain
              BY <6>6 DEF TypeOK
            <6>8. ArgsOf("ENQ") = EltDomain
              BY DEF ArgsOf
            <6>9. c_prev.op[pseq[i]] = "ENQ" /\ c_prev.arg[pseq[i]] \in ArgsOf("ENQ") /\ c_prev.res[pseq[i]] = BOT
              BY <6>5, <6>7, <6>8
            <6>10. \A z \in 1..n : i # z => pseq[i] # pseq[z]
              <7> DOMAIN pseq = 1..n 
                OBVIOUS
              <7> HIDE DEF pseq
              <7> QED  BY <5>18 DEF Perm
            <6>11. \A z \in 1..i-1 : pseq[z] # pseq[i]
              <7> HIDE DEF pseq
              <7> QED BY <6>10 
            <6>12. pseq[i] \notin Range(SubSeq(pseq, 1, i-1))
              <7> HIDE DEF pseq
              <7> QED  BY <6>11 DEF Range, SubSeq
            <6>13. bseq[i].res[pseq[i]] = BOT
              <7> HIDE DEF pseq
              <7> QED  BY <6>12, <6>6, <6>9
            <6>14. bseq[i].op[pseq[i]] = "ENQ" /\ bseq[i].arg[pseq[i]] \in ArgsOf("ENQ") /\ bseq[i].res[pseq[i]] = BOT
              BY <6>1, <6>13, <6>9, Zenon
            <6> HIDE DEF pseq, c_prev
            <6>15. c_prev.state \in Seq(EltDomain)
              BY <5>5 DEF ConfigDomain, StateDomain
            <6>16. \A z \in 1..i-1 : pseq[z] \in ProcSet
              BY <5>16 DEF Seq, pseq
            <6>17. \A z \in 1..i-1 : arg[pseq[z]] \in EltDomain
              BY <6>16 DEF TypeOK
            <6>18. [z \in 1..i-1 |-> arg[pseq[z]]] \in Seq(EltDomain)
              BY <6>17 DEF Seq
            <6>19. bseq[i].state \in Seq(EltDomain)
              BY <6>15, <6>18
            <6>20. arg[pseq[i]] \in EltDomain
              BY <6>6 DEF TypeOK
            <6>21. bseq[i+1].state = bseq[i].state \o <<arg[pseq[i]]>>
\*              BY <6>19, <6>24, Zenon
              BY <5>19, Zenon
            <6>22. bseq[i+1].state = Append(bseq[i].state, arg[pseq[i]])
              BY <6>19, <6>20, <6>21, AppendIsConcat, Isa
            <6>23. bseq[i+1].state = Append(bseq[i].state, bseq[i].arg[pseq[i]])
              BY <6>1, <6>5, <6>22, Zenon
            <6>24. bseq[i+1].op = bseq[i].op /\ bseq[i+1].arg = bseq[i].arg
              OBVIOUS
            <6>25. bseq[i+1].res = [bseq[i].res EXCEPT ![pseq[i]] = ACK]
              BY <5>19, Zenon
            <6> QED
              BY <6>14, <6>23, <6>24, <6>25 DEF Delta
          
          <5>21. bseq \in Seq(ConfigDomain) /\ bseq[n+1] \in ConfigDomain
            <6> HIDE DEF bseq
            <6> SUFFICES ASSUME TRUE
                         PROVE  bseq \in [1..n+1 -> ConfigDomain]
              BY DEF Seq
            <6>1. DOMAIN bseq = 1..n+1
              BY DEF bseq
            <6>2. \A i \in 1..n+1 : bseq[i] \in ConfigDomain
              <7> SUFFICES ASSUME NEW i \in 1..n+1
                           PROVE  bseq[i] \in ConfigDomain
                OBVIOUS
              <7> USE DEF bseq
              <7>1. bseq[i].op \in [ProcSet -> OpDomain]
                BY <3>2, <5>5 DEF ConfigDomain 
              <7>2. bseq[i].arg \in [ProcSet -> ArgDomain]
                BY <3>2, <5>5 DEF ConfigDomain 
              <7>3. bseq[i].state \in Seq(EltDomain)
                <8>1. \A z \in 1..i-1 : pseq[z] \in ProcSet
                  BY <5>16 DEF Seq, pseq
                <8>2. \A z \in 1..i-1 : arg[pseq[z]] \in EltDomain
                  BY <8>1, Zenon DEF TypeOK
                <8> HIDE DEF pseq
                <8>3. [z \in 1..i-1 |-> arg[pseq[z]]] \in Seq(EltDomain)
                  BY <8>2 DEF Seq
                <8>4. c_prev.state \in Seq(EltDomain)
                  BY <3>2, <5>5 DEF ConfigDomain, StateDomain
                <8>5. bseq[i].state \in Seq(EltDomain)
                  BY <8>3, <8>4
                <8> QED
                  BY <8>5
              <7>4. bseq[i].res \in [ProcSet -> ResDomain]
                BY <3>2, <5>5 DEF ConfigDomain, ResDomain
              <7> QED
                BY <7>1, <7>2, <7>3, <7>4 DEF ConfigDomain, StateDomain
            <6> HIDE DEF n
            <6> QED
              BY <6>1, <6>2, Zenon DEF bseq
          
          <5>22. bseq[n+1] = c
            <6>0. c \in ConfigDomain /\ bseq[n+1] \in ConfigDomain
              BY <3>2, <5>21, Zenon
            <6>1. bseq[n+1].op = c.op
              OBVIOUS
            <6>2. bseq[n+1].arg = c.arg
              OBVIOUS
            <6>3. bseq[n+1].state = c.state
              <7>1. bseq[n+1].state = c_prev.state \o [z \in 1..n |-> arg[pseq[z]]]
                <8> HIDE DEF pseq, c_prev
                <8> QED  BY Z3T(15)
              <7>2. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                BY <4>2
              <7>3. \A i \in 1..k-1 : c.state[i] = c_prev.state[i]
                BY DEF SubSeq
              <7>4. \A i \in 1..k-1 : c.state[i] = bseq[n+1].state[i]
                <8> HIDE DEF bseq
                <8> QED  BY <7>1, <7>3
              <7>5. bseq[n+1].state = [i \in 1..(Len(c_prev.state) + Len([z \in 1..n |-> arg[pseq[z]]])) 
                                          |-> IF i \leq Len(c_prev.state) 
                                                 THEN c_prev.state[i]
                                                 ELSE [z \in 1..n |-> arg[pseq[z]]][i-Len(c_prev.state)]]
                <8> HIDE DEF pseq, bseq, c_prev
                <8> QED  BY <7>1
              <7>6. Len([z \in 1..n |-> arg[pseq[z]]]) = n
                OBVIOUS
              <7>7. Len(c_prev.state) = k-1
                BY DEF SubSeq 
              <7>8. bseq[n+1].state = [i \in 1..(k-1+n)
                                          |-> IF i \leq k-1
                                                 THEN c_prev.state[i]
                                                 ELSE [z \in 1..n |-> arg[pseq[z]]][i-(k-1)]]
                <8> HIDE DEF pseq, bseq, c_prev
                <8> QED  BY <7>5, <7>6, <7>7, Zenon
              <7>9. bseq[n+1].state = [i \in 1..Len(alpha) |-> IF i \leq k-1
                                                                  THEN c_prev.state[i]
                                                                  ELSE [z \in 1..n |-> arg[pseq[z]]][i-(k-1)]]
                <8> HIDE DEF pseq, bseq, c_prev
                <8> QED  BY <7>8
              <7>10. \A i \in k..Len(alpha) : c.state[i] = bseq[n+1].state[i]
                <8> SUFFICES ASSUME NEW i \in k..Len(alpha)
                             PROVE  c.state[i] = bseq[n+1].state[i]
                  BY Zenon
                <8> HIDE DEF c_prev, pseq
                <8>1. c.state[i] = Val(alpha[i])'
                  BY <7>2
                <8>2. A[alpha[i]] = BOT
                  BY <5>4
                <8>3. alpha[i] \in IdxSet
                  BY <4>2 DEF Perm
                <8>4. Val(alpha[i])' # BOT
                  BY <4>1, <8>3, Zenon
                <8>5. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[i]
                  BY <8>2, <8>4 DEF Val
                <8>6. \A r \in ProcSet : (pc'[r] = "L2" /\ l'[q] = l'[r]) <=> q = r
                  BY <2>4, <8>5 DEF Inv2, TypeOK
                <8>7. c.state[i] = arg[q]
                  BY <8>1, <8>2, <8>5, <8>6 DEF Val
                <8>8. bseq[n+1].state[i] = [z \in 1..n |-> arg[pseq[z]]][i-(k-1)]
                  BY <7>9
                <8>9. i-(k-1) \in 1..n
                  OBVIOUS
                <8>10. bseq[n+1].state[i] = arg[pseq[i-(k-1)]]
                  BY <8>8, <8>9, Zenon
                <8>11. i-(k-1) \in 1..Len(alpha)-(k-1)
                  OBVIOUS
                <8>12. i-(k-1) \in 1..Len(alpha)-(k-1) => pseq[i-(k-1)] = CHOOSE r \in ProcSet : pc'[r] = "L2" /\ l'[r] = alpha[i-(k-1)+(k-1)]
                  BY Zenon DEF pseq
                <8>13. pseq[i-(k-1)] = CHOOSE r \in ProcSet : pc'[r] = "L2" /\ l'[r] = alpha[i]
                  BY <8>11, <8>12
                <8>14. pseq[i-(k-1)] = q
                  BY <8>5, <8>6, <8>13
                <8>15. bseq[n+1].state[i] = arg[q]
                  BY <8>10, <8>14, Zenon
                <8> QED
                  BY <8>7, <8>15, Zenon
              <7>11. \A i \in 1..Len(alpha) : c.state[i] = bseq[n+1].state[i]
                <8> HIDE DEF pseq, bseq, c_prev
                <8> QED  BY <7>4, <7>10
              <7> QED
                <8> HIDE DEF bseq, c_prev, pseq
                <8> QED BY <7>2, <7>9, <7>11
            <6>4. bseq[n+1].res = c.res
              <7>1. SubSeq(pseq, 1, n) = [i \in 1..n |-> pseq[i]]
                <8> HIDE DEF pseq
                <8> QED  BY DEF SubSeq
              <7>2. DOMAIN pseq = 1..n
                OBVIOUS
              <7>3. SubSeq(pseq, 1, n) = pseq
                BY <7>1, <7>2, Zenon
              <7>4. pseq \in Perm(pset)
                BY <5>18, Zenon
              <7>5. Range(pseq) = pset
                <8> HIDE DEF pset, pseq
                <8>1. IsFiniteSet(pset)
                  <9>1. pset \in SUBSET {q \in ProcSet : pc'[q] # "L0"}
                    BY DEF pset
                  <9> QED
                    BY <2>2, <9>1, FS_Subset DEF Inv0
                <8>2. \A x \in pset : x \in Range(pseq)
                  <9> HIDE DEF pset, pseq
                  <9> QED  BY FS_PermutationIndex, <7>4, <8>1 DEF Range
                <8>3. \A x \in Range(pseq) : x \in pset
                  BY <5>17 DEF Range, Seq
                <8> QED
                  BY <8>2, <8>3, Zenon
              <7> HIDE DEF pseq, c_prev
              <7>6. Range(SubSeq(pseq, 1, n)) = pset
                BY <7>3, <7>5, Zenon
              <7>7. bseq[n+1].res = [q \in ProcSet |-> IF q \in Range(SubSeq(pseq, 1, n)) THEN ACK ELSE c_prev.res[q]]
                BY <7>3
              <7>8. bseq[n+1].res = [q \in ProcSet |-> IF q \in pset THEN ACK ELSE c_prev.res[q]]
                BY <7>6, <7>7
              <7>9. c_prev.res = [q \in ProcSet |-> IF q \in pset THEN BOT ELSE c.res[q]]
                BY DEF c_prev
              <7>10. \A q \in ProcSet : q \notin pset => bseq[n+1].res[q] = c.res[q]
                BY <7>8, <7>9
              <7>11. \A q \in ProcSet : q \in pset => bseq[n+1].res[q] = ACK
                BY <7>8
              <7>12. \A q \in ProcSet : q \in pset => l'[q] \in IdxSet /\ pc'[q] = "L2"
                <8> SUFFICES ASSUME NEW q \in ProcSet, q \in pset
                             PROVE  l'[q] \in IdxSet /\ pc'[q] = "L2"
                  OBVIOUS
                <8>1. PICK m \in k..Len(alpha) : pc'[q] = "L2" /\ l'[q] = alpha[m]
                  OBVIOUS
                <8>2. alpha[m] \in IdxSet
                  BY <4>2 DEF Perm
                <8> QED
                  BY <8>1, <8>2
              <7>13. \A q \in ProcSet : l'[q] \in IdxSet /\ pc'[q] = "L2" => c.res[q] = ACK
                BY <4>2, Zenon DEF WellFormed
              <7>14. \A q \in ProcSet : q \in pset => c.res[q] = ACK
                BY <7>12, <7>13
              <7>15. \A q \in ProcSet : q \in pset => bseq[n+1].res[q] = c.res[q]
                BY <7>11, <7>14, Zenon
              <7>16. \A q \in ProcSet : bseq[n+1].res[q] = c.res[q]
                BY <7>10, <7>15, Zenon
              <7>17. bseq[n+1].res \in [ProcSet -> ResDomain]
                BY <5>5, <7>8 DEF ConfigDomain, ResDomain
              <7>18. c.res \in [ProcSet -> ResDomain]
                BY <3>2 DEF ConfigDomain
              <7> QED
                BY <7>17, <7>18, <7>16, Isa
            <6> HIDE DEF bseq
            <6> QED
              BY <6>0, <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain
          
          <5>23. Len(pseq) = n
            OBVIOUS
            
          <5>24. Len(bseq) = n+1
            OBVIOUS
            
          <5>25. bseq[1] = c_prev
            OBVIOUS
          
          <5>26. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                         PROVE  /\ c \in ConfigDomain
                                /\ \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
              BY Zenon DEF Evolve
            <6> HIDE DEF pseq, bseq
            <6> QED
              BY Z3T(10), <3>2, <5>14, <5>15, <5>16, <5>21, <5>23, <5>24, <5>25, <5>20, <5>22
          
          <5> QED
            BY <5>26
        <4> QED
          BY <4>3, <4>4
      <3>5. ASSUME NEW p \in ProcSet,
                   L2(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>5 DEF L2
        <4>1. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>2. IdxSet \in SUBSET 0..(L-1)
          BY <4>1
        <4>3A. \A m \in IdxSet : Val(m) # BOT
          <5> SUFFICES ASSUME NEW m \in IdxSet
                       PROVE  Val(m) # BOT
            OBVIOUS
          <5>1. Val(m)' # BOT
            BY <4>1
          <5>2. CASE A'[m] # BOT
            <6> USE <5>2
            <6> SUFFICES ASSUME A'[m] # A[m], A[m] = BOT
                         PROVE  Val(m) # BOT
              BY <5>1, <5>2 DEF Val
            <6>1. m = l[p]
              OBVIOUS
            <6>2. pc[p] = "L2" /\ l[p] = m
              OBVIOUS
            <6>3. \A r \in ProcSet : (pc[r] = "L2" /\ l[p] = l[r]) <=> p = r
              BY <6>2 DEF Inv2
            <6>4. Val(m) = arg[p]
              BY <6>2, <6>3 DEF Val
            <6> QED
              BY BotDef, <6>4 DEF TypeOK
          <5>3. CASE A'[m] = BOT /\ \E q \in ProcSet : pc'[q] = "L2" /\ l'[q] = m 
            <6> USE <5>3
            <6>1. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = m 
              OBVIOUS
            <6>2. pc[q] = "L2" /\ l[q] = m
              BY <6>1 DEF TypeOK
            <6>3. A[m] = BOT
              BY <6>2 DEF InvE
            <6>4. \A r \in ProcSet : (pc[r] = "L2" /\ l[q] = l[r]) <=> q = r
              BY <6>2 DEF Inv2
            <6>5. Val(m) = arg[q]
              BY <6>2, <6>3, <6>4 DEF Val
            <6> QED
              BY BotDef, <6>1, <6>5 DEF TypeOK
          <5> QED
            BY <5>1, <5>2, <5>3 DEF Val
        <4>3B. \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          <5> SUFFICES ASSUME NEW m \in 0..(L-1), A[m] # BOT
                       PROVE  m \in IdxSet
            OBVIOUS
          <5>1. A'[m] # BOT => m \in IdxSet
            BY <4>1
          <5>2. A[m] # A'[m] => m = l[p]
            OBVIOUS
          <5>3. A'[m] # BOT => A[m] # BOT \/ m = l[p]
            BY <5>1, <5>2
          <5>4. A'[l[p]] # BOT
            BY BotDef DEF TypeOK
          <5>5. l[p] \in IdxSet
            BY <4>1, <5>4 DEF TypeOK, Inv1
          <5> QED
            BY <5>1, <5>3, <5>5
        <4>3. /\ \A m \in IdxSet : Val(m) # BOT
              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          BY <4>3A, <4>3B
        <4>4. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>1
        <4>5. Justified(alpha)
          <5> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                              m < n
                       PROVE  \/ alpha[m] < alpha[n]
                              \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                         /\ alpha[n] < j[q]
                                                                         /\ alpha[m] < l[q]
            BY DEF Justified
          <5>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
            BY <4>2, <4>4 DEF Perm
          <5>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
            BY <4>2, <5>1, Zenon
          <5> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                       PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <4>2, <5>2 DEF Perm
          <5>3. alpha[n] # l[p]
            BY DEF InvE
          <5>4. A[alpha[n]] = A'[alpha[n]]
            BY <5>3 DEF TypeOK
          <5>5. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
            BY <4>4, <5>1, <5>2, <5>4 DEF Justified
          <5>6. q # p
            BY <5>3, <5>5 DEF TypeOK
          <5>7. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <5>5, <5>6 DEF TypeOK
          <5> QED
            BY <5>7
        <4>6. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          <5> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                       PROVE  Val(alpha[i])' = Val(alpha[i])
            BY <4>1, <4>4
          <5>1. CASE A[alpha[i]] # BOT
            BY <5>1 DEF Val, TypeOK, InvE
          <5>2. CASE A[alpha[i]] = BOT /\ ~(\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
            BY <5>2, <4>4 DEF Val
          <5>3. CASE A[alpha[i]] = BOT /\ (\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
            BY <5>3, <4>4 DEF Val, Inv2, TypeOK
          <5> QED
            BY <5>1, <5>2, <5>3 DEF Val
        <4>7. WellFormed(c, IdxSet)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  CASE pc[q] = "L0" 
                                     -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                [] pc[q] = "L1"
                                     -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \notin IdxSet
                                     -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \in IdxSet
                                     -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
                                [] pc[q] = "L3"
                                     -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
                                [] pc[q] = "L4"
                                     -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                [] pc[q] = "L5"
                                     -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                [] pc[q] = "L6"
                                     -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q])
            BY Zenon DEF WellFormed
          <5>1. CASE pc[q] = "L0"
            BY <4>4, <5>1, Zenon DEF WellFormed, TypeOK
          <5>2. CASE pc[q] = "L1"
            BY <4>4, <5>2, Zenon DEF WellFormed, TypeOK
          <5>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet
            <6> USE <5>3
            <6>1. CASE q = p
              <7> USE <6>1
              <7>1. A'[l[q]] # BOT
                BY BotDef DEF TypeOK
              <7>2. l[q] \in IdxSet
                BY <7>1, <4>1 DEF TypeOK, Inv1
              <7> QED
                BY <7>2
            <6>2. CASE q # p
              BY <4>4, <6>2, Zenon DEF WellFormed, TypeOK
            <6> QED
              BY <6>1, <6>2, Zenon
          <5>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet
            BY <4>4, <5>4, Zenon DEF WellFormed, TypeOK
          <5>5. CASE pc[q] = "L3"
            BY <4>4, <5>5, Zenon DEF WellFormed, TypeOK
          <5>6. CASE pc[q] = "L4"
            BY <4>4, <5>6, Zenon DEF WellFormed, TypeOK
          <5>7. CASE pc[q] = "L5"
            BY <4>4, <5>7, Zenon DEF WellFormed, TypeOK
          <5>8. CASE pc[q] = "L6"
            BY <4>4, <5>8, Zenon DEF WellFormed, TypeOK
          <5> QED
            BY RemDef, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, ZenonT(15) DEF TypeOK
        <4>8. c \in S
          BY Zenon, <3>2, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF S
        <4>9. c \in P
          BY <4>8
        <4> DEFINE aseq == << >>
        <4> DEFINE beta == <<c>>
        <4> DEFINE n    == 0
        <4>10. n \in Nat
          OBVIOUS
        <4>11. aseq \in Seq(ProcSet)
          OBVIOUS
        <4>12. beta \in Seq(ConfigDomain)
          BY <3>2
        <4>13. Len(aseq) = n
          OBVIOUS
        <4>14. Len(beta) = n+1
          OBVIOUS
        <4>15. beta[1] = c
          OBVIOUS
        <4>16. \A i \in 1..n : Delta(beta[i], aseq[i], beta[i+1])
          OBVIOUS
        <4>17. beta[n+1] = c
          OBVIOUS
        <4>18. c \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E aseq_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(aseq_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], aseq_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
            BY <4>1 DEF Evolve
          <5> QED
            BY Zenon, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16, <4>17
        <4> QED
          BY <4>18
      <3>6. ASSUME NEW p \in ProcSet,
                   L3(p), 
                   P' = Filter(Evolve(P), p, (ret')[p])
            PROVE  c \in P'
        <4> USE <3>6 DEF L3
        <4>1. ret'[p] = ACK
          BY DEF TypeOK
        <4> USE <4>1
        <4>2. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>3. IdxSet \in SUBSET 0..(L-1)
          BY <4>2
        <4>4. /\ \A m \in IdxSet : Val(m) # BOT
              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          BY <4>2, Z3T(10) DEF Val
        <4>5. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>2
        <4>6. Justified(alpha)
          <5> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                              m < n
                       PROVE  \/ alpha[m] < alpha[n]
                              \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                         /\ alpha[n] < j[q]
                                                                         /\ alpha[m] < l[q]
            BY DEF Justified
          <5>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
            BY <4>3, <4>5 DEF Perm
          <5>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
            BY <4>3, <5>1, Zenon
          <5> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                       PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <4>3, <5>2 DEF Perm
          <5>3. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
            BY <4>5, <5>2 DEF Justified
          <5>4. q # p
            BY <5>2, <5>3 DEF TypeOK
          <5>5. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <5>3, <5>4 DEF TypeOK
          <5> QED
            BY <5>5 
        <4> DEFINE c_prev == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "ENQ"],
                              arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                              res   |-> [c.res EXCEPT ![p] = ACK]]
        <4>7. c_prev \in ConfigDomain
          BY <3>2 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
        <4>8. c_prev.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          BY <4>5 DEF Val, TypeOK
        <4>9. WellFormed(c_prev, IdxSet)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  CASE pc[q] = "L0" 
                                     -> (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L1"
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \notin IdxSet
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \in IdxSet
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                [] pc[q] = "L3"
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                [] pc[q] = "L4"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L5"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L6"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q])
            BY Zenon DEF WellFormed
          <5>1. CASE pc[q] = "L0"
            <6> USE <5>1
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>2. CASE pc[q] = "L1"
            <6> USE <5>2
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet
            <6> USE <5>3
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2, Zenon
          <5>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet
            <6> USE <5>4
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
              BY <6>0, <6>1
            <6> QED
              BY <6>2, Zenon
          <5>5. CASE pc[q] = "L3"
            <6> USE <5>5
            <6>1. CASE p = q
              <7>1. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <6>1, <4>7 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
              <7> QED
                BY <7>1
            <6>2. CASE p # q
              <7>1. c.op[q] = "ENQ" /\ c.arg[q] = arg'[q] /\ c.res[q] = ACK
                BY <4>5, <6>2, Zenon DEF WellFormed, TypeOK
              <7>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <6>2, <7>1
              <7> QED
                BY <7>2
            <6> QED
              BY <6>1, <6>2
          <5>6. CASE pc[q] = "L4"
            <6> USE <5>6
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>7. CASE pc[q] = "L5"
            <6> USE <5>7
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>8. CASE pc[q] = "L6"
            <6> USE <5>8
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q]
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5> QED
            BY RemDef, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, ZenonT(15) DEF TypeOK
        <4>10. c_prev \in S
          BY Zenon, <4>7, <4>2, <4>3, <4>4, <4>5, <4>6, <4>6, <4>8, <4>9 DEF S
        <4>11. c_prev \in P
          BY <4>10
        <4> DEFINE pseq == << >>
        <4> DEFINE beta  == <<c_prev>>
        <4> DEFINE n     == 0
        <4>12. n \in Nat
          OBVIOUS
        <4>13. pseq \in Seq(ProcSet)
          OBVIOUS
        <4>14. beta \in Seq(ConfigDomain)
          BY <4>7
        <4>15. Len(pseq) = n
          OBVIOUS
        <4>16. Len(beta) = n+1
          OBVIOUS
        <4>17. beta[1] = c_prev
          OBVIOUS
        <4>18. \A i \in 1..n : Delta(beta[i], pseq[i], beta[i+1])
          OBVIOUS
        <4>19. beta[n+1] = c_prev
          OBVIOUS
        <4>20. c_prev \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c_prev
            BY Zenon, <4>7 DEF Evolve
          <5> QED
            BY Zenon, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16, <4>17, <4>18, <4>19
        
        <4>21. c_prev.res[p] = ACK
          BY <3>2 DEF ConfigDomain
        <4>22. c.op = [c_prev.op EXCEPT ![p] = BOT]
          <5>1. \A q \in ProcSet : p # q => c.op[q] = c_prev.op[q]
            OBVIOUS
          <5>2. c.op[p] = BOT
            BY <4>5, Zenon DEF TypeOK, WellFormed
          <5> QED
            BY <3>2, <5>1, <5>2, Zenon DEF ConfigDomain
        <4>23. c.arg = [c_prev.arg EXCEPT ![p] = BOT]
          <5>1. \A q \in ProcSet : p # q => c.arg[q] = c_prev.arg[q]
            OBVIOUS
          <5>2. c.arg[p] = BOT
            BY <4>5, Zenon DEF TypeOK, WellFormed
          <5> QED
            BY <3>2, <5>1, <5>2, Zenon DEF ConfigDomain
        <4>24. c.res = [c_prev.res EXCEPT ![p] = BOT]
          <5>1. \A q \in ProcSet : p # q => c.res[q] = c_prev.res[q]
            OBVIOUS
          <5>2. c.res[p] = BOT
            BY <4>5, Zenon DEF TypeOK, WellFormed
          <5> QED
            BY <3>2, <5>1, <5>2, Zenon DEF ConfigDomain
        <4>25. c.state = c_prev.state
          OBVIOUS
        <4>26. c \in Filter(Evolve(P), p, ACK)
          BY Zenon, <3>2, <4>20, <4>21, <4>22, <4>23, <4>24, <4>25 DEF Filter
        <4> QED
          BY <4>26
      <3>7. ASSUME NEW p \in ProcSet,
                   L4(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>7 DEF L4
        <4>1. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>2. IdxSet \in SUBSET 0..(L-1)
          BY <4>1
        <4>3. /\ \A m \in IdxSet : Val(m) # BOT
              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          BY <4>1, Z3T(10) DEF Val
        <4>4. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>1
        <4>5. Justified(alpha)
          <5> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                              m < n
                       PROVE  \/ alpha[m] < alpha[n]
                              \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                         /\ alpha[n] < j[q]
                                                                         /\ alpha[m] < l[q]
            BY DEF Justified
          <5>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
            BY <4>2, <4>4 DEF Perm
          <5>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
            BY <4>2, <5>1, Zenon
          <5> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                       PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <4>2, <5>2 DEF Perm
          <5>3. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
            BY <4>4, <5>2 DEF Justified
          <5>4. q # p
            BY <5>2, <5>3 DEF TypeOK
          <5>5. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <5>3, <5>4 DEF TypeOK
          <5> QED
            BY <5>5
        <4>6. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          <5> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                       PROVE  Val(alpha[i])' = Val(alpha[i])
            BY <4>1, <4>4
          <5>1. CASE A[alpha[i]] # BOT
            BY <5>1, <4>4 DEF Val
          <5>2. CASE A[alpha[i]] = BOT /\ ~(\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
            BY <5>2, <4>4 DEF Val
          <5>3. CASE A[alpha[i]] = BOT /\ (\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
            BY <5>3, <4>4 DEF Val, Inv2
          <5> QED
            BY <4>4, <5>3 DEF Val
        <4>7. WellFormed(c, IdxSet)
          BY <4>4, ZenonT(15) DEF WellFormed, TypeOK
        <4>8. c \in S
          BY Zenon, <3>2, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF S
        <4>9. c \in P
          BY <4>8
        <4> DEFINE aseq == << >>
        <4> DEFINE beta == <<c>>
        <4> DEFINE n    == 0
        <4>10. n \in Nat
          OBVIOUS
        <4>11. aseq \in Seq(ProcSet)
          OBVIOUS
        <4>12. beta \in Seq(ConfigDomain)
          BY <3>2
        <4>13. Len(aseq) = n
          OBVIOUS
        <4>14. Len(beta) = n+1
          OBVIOUS
        <4>15. beta[1] = c
          OBVIOUS
        <4>16. \A i \in 1..n : Delta(beta[i], aseq[i], beta[i+1])
          OBVIOUS
        <4>17. beta[n+1] = c
          OBVIOUS
        <4>18. c \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E aseq_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(aseq_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], aseq_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c
            BY <4>1 DEF Evolve
          <5> QED
            BY Zenon, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16, <4>17
        <4> QED
          BY <4>18
      <3>8. ASSUME NEW p \in ProcSet,
                   L5(p),
                   P' = Evolve(P)
            PROVE  c \in P'
        <4> USE <3>8 DEF L5
        <4>1. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>2. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>1
        <4>3. CASE (j[p] = l[p])
          <5> USE <4>3
          <5>1. /\ \A m \in IdxSet : Val(m) # BOT
                /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
            BY <4>1 DEF Val, TypeOK
          <5>2. Justified(alpha)
            <6> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                                m < n
                         PROVE  \/ alpha[m] < alpha[n]
                                \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                           /\ alpha[n] < j[q]
                                                                           /\ alpha[m] < l[q]
              BY DEF Justified
            <6>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
              BY <4>1, <4>2 DEF Perm
            <6>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
              BY <4>2, <6>1, Zenon
            <6> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                         PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <4>2, <6>2 DEF Perm
            <6>3. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
              BY <4>1, <4>2, <6>2 DEF Justified
            <6>4. q # p
              BY <6>2, <6>3 DEF TypeOK
            <6>5. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <6>3, <6>4 DEF TypeOK
            <6> QED
              BY <6>5
          <5>3. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
            <6> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                         PROVE  Val(alpha[i])' = Val(alpha[i])
              BY <4>1, <4>2
            <6>1. CASE A[alpha[i]] # BOT
              BY <6>1, <4>2 DEF Val
            <6>2. CASE A[alpha[i]] = BOT /\ ~(\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>2, <4>2 DEF Val, TypeOK
            <6>3. CASE A[alpha[i]] = BOT /\ (\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>3, <4>2 DEF Val, TypeOK
            <6> QED
              BY <6>1, <6>2, <6>3, Zenon
          <5>4. WellFormed(c, IdxSet)
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc[q] = "L0" 
                                       -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                  [] pc[q] = "L1"
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \notin IdxSet
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \in IdxSet
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
                                  [] pc[q] = "L3"
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
                                  [] pc[q] = "L4"
                                       -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                  [] pc[q] = "L5"
                                       -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                  [] pc[q] = "L6"
                                       -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q])
              BY Zenon DEF WellFormed
            <6>1. CASE pc[q] = "L0"
              BY <4>1, <6>1, Zenon DEF WellFormed, TypeOK
            <6>2. CASE pc[q] = "L1"
              BY <4>1, <6>2, Zenon DEF WellFormed, TypeOK
            <6>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet
              BY <4>1, <6>3, Zenon DEF WellFormed, TypeOK
            <6>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet
              BY <4>1, <6>4, Zenon DEF WellFormed, TypeOK
            <6>5. CASE pc[q] = "L3"
              BY <4>1, <6>5, Zenon DEF WellFormed, TypeOK
            <6>6. CASE pc[q] = "L4"
              BY <4>1, <6>6, Zenon DEF WellFormed, TypeOK
            <6>7. CASE pc[q] = "L5"
              BY <4>1, <6>7, Zenon DEF WellFormed, TypeOK
            <6>8. CASE pc[q] = "L6"
              BY <4>1, <6>8, Zenon DEF WellFormed, TypeOK
            <6> QED
              BY RemDef, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, ZenonT(15) DEF TypeOK
          <5>5. c \in S
            BY Zenon, <3>2, <4>1, <4>2, <5>1, <5>2, <5>3, <5>4 DEF S
          <5>6. c \in P
            BY <5>5
          <5> DEFINE aseq == << >>
          <5> DEFINE beta == <<c>>
          <5> DEFINE n    == 0
          <5>7. n \in Nat
            OBVIOUS
          <5>8. aseq \in Seq(ProcSet)
            OBVIOUS
          <5>9. beta \in Seq(ConfigDomain)
            BY <3>2
          <5>10. Len(aseq) = n
            OBVIOUS
          <5>11. Len(beta) = n+1
            OBVIOUS
          <5>12. beta[1] = c
            OBVIOUS
          <5>13. \A i \in 1..n : Delta(beta[i], aseq[i], beta[i+1])
            OBVIOUS
          <5>14. beta[n+1] = c
            OBVIOUS
          <5>15. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                         PROVE  \E poss_old \in P : \E n_ \in Nat : \E aseq_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                      /\ Len(aseq_) = n_
                                      /\ Len(beta_) = n_ + 1
                                      /\ beta_[1] = poss_old
                                      /\ \A i \in 1..n_ : Delta(beta_[i], aseq_[i], beta_[i+1])
                                      /\ beta_[n_+1] = c
              BY <4>1 DEF Evolve
            <6> QED
              BY Zenon, <5>6, <5>7, <5>8, <5>9, <5>10, <5>11, <5>12, <5>13, <5>14
          <5> QED
            BY <5>15
        <4>4. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
          <5> USE <4>4
          <5>1. /\ \A m \in IdxSet : Val(m) # BOT
                /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
            BY <4>1 DEF Val, TypeOK
          <5>2. Justified(alpha)
            <6> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                                m < n
                         PROVE  \/ alpha[m] < alpha[n]
                                \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                           /\ alpha[n] < j[q]
                                                                           /\ alpha[m] < l[q]
              BY DEF Justified
            <6>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
              BY <4>1, <4>2 DEF Perm
            <6>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
              BY <4>2, <6>1, Zenon
            <6> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                         PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
              BY <4>2, <6>2 DEF Perm
            <6>3. A'[alpha[n]] # BOT => (\E q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q])
              BY <4>2, <6>1, <6>2 DEF Justified
            <6>4. A' = [A EXCEPT ![j[p]] = BOT]
              OBVIOUS
            <6>5. A'[alpha[n]] = A[alpha[n]]
              BY <6>4
            <6>6. alpha[n] # j[p]
              OBVIOUS
            <6>7. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
              BY <6>3, <6>5
            <6>8. CASE q = p
              <7>0. pc[q] = "L5" /\ alpha[n] < j[p] + 1 /\ alpha[m] < l[p]
                BY <6>7, <6>8 DEF TypeOK
              <7>1. alpha[n] # j[p]
                BY <4>1, <4>2, <6>8 DEF WellFormed, Justified, TypeOK, Inv3
              <7>2. pc[q] = "L5" /\ alpha[n] < j[p] /\ alpha[m] < l[p]
                BY <6>1, <7>0, <7>1 DEF TypeOK
              <7> QED 
                BY <7>2
            <6>9. CASE q # p
              BY <6>7, <6>9 DEF TypeOK
            <6> QED
              BY <6>8, <6>9
          <5>3. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
            <6> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                         PROVE  Val(alpha[i])' = Val(alpha[i])
              BY <4>1, <4>2
            <6>1. CASE A[alpha[i]] # BOT
              BY <6>1, <4>2, Zenon DEF Val, TypeOK
            <6>2. CASE A[alpha[i]] = BOT /\ ~(\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              <7>1. Val(alpha[i]) = BOT
                BY <6>2 DEF Val
              <7>X. ~(\E q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[i])
                BY <6>2 DEF TypeOK
              <7>Y. A' = [A EXCEPT ![j[p]] = BOT]
                OBVIOUS
              <7>Z. alpha[i] # j[p] => A'[alpha[i]] = BOT
                BY <6>2, <7>Y DEF TypeOK 
              <7>Q. alpha[i] = j[p] => A'[alpha[i]] = BOT
                BY <7>Y
              <7>H. A'[alpha[i]] = BOT
                BY <7>Z, <7>Q
              <7>2. Val(alpha[i])' = BOT
                BY <7>X, <7>H DEF Val
              <7> QED
                BY <7>1, <7>2
            <6>3. CASE A[alpha[i]] = BOT /\ (\E q \in ProcSet : pc[q] = "L2" /\ l[q] = alpha[i])
              BY <6>3, <4>2 DEF Val, TypeOK
            <6> QED
              BY <6>1, <6>2, <6>3, Zenon
          <5>4. WellFormed(c, IdxSet)
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc[q] = "L0" 
                                       -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                  [] pc[q] = "L1"
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \notin IdxSet
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \in IdxSet
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
                                  [] pc[q] = "L3"
                                       -> (c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
                                  [] pc[q] = "L4"
                                       -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                  [] pc[q] = "L5"
                                       -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                                  [] pc[q] = "L6"
                                       -> (c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q])
              BY Zenon DEF WellFormed
            <6>1. CASE pc[q] = "L0"
              BY <4>1, <6>1, Zenon DEF WellFormed, TypeOK
            <6>2. CASE pc[q] = "L1"
              BY <4>1, <6>2, Zenon DEF WellFormed, TypeOK
            <6>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet
              BY <4>1, <6>3, Zenon DEF WellFormed, TypeOK
            <6>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet
              BY <4>1, <6>4, Zenon DEF WellFormed, TypeOK
            <6>5. CASE pc[q] = "L3"
              BY <4>1, <6>5, Zenon DEF WellFormed, TypeOK
            <6>6. CASE pc[q] = "L4"
              BY <4>1, <6>6, Zenon DEF WellFormed, TypeOK
            <6>7. CASE pc[q] = "L5"
              BY <4>1, <6>7, Zenon DEF WellFormed, TypeOK
            <6>8. CASE pc[q] = "L6"
              BY <4>1, <6>8, Zenon DEF WellFormed, TypeOK
            <6> QED
              BY RemDef, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, ZenonT(15) DEF TypeOK
          <5>5. c \in S
            BY Zenon, <3>2, <4>1, <4>2, <5>1, <5>2, <5>3, <5>4 DEF S
          <5>6. c \in P
            BY <5>5
          <5> DEFINE aseq == << >>
          <5> DEFINE beta == <<c>>
          <5> DEFINE n    == 0
          <5>7. n \in Nat
            OBVIOUS
          <5>8. aseq \in Seq(ProcSet)
            OBVIOUS
          <5>9. beta \in Seq(ConfigDomain)
            BY <3>2
          <5>10. Len(aseq) = n
            OBVIOUS
          <5>11. Len(beta) = n+1
            OBVIOUS
          <5>12. beta[1] = c
            OBVIOUS
          <5>13. \A i \in 1..n : Delta(beta[i], aseq[i], beta[i+1])
            OBVIOUS
          <5>14. beta[n+1] = c
            OBVIOUS
          <5>15. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                         PROVE  \E poss_old \in P : \E n_ \in Nat : \E aseq_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                      /\ Len(aseq_) = n_
                                      /\ Len(beta_) = n_ + 1
                                      /\ beta_[1] = poss_old
                                      /\ \A i \in 1..n_ : Delta(beta_[i], aseq_[i], beta_[i+1])
                                      /\ beta_[n_+1] = c
              BY <4>1 DEF Evolve
            <6> QED
              BY Zenon, <5>6, <5>7, <5>8, <5>9, <5>10, <5>11, <5>12, <5>13, <5>14
          <5> QED
            BY <5>15
        <4>5. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
          <5> USE <4>5
          <5> DEFINE c_prev == [state |-> <<A[j[p]]>> \o c.state,
                                op    |-> c.op,
                                arg   |-> c.arg,
                                res   |-> [c.res EXCEPT ![p] = BOT]]
          <5> DEFINE IdxSet_prev == IdxSet \union {j[p]}
          <5> DEFINE alpha_prev == <<j[p]>> \o alpha
          <5>1. j[p] \notin IdxSet
            <6> SUFFICES ASSUME j[p] \in IdxSet
                         PROVE  FALSE
              OBVIOUS
            <6>0. A' = [A EXCEPT ![j[p]] = BOT]
              BY Zenon
            <6>1. A'[j[p]] = BOT
              BY <6>0 DEF TypeOK
            <6>2. Val(j[p])' # BOT
              BY <4>1, Zenon
            <6>3. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = j[p]
              BY <6>1, <6>2, Zenon DEF Val
            <6>4. pc[q] = "L2" /\ l[q] = j[p]
              BY <6>3, Zenon DEF TypeOK
            <6>5. A[l[q]] = BOT
              BY <6>4 DEF InvE
            <6> QED
              BY <6>4, <6>5
          <5>2. c_prev \in ConfigDomain
            <6>1. c_prev.state \in Seq(EltDomain)
              <7>1. <<A[j[p]]>> \in Seq(EltDomain)
                BY DEF TypeOK, Seq
              <7>2. c.state \in Seq(EltDomain)
                BY <3>2 DEF ConfigDomain, StateDomain
              <7> QED
                BY <7>1, <7>2, ConcatProperties
            <6>2. c_prev.op \in [ProcSet -> OpDomain]
              BY <3>2 DEF ConfigDomain
            <6>3. c_prev.arg \in [ProcSet -> ArgDomain]
              BY <3>2 DEF ConfigDomain
            <6>4. c_prev.res \in [ProcSet -> ResDomain]
              BY <3>2 DEF ConfigDomain, StateDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4, Zenon DEF ConfigDomain, StateDomain
          <5>3. IdxSet_prev \in SUBSET 0..(L-1)
            <6> SUFFICES ASSUME NEW m \in IdxSet_prev
                         PROVE  m \in 0..(L-1)
              OBVIOUS
            <6>1. CASE m = j[p]
              <7>1. j[p] \in 0..l[p] /\ l[p] <= L
                BY DEF Inv3
              <7>2. j[p] # l[p]
                BY <6>1
              <7>3. j[p] \in 0..l[p]-1
                BY <7>1, <7>2 DEF TypeOK
              <7>4. 0..l[p]-1 \in SUBSET 0..L-1
                BY <7>1 DEF TypeOK
              <7>5. j[p] \in 0..L-1
                BY <7>3, <7>4
              <7> QED
                BY <6>1, <7>5
            <6>2. CASE m \in IdxSet
              BY <6>2, Zenon
            <6> QED
              BY <6>1, <6>2
          <5>4. \A m \in IdxSet_prev : Val(m) # BOT
            <6> SUFFICES ASSUME NEW m \in IdxSet_prev
                         PROVE  Val(m) # BOT
              OBVIOUS
            <6>1. CASE m = j[p]
              BY <6>1 DEF Val
            <6>2. CASE m # j[p]
              <7> USE <6>2
              <7>1. Val(m)' # BOT
                BY <4>1
              <7>2. A' = [A EXCEPT ![j[p]] = BOT]
                BY Zenon
              <7>3. A[m] = A'[m]
                BY <7>2 DEF TypeOK
              <7>4. \A q \in ProcSet : (pc[q] = "L2" /\ l[q] = m) <=> (pc'[q] = "L2" /\ l'[q] = m)
                BY Zenon DEF TypeOK
              <7>5. CASE A'[m] # BOT
                BY <7>5, <7>3 DEF Val
              <7>6. CASE A'[m] = BOT /\ \E q \in ProcSet : pc'[q] = "L2" /\ l'[q] = m
                <8> USE <7>6
                <8>1. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = m
                  OBVIOUS
                <8>2. \A r \in ProcSet : (pc'[r] = "L2" /\ l'[r] = l'[q]) => q = r
                  BY <2>4, <8>1 DEF Inv2
                <8>3. Val(m)' = arg[q]
                  BY <8>1, <8>2, Zenon DEF Val
                <8>4. pc[q] = "L2" /\ l[q] = m
                  BY <7>4, <8>1
                <8>5. \A r \in ProcSet : (pc[r] = "L2" /\ l[r] = l[q]) => q = r
                  BY <8>4 DEF Inv2
                <8>6. Val(m) = arg[q]
                  BY <7>3, <8>4, <8>5 DEF Val
                <8> QED
                  BY <8>6, <8>3, <7>1
              <7> QED
                BY <7>1, <7>5, <7>6 DEF Val
            <6> QED
              BY <6>1, <6>2
          <5>5. \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet_prev
            <6> SUFFICES ASSUME NEW m \in 0..(L-1),
                                A[m] # BOT
                         PROVE  m \in IdxSet_prev
              OBVIOUS
            <6>1. CASE m = j[p]
              BY <6>1
            <6>2. CASE m # j[p]
              <7> USE <6>2
              <7>1. A'[m] # BOT => m \in IdxSet
                BY <4>1, Zenon DEF TypeOK
              <7>2. A' = [A EXCEPT ![j[p]] = BOT]
                BY Zenon
              <7>3. A[m] = A'[m]
                BY <7>2 DEF TypeOK
              <7> QED
                BY <7>1, <7>3
            <6> QED
              BY <6>1, <6>2
          <5>6. alpha_prev \in Perm(IdxSet_prev)
            <6>1. alpha_prev \in Seq(IdxSet_prev)
              BY <4>2 DEF Perm, ConcatProperties
            <6>2. Len(alpha_prev) = Cardinality(IdxSet_prev)
              <7>1. (L' \in Nat) => IsFiniteSet(0..L'-1)
                BY FS_Interval
              <7>2. L' \in Nat
                BY <2>1 DEF TypeOK
              <7>3. IsFiniteSet(0..L'-1)
                BY <7>1, <7>2
              <7>4. IsFiniteSet(IdxSet)
                BY <4>1, <7>3, FS_Subset, Zenon
              <7>5. Cardinality(IdxSet_prev) = Cardinality(IdxSet) + Cardinality({j[p]}) - Cardinality(IdxSet \cap {j[p]})
                BY <5>1, <5>3, <7>4, Zenon, FS_Union, FS_Interval, FS_Singleton
              <7>6. Cardinality({j[p]}) = 1
                BY FS_Singleton, Zenon
              <7>7. Cardinality(IdxSet \cap {j[p]}) = 0
                BY FS_EmptySet, <5>1, Zenon
              <7>8. Cardinality(IdxSet_prev) = Cardinality(IdxSet) + 1
                BY <7>5, <7>6, <7>7
              <7>9. Len(alpha) = Cardinality(IdxSet)
                BY <4>2 DEF Perm
              <7>10. Len(alpha_prev) = Len(alpha) + 1
                BY ConcatProperties
              <7> QED
                BY <7>8, <7>9, <7>10
            <6>3. \A x, y \in 1..Len(alpha_prev) : x # y => alpha_prev[x] # alpha_prev[y]
              BY <4>2, <5>1 DEF Perm
            <6> QED
              BY <6>1, <6>2, <6>3, Zenon DEF Perm
          <5>7. Justified(alpha_prev)
            <6> SUFFICES ASSUME NEW m \in 1..Len(alpha_prev), NEW n \in 1..Len(alpha_prev),
                                m < n
                         PROVE  \/ alpha_prev[m] < alpha_prev[n]
                                \/ A[alpha_prev[n]] # BOT => \E q \in ProcSet : (pc[q] = "L5" /\ alpha_prev[n] < j[q] /\ alpha_prev[m] < l[q])
              BY DEF Justified
            <6>1. CASE m # 1 /\ n # 1
              <7> USE <6>1
              <7>1. \A q \in ProcSet : pc'[q] = "L5" => pc[q] = "L5" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. \A q \in ProcSet : q # p => j'[q] = j[q] /\ l'[q] = l[q]
                BY Zenon DEF TypeOK
              <7>3. Justified(alpha)'
                BY <4>2  
              <7>4. m-1 \in 1..Len(alpha) /\ n-1 \in 1..Len(alpha)
                OBVIOUS  
              <7>5. m-1 < n-1
                OBVIOUS
              <7>6. (\/ alpha[m-1] < alpha[n-1]
                     \/ (A'[alpha[n-1]] # BOT => 
                              (\E q \in ProcSet : /\ pc[q] = "L5"
                                                  /\ alpha[n-1] < j[q]
                                                  /\ alpha[m-1] < l[q])))
                BY <7>3, <7>4, <7>5, Zenon DEF Justified, TypeOK
              <7>7. CASE alpha[m-1] < alpha[n-1]
                BY <7>7
              <7>8. CASE (A'[alpha[n-1]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5" /\ alpha[n-1] < j[q] /\ alpha[m-1] < l[q])
                <8> SUFFICES ASSUME A[alpha_prev[n]] # BOT
                             PROVE  \E q \in ProcSet : (pc[q] = "L5" /\ alpha_prev[n] < j[q] /\ alpha_prev[m] < l[q])
                  OBVIOUS
                <8>1. A[alpha[n-1]] # BOT
                  OBVIOUS
                <8>2. A' = [A EXCEPT ![j[p]] = BOT]
                  BY Zenon
                <8>3. alpha[n-1] # j[p] => A'[alpha[n-1]] # BOT
                  BY <8>1, <8>2
                <8>4. j[p] = alpha_prev[1]
                  OBVIOUS
                <8>5. alpha[n-1] = alpha_prev[n]
                  OBVIOUS
                <8> HIDE DEF alpha_prev
                <8>6. (1 \in 1..Len(alpha_prev) /\ n \in 1..Len(alpha_prev)) => (1 # n => alpha_prev[1] # alpha_prev[n])
                  BY <5>6, Zenon DEF Perm
                <8>7. 1 \in 1..Len(alpha_prev) /\ n \in 1..Len(alpha_prev) /\ 1 # n
                  BY DEF alpha_prev
                <8>8. alpha_prev[1] # alpha_prev[n]
                  BY <8>6, <8>7
                <8>9. alpha[n-1] # j[p]
                  BY <8>4, <8>5, <8>8
                <8>10. A'[alpha[n-1]] # BOT
                  BY <8>3, <8>9
                <8>11. PICK q \in ProcSet : /\ pc[q] = "L5" /\ alpha[n-1] < j[q] /\ alpha[m-1] < l[q]
                  BY <7>8, <8>10
                <8> QED
                  BY <8>11 DEF alpha_prev
              <7>9. QED
                BY <7>6, <7>7, <7>8
            <6>2. CASE m = 1
              <7> USE <6>2
              <7>1. m # n => alpha_prev[m] # alpha_prev[n]
                BY <5>6, Zenon DEF Perm
              <7> SUFFICES ASSUME alpha_prev[m] > alpha_prev[n], A[alpha_prev[n]] # BOT
                           PROVE  \E q \in ProcSet : (pc[q] = "L5" /\ alpha_prev[n] < j[q] /\ alpha_prev[m] < l[q])
                BY <5>6, <7>1 DEF Perm, TypeOK
              <7>2. alpha_prev[m] < l[p]
                BY DEF Inv3
              <7>3. alpha_prev[n] < j[p]
                OBVIOUS
              <7> QED
                BY <7>2, <7>3
            <6>3. CASE n = 1
              BY <4>2, <6>3 DEF Justified
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>8. c_prev.state = [i \in 1..Len(alpha_prev) |-> Val(alpha_prev[i])]
            <6>1. c_prev.state = [i \in 1..(Len(c.state)+1) |-> IF i = 1 THEN A[j[p]] ELSE c.state[i-1]]
              OBVIOUS
            <6>2. Len(c.state) = Len(alpha)
              BY <4>2
            <6>3. Len(alpha_prev) = Len(alpha) + 1
              BY ConcatProperties
            <6>4. Val(alpha_prev[1]) = A[j[p]]
              BY DEF Val
            <6>5. \A i \in 1..Len(alpha) : c.state[i] = Val(alpha[i])
              <7> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                           PROVE  c.state[i] = Val(alpha[i])
                OBVIOUS
              <7>1. alpha[i] \in IdxSet
                BY <4>2 DEF Perm
              <7>2. Val(alpha[i])' # BOT
                BY <4>1, <7>1
              <7>3. A' = [A EXCEPT ![j[p]] = BOT]
                BY Zenon
              <7>4. A[alpha[i]] = A'[alpha[i]]
                BY <5>1, <7>1, <7>3 DEF TypeOK
              <7>5. \A q \in ProcSet : (pc[q] = "L2" /\ l[q] = alpha[i]) <=> (pc'[q] = "L2" /\ l'[q] = alpha[i])
                BY Zenon DEF TypeOK
              <7>6. CASE A'[alpha[i]] # BOT
                BY <4>2, <7>6, <7>4, <7>1 DEF Val
              <7>7. CASE A'[alpha[i]] = BOT /\ \E q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[i]
                <8> USE <7>7
                <8>1. PICK q \in ProcSet : pc'[q] = "L2" /\ l'[q] = alpha[i]
                  OBVIOUS
                <8>2. \A r \in ProcSet : (pc'[r] = "L2" /\ l'[r] = l'[q]) => q = r
                  BY <2>4, <8>1 DEF Inv2
                <8>3. Val(alpha[i])' = arg[q]
                  BY <8>1, <8>2, Zenon DEF Val
                <8>4. pc[q] = "L2" /\ l[q] = alpha[i]
                  BY <7>5, <8>1
                <8>5. \A r \in ProcSet : (pc[r] = "L2" /\ l[r] = l[q]) => q = r
                  BY <8>4 DEF Inv2
                <8>6. Val(alpha[i]) = arg[q]
                  BY <7>4, <8>4, <8>5 DEF Val
                <8> QED
                  BY <8>6, <8>3, <7>2, <7>1, <4>2
              <7> QED
                BY <7>2, <7>6, <7>7 DEF Val
            <6>6. \A i \in 2..Len(alpha_prev) : c_prev.state[i] = c.state[i-1]
              BY <6>1, <6>2, <6>3
            <6>7. \A i \in 2..Len(alpha_prev) : alpha_prev[i] = alpha[i-1]
              OBVIOUS
            <6>A. \A i \in 2..Len(alpha_prev) : i-1 \in 1..Len(alpha)
              BY <6>3
            <6>B. \A i \in 2..Len(alpha_prev) : c_prev.state[i] = Val(alpha[i-1])
              BY <6>A, <6>5, <6>6, Zenon
            <6>8. \A i \in 2..Len(alpha_prev) : c_prev.state[i] = Val(alpha_prev[i])
              BY <6>B, <6>7, Zenon
            <6>9. \A i \in 1..Len(alpha_prev) : i = 1 => c_prev.state[i] = Val(alpha_prev[i])
              BY <6>1, <6>4
            <6>10. \A i \in 1..Len(alpha_prev) : i # 1 => i \in 2..Len(alpha_prev)
              OBVIOUS
            <6>11. \A i \in 1..Len(alpha_prev) : i # 1 => c_prev.state[i] = Val(alpha_prev[i])
              BY <6>8, <6>10, Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, <6>9, <6>11, Zenon
          <5>9. WellFormed(c_prev, IdxSet_prev)
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc[q] = "L0" 
                                       -> (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L1"
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \notin IdxSet_prev
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L2" /\ l[q] \in IdxSet_prev
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                  [] pc[q] = "L3"
                                       -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                  [] pc[q] = "L4"
                                       -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L5"
                                       -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                  [] pc[q] = "L6"
                                       -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q])
              BY Zenon DEF WellFormed
            <6>1. CASE pc[q] = "L0"
              <7> USE <6>1
              <7>1. pc'[q] = "L0" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>2. CASE pc[q] = "L1"
              <7> USE <6>2
              <7>1. pc'[q] = "L1" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet_prev
              <7> USE <6>3
              <7>1. pc'[q] = "L2" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3, Zenon
            <6>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet_prev
              <7> USE <6>4
              <7>1. pc'[q] = "L2" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
                BY <4>2, <7>1, Zenon DEF WellFormed, TypeOK, InvE
              <7>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <7>1, <7>2
              <7> QED
                BY <7>3, Zenon
            <6>5. CASE pc[q] = "L3"
              <7> USE <6>5
              <7>1. pc'[q] = "L3" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>6. CASE pc[q] = "L4"
              <7> USE <6>6
              <7>1. pc'[q] = "L4" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <4>2, <7>1, Zenon DEF WellFormed
              <7>3. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6>7. CASE pc[q] = "L5"
              <7> USE <6>7
              <7>1. (pc'[q] = "L5" /\ q # p) \/ q = p
                BY Zenon DEF TypeOK
              <7>2. CASE pc'[q] = "L5" /\ q # p
                <8> USE <7>2
                <8>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <4>2, Zenon DEF WellFormed
                <8>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                  BY <8>1
                <8> QED
                  BY <8>2
              <7>3. CASE q = p
                <8> USE <7>3
                <8>1. pc'[q] = "L6"
                  BY Zenon DEF TypeOK
                <8>2. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v'[q]
                  BY <4>2, <8>1 DEF WellFormed
                <8>3. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
                  BY <8>1, <8>2, <3>2 DEF ConfigDomain, ResDomain
                <8> QED
                  BY <8>3
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6>8. CASE pc[q] = "L6"
              <7> USE <6>8
              <7>1. pc'[q] = "L6" /\ q # p
                BY Zenon DEF TypeOK
              <7>2. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
                BY <4>2, <7>1, Zenon DEF WellFormed, TypeOK
              <7>3. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q]
                BY <7>1, <7>2
              <7> QED
                BY <7>3
            <6> QED
              BY RemDef, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, ZenonT(15) DEF TypeOK
          <5>10. c_prev \in S
            BY Zenon, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9 DEF S
          <5>11. c_prev \in P
            BY <5>10
          <5> DEFINE aseq == <<p>>
          <5> DEFINE beta == <<c_prev, c>>
          <5> DEFINE n    == 1
          <5>12. aseq \in Seq(ProcSet)
            OBVIOUS
          <5>13. beta \in Seq(ConfigDomain)
            BY <3>2, <5>2
          <5>14. Len(aseq) = n
            OBVIOUS
          <5>15. Len(beta) = n+1
            OBVIOUS
          <5>16. beta[1] = c_prev
            OBVIOUS
          <5>17. \A i \in 1..n : Delta(beta[i], aseq[i], beta[i+1])
            <6>1. SUFFICES ASSUME TRUE
                           PROVE  Delta(c_prev, p, c)
              <7> HIDE DEF c_prev
              <7> QED
                OBVIOUS
            <6> USE <6>1
            <6>2. c_prev.state # << >>
              OBVIOUS
            <6>3. c_prev.op[p] = "DEQ" /\ c_prev.arg[p] = BOT /\ c_prev.res[p] = BOT
              BY <5>9, Zenon DEF WellFormed
            <6>4. Tail(<<A[j[p]]>> \o c.state) = [i \in 1..(Len(c.state)) |-> c.state[i]]
              BY DEF Tail
            <6>5. c.state = Tail(c_prev.state)
              BY <6>4, <3>2 DEF ConfigDomain, StateDomain
            <6>6. c.op = c_prev.op /\ c.arg = c_prev.arg
              OBVIOUS
            <6>7. Head(c_prev.state) = A[j[p]]
              OBVIOUS
            <6>8. c.res[p] = v'[p]
              BY <4>2, Zenon DEF WellFormed, TypeOK
            <6>9. c.res = [c_prev.res EXCEPT ![p] = Head(c_prev.state)]
              BY <3>2, <6>7, <6>8, Zenon DEF ConfigDomain, ResDomain, TypeOK
            <6> QED
              BY <6>2, <6>3, <6>5, <6>6, <6>9 DEF Delta, ArgsOf
          <5>18. beta[n+1] = c
            OBVIOUS
          <5>19. c \in Evolve(P)
            <6> SUFFICES ASSUME TRUE
                         PROVE  /\ c \in ConfigDomain
                                /\ \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                      /\ Len(alpha_) = n_
                                      /\ Len(beta_) = n_ + 1
                                      /\ beta_[1] = poss_old
                                      /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                      /\ beta_[n_+1] = c
              BY Zenon DEF Evolve
            <6> HIDE DEF c_prev, aseq, beta
            <6> QED
              BY Zenon, <3>2, <5>11, <5>12, <5>13, <5>14, <5>15, <5>16, <5>17, <5>18
          <5> QED
            BY <5>19
        <4> QED
          BY <4>3, <4>4, <4>5
      <3>9. ASSUME NEW p \in ProcSet,
                   L6(p), 
                   P' = Filter(Evolve(P), p, (ret')[p])
            PROVE  c \in P'
        <4> USE <3>9 DEF L6
        <4>1. ret'[p] = v[p]
          BY DEF TypeOK
        <4> USE <4>1
        <4>2. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY Zenon DEF S
        <4>3. IdxSet \in SUBSET 0..(L-1)
          BY <4>2
        <4>4. /\ \A m \in IdxSet : Val(m) # BOT
              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          BY <4>2, Z3T(10) DEF Val
        <4>5. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>2
        <4>6. Justified(alpha)
          <5> SUFFICES ASSUME NEW m \in 1..Len(alpha), NEW n \in 1..Len(alpha),
                              m < n
                       PROVE  \/ alpha[m] < alpha[n]
                              \/ A[alpha[n]] # BOT => \E q \in ProcSet : /\ pc[q] = "L5"
                                                                         /\ alpha[n] < j[q]
                                                                         /\ alpha[m] < l[q]
            BY DEF Justified
          <5>1. alpha[m] \in IdxSet /\ alpha[n] \in IdxSet
            BY <4>3, <4>5 DEF Perm
          <5>2. alpha[m] \in 0..(L-1) /\ alpha[n] \in 0..(L-1)
            BY <4>3, <5>1, Zenon
          <5> SUFFICES ASSUME (alpha[m] > alpha[n]), A[alpha[n]] # BOT
                       PROVE  \E q \in ProcSet : pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <4>3, <5>2 DEF Perm
          <5>3. PICK q \in ProcSet : pc'[q] = "L5" /\ alpha[n] < j'[q] /\ alpha[m] < l'[q]
            BY <4>5, <5>2 DEF Justified
          <5>4. q # p
            BY <5>2, <5>3 DEF TypeOK
          <5>5. pc[q] = "L5" /\ alpha[n] < j[q] /\ alpha[m] < l[q]
            BY <5>3, <5>4 DEF TypeOK
          <5> QED
            BY <5>5 
        <4> DEFINE c_prev == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "DEQ"],
                              arg   |-> [c.arg EXCEPT ![p] = BOT],
                              res   |-> [c.res EXCEPT ![p] = v[p]]]
        <4>7. c_prev \in ConfigDomain
          BY <3>2 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
        <4>8. c_prev.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          BY <4>5 DEF Val, TypeOK
        <4>9. WellFormed(c_prev, IdxSet)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  CASE pc[q] = "L0" 
                                     -> (c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L1"
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \notin IdxSet
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L2" /\ l[q] \in IdxSet
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                [] pc[q] = "L3"
                                     -> (c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK)
                                [] pc[q] = "L4"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L5"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT)
                                [] pc[q] = "L6"
                                     -> (c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q])
            BY Zenon DEF WellFormed
          <5>1. CASE pc[q] = "L0"
            <6> USE <5>1
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = BOT /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>2. CASE pc[q] = "L1"
            <6> USE <5>2
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>3. CASE pc[q] = "L2" /\ l[q] \notin IdxSet
            <6> USE <5>3
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2, Zenon
          <5>4. CASE pc[q] = "L2" /\ l[q] \in IdxSet
            <6> USE <5>4
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
              BY <6>0, <6>1
            <6> QED
              BY <6>2, Zenon
          <5>5. CASE pc[q] = "L3"
            <6> USE <5>5
            <6>1. CASE p = q
              <7>1. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <6>1, <4>7 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
              <7> QED
                BY <7>1
            <6>2. CASE p # q
              <7>1. c.op[q] = "ENQ" /\ c.arg[q] = arg'[q] /\ c.res[q] = ACK
                BY <4>5, <6>2, Zenon DEF WellFormed, TypeOK
              <7>2. c_prev.op[q] = "ENQ" /\ c_prev.arg[q] = arg[q] /\ c_prev.res[q] = ACK
                BY <6>2, <7>1
              <7> QED
                BY <7>2
            <6> QED
              BY <6>1, <6>2
          <5>6. CASE pc[q] = "L4"
            <6> USE <5>6
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>7. CASE pc[q] = "L5"
            <6> USE <5>7
            <6>0. q # p 
              OBVIOUS
            <6>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <4>5, Zenon DEF WellFormed, TypeOK
            <6>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = BOT
              BY <6>0, <6>1
            <6> QED
              BY <6>2
          <5>8. CASE pc[q] = "L6"
            <6> USE <5>8
            <6>1. CASE p = q
              <7>1. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q]
                BY <6>1, <4>7 DEF TypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain
              <7> QED
                BY <7>1
            <6>2. CASE p # q
              <7>1. c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
                BY <4>5, <6>2, Zenon DEF WellFormed, TypeOK
              <7>2. c_prev.op[q] = "DEQ" /\ c_prev.arg[q] = BOT /\ c_prev.res[q] = v[q]
                BY <6>2, <7>1
              <7> QED
                BY <7>2
            <6> QED
              BY <6>1, <6>2
          <5> QED
            BY RemDef, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, ZenonT(15) DEF TypeOK
        <4>10. c_prev \in S
          BY Zenon, <4>7, <4>2, <4>3, <4>4, <4>5, <4>6, <4>6, <4>8, <4>9 DEF S
        <4>11. c_prev \in P
          BY <4>10
        <4> DEFINE pseq == << >>
        <4> DEFINE beta  == <<c_prev>>
        <4> DEFINE n     == 0
        <4>12. n \in Nat
          OBVIOUS
        <4>13. pseq \in Seq(ProcSet)
          OBVIOUS
        <4>14. beta \in Seq(ConfigDomain)
          BY <4>7
        <4>15. Len(pseq) = n
          OBVIOUS
        <4>16. Len(beta) = n+1
          OBVIOUS
        <4>17. beta[1] = c_prev
          OBVIOUS
        <4>18. \A i \in 1..n : Delta(beta[i], pseq[i], beta[i+1])
          OBVIOUS
        <4>19. beta[n+1] = c_prev
          OBVIOUS
        <4>20. c_prev \in Evolve(P)
          <5> SUFFICES ASSUME TRUE
                       PROVE  \E poss_old \in P : \E n_ \in Nat : \E alpha_ \in Seq(ProcSet) : \E beta_ \in Seq(ConfigDomain) :
                                    /\ Len(alpha_) = n_
                                    /\ Len(beta_) = n_ + 1
                                    /\ beta_[1] = poss_old
                                    /\ \A i \in 1..n_ : Delta(beta_[i], alpha_[i], beta_[i+1])
                                    /\ beta_[n_+1] = c_prev
            BY Zenon, <4>7 DEF Evolve
          <5> QED
            BY Zenon, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16, <4>17, <4>18, <4>19
        
        <4>21. c_prev.res[p] = v[p]
          BY <3>2 DEF ConfigDomain
        <4>22. c.op = [c_prev.op EXCEPT ![p] = BOT]
          <5>1. \A q \in ProcSet : p # q => c.op[q] = c_prev.op[q]
            OBVIOUS
          <5>2. c.op[p] = BOT
            BY <4>5, Zenon DEF TypeOK, WellFormed
          <5> QED
            BY <3>2, <5>1, <5>2, Zenon DEF ConfigDomain
        <4>23. c.arg = [c_prev.arg EXCEPT ![p] = BOT]
          <5>1. \A q \in ProcSet : p # q => c.arg[q] = c_prev.arg[q]
            OBVIOUS
          <5>2. c.arg[p] = BOT
            BY <4>5, Zenon DEF TypeOK, WellFormed
          <5> QED
            BY <3>2, <5>1, <5>2, Zenon DEF ConfigDomain
        <4>24. c.res = [c_prev.res EXCEPT ![p] = BOT]
          <5>1. \A q \in ProcSet : p # q => c.res[q] = c_prev.res[q]
            OBVIOUS
          <5>2. c.res[p] = BOT
            BY <4>5, Zenon DEF TypeOK, WellFormed
          <5> QED
            BY <3>2, <5>1, <5>2, Zenon DEF ConfigDomain
        <4>25. c.state = c_prev.state
          OBVIOUS
        <4>26. c \in Filter(Evolve(P), p, v[p])
          BY Zenon, <3>2, <4>20, <4>21, <4>22, <4>23, <4>24, <4>25 DEF Filter
        <4> QED
          BY <4>26
      <3>10. CASE UNCHANGED vars
        <4> USE <3>10 DEF vars, algvars
        <4>1. PICK IdxSet \in SUBSET 0..(L'-1) : /\ \A m \in IdxSet : Val(m)' # BOT
                                                 /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in IdxSet
                                                 /\ \E alpha \in Perm(IdxSet) : 
                                                    /\ Justified(alpha)'
                                                    /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                                    /\ WellFormed(c, IdxSet)'
          BY DEF S
        <4>2. IdxSet \in SUBSET 0..(L-1)
          BY <4>1
        <4>3. /\ \A m \in IdxSet : Val(m) # BOT
              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          BY <4>1, Z3T(10) DEF Val
        <4>4. PICK alpha \in Perm(IdxSet) : /\ Justified(alpha)'
                                            /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])']
                                            /\ WellFormed(c, IdxSet)'
          BY <4>1
        <4>5. Justified(alpha)
          BY <4>4 DEF Justified
        <4>6. c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
          <5> SUFFICES ASSUME NEW i \in 1..Len(alpha)
                       PROVE  Val(alpha[i])' = Val(alpha[i])
            BY <4>1, <4>4
          <5>1. CASE A[alpha[i]] # BOT
            BY <5>1, <4>4 DEF Val
          <5>2. CASE A[alpha[i]] = BOT /\ ~(\E p \in ProcSet : pc[p] = "L2" /\ l[p] = alpha[i])
            BY <5>2, <4>4 DEF Val
          <5>3. CASE A[alpha[i]] = BOT /\ (\E p \in ProcSet : pc[p] = "L2" /\ l[p] = alpha[i])
            BY <5>3, <4>4 DEF Val, Inv2
          <5> QED
            BY <4>4, <5>3 DEF Val
        <4>7. WellFormed(c, IdxSet)
          <5> SUFFICES ASSUME TRUE 
                       PROVE \A p \in ProcSet : CASE pc[p] = "L0" 
                                                       -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                                                  [] pc[p] = "L1"
                                                       -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
                                                  [] pc[p] = "L2" /\ l[p] \notin IdxSet
                                                       -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
                                                  [] pc[p] = "L2" /\ l[p] \in IdxSet
                                                       -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK)
                                                  [] pc[p] = "L3"
                                                       -> (c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK)
                                                  [] pc[p] = "L4"
                                                       -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                                                  [] pc[p] = "L5"
                                                       -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
                                                  [] pc[p] = "L6"
                                                       -> (c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = v[p])
            BY Zenon DEF WellFormed
          <5>1. \A p \in ProcSet : pc'[p] = pc[p] /\ arg'[p] = arg[p] /\ l'[p] = l[p] /\ v'[p] = v[p]
            OBVIOUS
          <5>2. ASSUME NEW p \in ProcSet, pc[p] = "L0"
                       PROVE c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
            BY <4>4, <5>2, <5>1, Zenon DEF WellFormed
          <5>3. ASSUME NEW p \in ProcSet, pc[p] = "L1"
                       PROVE c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
            BY <4>4, <5>3, <5>1, Zenon DEF WellFormed
          <5>4. ASSUME NEW p \in ProcSet, pc[p] = "L2", l[p] \notin IdxSet
                       PROVE c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
            BY <4>4, <5>4, <5>1, Zenon DEF WellFormed
          <5>5. ASSUME NEW p \in ProcSet, pc[p] = "L2", l[p] \in IdxSet
                       PROVE c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK
            BY <4>4, <5>5, <5>1, Zenon DEF WellFormed
          <5>6. ASSUME NEW p \in ProcSet, pc[p] = "L3"
                       PROVE c.op[p] = "ENQ" /\ c.arg[p] = arg[p] /\ c.res[p] = ACK
            BY <4>4, <5>6, <5>1, Zenon DEF WellFormed
          <5>7. ASSUME NEW p \in ProcSet, pc[p] = "L4"
                       PROVE c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT
            BY <4>4, <5>7, <5>1, Zenon DEF WellFormed
          <5>8. ASSUME NEW p \in ProcSet, pc[p] = "L5"
                       PROVE c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = BOT
            BY <4>4, <5>8, <5>1, Zenon DEF WellFormed
          <5>9. ASSUME NEW p \in ProcSet, pc[p] = "L6"
                       PROVE c.op[p] = "DEQ" /\ c.arg[p] = BOT /\ c.res[p] = v[p]
            BY <4>4, <5>9, <5>1, Zenon DEF WellFormed
          <5> QED
            BY RemDef, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, Zenon DEF TypeOK
        <4>8. c \in S
          BY Zenon, <3>2, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF S
        <4>9. c \in P
          BY <4>8
        <4> QED
          BY <4>9
      <3>11. QED
        BY <3>1, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10 DEF Next, IntLine, IntLines, RetLine, RetLines
    <2>9. Lin2'
      <3> SUFFICES S' # {}
        BY DEF Lin2
      <3>1. ASSUME NEW p \in ProcSet, L0(p)
            PROVE  S' # {}
        <4> USE <3>1 DEF L0
        <4>1. CASE pc'[p] = "L1"
          <5> USE <4>1 DEF algvars, TypeOK
          <5>1. PICK p_op \in OpNames : /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(p_op)]
                                        /\ \E arg_val \in ArgsOf(p_op) : 
                                           /\ IF arg_val # BOT 
                                                 THEN arg' = [arg EXCEPT ![p] = arg_val]
                                                 ELSE arg' = arg  
                                           /\ P' = Evolve(Invoke(P, p, p_op, arg_val))
            BY Zenon
          <5>2. p_op = "ENQ"
            BY <5>1 DEF OpToInvocLine, ArgsOf
          <5>3. PICK p_arg \in ArgsOf("ENQ") : /\ IF p_arg # BOT 
                                                     THEN arg' = [arg EXCEPT ![p] = p_arg]
                                                     ELSE arg' = arg  
                                               /\ P' = Evolve(Invoke(P, p, p_op, p_arg))
            BY <5>1, <5>2 DEF ArgsOf
          <5>4. p_arg \in EltDomain
            BY <5>3 DEF ArgsOf
          <5> DEFINE IdxSet == {i \in 0..(L-1) : A[i] # BOT}
          <5>5. \A m \in IdxSet : Val(m) # BOT
            BY DEF Val
          <5>6. \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
            OBVIOUS
          <5>7. IdxSet \in SUBSET Int
            OBVIOUS
          <5>8. IsFiniteSet(0..(L-1))
            BY FS_Interval
          <5>9. IsFiniteSet(IdxSet)
            BY <5>8, FS_Subset
          <5>10. PICK alpha \in Perm(IdxSet) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
            BY <5>7, <5>9, FS_SortedPermutation, Zenon
          <5>11. Justified(alpha)'
            BY <5>10 DEF Justified
          <5> DEFINE val == [i \in 1..Len(alpha) |-> Val(alpha[i])]
          <5>12. \A i \in 1..Len(alpha) : val[i] \in EltDomain
            BY DEF Val, Perm
          <5>13. val \in StateDomain
            BY <5>12 DEF Perm, StateDomain
          <5> DEFINE op == [q \in ProcSet |-> CASE pc[q] = "L0" /\ q # p -> BOT
                                                [] pc[q] = "L0" /\ q = p -> "ENQ"
                                                [] pc[q] = "L1"          -> "ENQ"
                                                [] pc[q] = "L2"          -> "ENQ"
                                                [] pc[q] = "L3"          -> "ENQ"
                                                [] pc[q] = "L4"          -> "DEQ"
                                                [] pc[q] = "L5"          -> "DEQ"
                                                [] pc[q] = "L6"          -> "DEQ"]
          <5>14. op \in [ProcSet -> OpDomain]
            BY DEF OpDomain
          <5> DEFINE carg == [q \in ProcSet |-> CASE pc[q] = "L0" /\ q # p -> BOT
                                                  [] pc[q] = "L0" /\ q = p -> p_arg
                                                  [] pc[q] = "L1"          -> arg[q]
                                                  [] pc[q] = "L2"          -> arg[q]
                                                  [] pc[q] = "L3"          -> arg[q]
                                                  [] pc[q] = "L4"          -> BOT
                                                  [] pc[q] = "L5"          -> BOT
                                                  [] pc[q] = "L6"          -> BOT]
          <5>15. carg \in [ProcSet -> ArgDomain]
            BY <5>4 DEF ArgDomain
          <5> DEFINE res == [q \in ProcSet |-> CASE pc[q] = "L0" /\ q # p -> BOT
                                                 [] pc[q] = "L0" /\ q = p -> BOT
                                                 [] pc[q] = "L1"          -> BOT
                                                 [] pc[q] = "L2" /\ l[q] \notin IdxSet -> BOT
                                                 [] pc[q] = "L2" /\ l[q] \in IdxSet    -> ACK
                                                 [] pc[q] = "L3"          -> ACK
                                                 [] pc[q] = "L4"          -> BOT
                                                 [] pc[q] = "L5"          -> BOT
                                                 [] pc[q] = "L6"          -> v[q]]
          <5>16. res \in [ProcSet -> ResDomain]
            BY DEF ResDomain
          <5> DEFINE c == [state |-> val, op |-> op, arg |-> carg, res |-> res]
          <5> DEFINE WF0(q) == c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          <5> DEFINE WF1(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          <5> DEFINE WF2A(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          <5> DEFINE WF2B(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
          <5> DEFINE WF3(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
          <5> DEFINE WF4(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
          <5> DEFINE WF5(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
          <5> DEFINE WF6(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
          <5>17. c \in ConfigDomain
            BY <5>13, <5>14, <5>15, <5>16 DEF ConfigDomain
          <5>18. WellFormed(c, IdxSet)' = \A q \in ProcSet : 
                   (CASE pc'[q] = "L0" -> WF0(q)'
                      [] pc'[q] = "L1" -> WF1(q)'
                      [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                      [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                      [] pc'[q] = "L3" -> WF3(q)'
                      [] pc'[q] = "L4" -> WF4(q)'
                      [] pc'[q] = "L5" -> WF5(q)'
                      [] pc'[q] = "L6" -> WF6(q)')
            BY Z3T(30) DEF WellFormed
          <5>19. WellFormed(c, IdxSet)'
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc'[q] = "L0" -> WF0(q)'
                                  [] pc'[q] = "L1" -> WF1(q)'
                                  [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                                  [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                                  [] pc'[q] = "L3" -> WF3(q)'
                                  [] pc'[q] = "L4" -> WF4(q)'
                                  [] pc'[q] = "L5" -> WF5(q)'
                                  [] pc'[q] = "L6" -> WF6(q)'
              BY <5>18, Zenon DEF WellFormed
            <6>1. CASE pc'[q] = "L0"
              BY <6>1, Zenon
            <6>2. CASE pc'[q] = "L1"
              BY <6>2, Zenon
            <6>3. CASE pc'[q] = "L2" /\ l'[q] \notin IdxSet
              BY <6>3, Zenon
            <6>4. CASE pc'[q] = "L2" /\ l'[q] \in IdxSet
              BY <6>4, Zenon
            <6>5. CASE pc'[q] = "L3"
              BY <6>5, Zenon
            <6>6. CASE pc'[q] = "L4"
              BY <6>6, Zenon
            <6>7. CASE pc'[q] = "L5"
              BY <6>7, Zenon
            <6>8. CASE pc'[q] = "L6"
              BY <6>8, Zenon
            <6> QED
              BY RemDef, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, ZenonT(15) DEF TypeOK
          <5> SUFFICES c \in S'
            OBVIOUS
          <5> DEFINE Q(d, iset) == \E alph \in Perm(iset) : 
                                        /\ Justified(alph)'
                                        /\ d.state = [i \in 1..Len(alph) |-> Val(alph[i])]
                                        /\ WellFormed(d, iset)'
          <5>20. S' = {d \in ConfigDomain : 
                          \E iset \in SUBSET 0..(L-1) :
                              /\ \A m \in iset : Val(m) # BOT                  
                              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in iset  
                              /\ Q(d, iset)}
            BY DEF S, Val
          <5>21. Q(c, IdxSet)
            <6> SUFFICES /\ Justified(alpha)'
                         /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
                         /\ WellFormed(c, IdxSet)'
              BY <5>10, Zenon
            <6> QED
              BY <5>11, <5>12, <5>19, Zenon
          <5> HIDE DEF c, Q
          <5> QED
            BY <5>20, <5>5, <5>6, <5>17, <5>21
        <4>2. CASE pc'[p] = "L4"
          <5> USE <4>2 DEF algvars, TypeOK
          <5>1. PICK p_op \in OpNames : /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(p_op)]
                                        /\ \E arg_val \in ArgsOf(p_op) : 
                                           /\ IF arg_val # BOT 
                                                 THEN arg' = [arg EXCEPT ![p] = arg_val]
                                                 ELSE arg' = arg  
                                           /\ P' = Evolve(Invoke(P, p, p_op, arg_val))
            BY Zenon
          <5>2. p_op = "DEQ"
            BY <5>1 DEF OpToInvocLine, ArgsOf
          <5>3. PICK p_arg \in ArgsOf("DEQ") : /\ IF p_arg # BOT 
                                                     THEN arg' = [arg EXCEPT ![p] = p_arg]
                                                     ELSE arg' = arg  
                                               /\ P' = Evolve(Invoke(P, p, p_op, p_arg))
            BY <5>1, <5>2 DEF ArgsOf
          <5>4. p_arg = BOT
            BY <5>3 DEF ArgsOf
          <5> DEFINE IdxSet == {i \in 0..(L-1) : A[i] # BOT}
          <5>5. \A m \in IdxSet : Val(m) # BOT
            BY DEF Val
          <5>6. \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
            OBVIOUS
          <5>7. IdxSet \in SUBSET Int
            OBVIOUS
          <5>8. IsFiniteSet(0..(L-1))
            BY FS_Interval
          <5>9. IsFiniteSet(IdxSet)
            BY <5>8, FS_Subset
          <5>10. PICK alpha \in Perm(IdxSet) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
            BY <5>7, <5>9, FS_SortedPermutation, Zenon
          <5>11. Justified(alpha)'
            BY <5>10 DEF Justified
          <5> DEFINE val == [i \in 1..Len(alpha) |-> Val(alpha[i])]
          <5>12. \A i \in 1..Len(alpha) : val[i] \in EltDomain
            BY DEF Val, Perm
          <5>13. val \in StateDomain
            BY <5>12 DEF Perm, StateDomain
          <5> DEFINE op == [q \in ProcSet |-> CASE pc[q] = "L0" /\ q # p -> BOT
                                                [] pc[q] = "L0" /\ q = p -> "ENQ"
                                                [] pc[q] = "L1"          -> "ENQ"
                                                [] pc[q] = "L2"          -> "ENQ"
                                                [] pc[q] = "L3"          -> "ENQ"
                                                [] pc[q] = "L4"          -> "DEQ"
                                                [] pc[q] = "L5"          -> "DEQ"
                                                [] pc[q] = "L6"          -> "DEQ"]
          <5>14. op \in [ProcSet -> OpDomain]
            BY DEF OpDomain
          <5> DEFINE carg == [q \in ProcSet |-> CASE pc[q] = "L0" /\ q # p -> BOT
                                                  [] pc[q] = "L0" /\ q = p -> p_arg
                                                  [] pc[q] = "L1"          -> arg[q]
                                                  [] pc[q] = "L2"          -> arg[q]
                                                  [] pc[q] = "L3"          -> arg[q]
                                                  [] pc[q] = "L4"          -> BOT
                                                  [] pc[q] = "L5"          -> BOT
                                                  [] pc[q] = "L6"          -> BOT]
          <5>15. carg \in [ProcSet -> ArgDomain]
            BY <5>4 DEF ArgDomain
          <5> DEFINE res == [q \in ProcSet |-> CASE pc[q] = "L0" /\ q # p -> BOT
                                                 [] pc[q] = "L0" /\ q = p -> BOT
                                                 [] pc[q] = "L1"          -> BOT
                                                 [] pc[q] = "L2" /\ l[q] \notin IdxSet -> BOT
                                                 [] pc[q] = "L2" /\ l[q] \in IdxSet    -> ACK
                                                 [] pc[q] = "L3"          -> ACK
                                                 [] pc[q] = "L4"          -> BOT
                                                 [] pc[q] = "L5"          -> BOT
                                                 [] pc[q] = "L6"          -> v[q]]
          <5>16. res \in [ProcSet -> ResDomain]
            BY DEF ResDomain
          <5> DEFINE c == [state |-> val, op |-> op, arg |-> carg, res |-> res]
          <5> DEFINE WF0(q) == c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          <5> DEFINE WF1(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          <5> DEFINE WF2A(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          <5> DEFINE WF2B(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
          <5> DEFINE WF3(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
          <5> DEFINE WF4(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
          <5> DEFINE WF5(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
          <5> DEFINE WF6(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
          <5>17. c \in ConfigDomain
            BY <5>13, <5>14, <5>15, <5>16 DEF ConfigDomain
          <5>18. WellFormed(c, IdxSet)' = \A q \in ProcSet : 
                   (CASE pc'[q] = "L0" -> WF0(q)'
                      [] pc'[q] = "L1" -> WF1(q)'
                      [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                      [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                      [] pc'[q] = "L3" -> WF3(q)'
                      [] pc'[q] = "L4" -> WF4(q)'
                      [] pc'[q] = "L5" -> WF5(q)'
                      [] pc'[q] = "L6" -> WF6(q)')
            BY Z3T(30) DEF WellFormed
          <5>19. WellFormed(c, IdxSet)'
            <6> SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc'[q] = "L0" -> WF0(q)'
                                  [] pc'[q] = "L1" -> WF1(q)'
                                  [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                                  [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                                  [] pc'[q] = "L3" -> WF3(q)'
                                  [] pc'[q] = "L4" -> WF4(q)'
                                  [] pc'[q] = "L5" -> WF5(q)'
                                  [] pc'[q] = "L6" -> WF6(q)'
              BY <5>18, Zenon DEF WellFormed
            <6>1. CASE pc'[q] = "L0"
              BY <6>1, Zenon
            <6>2. CASE pc'[q] = "L1"
              BY <6>2, Zenon
            <6>3. CASE pc'[q] = "L2" /\ l'[q] \notin IdxSet
              BY <6>3, Zenon
            <6>4. CASE pc'[q] = "L2" /\ l'[q] \in IdxSet
              BY <6>4, Zenon
            <6>5. CASE pc'[q] = "L3"
              BY <6>5, Zenon
            <6>6. CASE pc'[q] = "L4"
              BY <6>6, Zenon
            <6>7. CASE pc'[q] = "L5"
              BY <6>7, Zenon
            <6>8. CASE pc'[q] = "L6"
              BY <6>8, Zenon
            <6> QED
              BY RemDef, <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, ZenonT(15) DEF TypeOK
          <5> SUFFICES c \in S'
            OBVIOUS
          <5> DEFINE Q(d, iset) == \E alph \in Perm(iset) : 
                                        /\ Justified(alph)'
                                        /\ d.state = [i \in 1..Len(alph) |-> Val(alph[i])]
                                        /\ WellFormed(d, iset)'
          <5>20. S' = {d \in ConfigDomain : 
                          \E iset \in SUBSET 0..(L-1) :
                              /\ \A m \in iset : Val(m) # BOT                  
                              /\ \A m \in 0..(L-1) : A[m] # BOT => m \in iset  
                              /\ Q(d, iset)}
            BY DEF S, Val
          <5>21. Q(c, IdxSet)
            <6> SUFFICES /\ Justified(alpha)'
                         /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
                         /\ WellFormed(c, IdxSet)'
              BY <5>10, Zenon
            <6> QED
              BY <5>11, <5>12, <5>19, Zenon
          <5> HIDE DEF c, Q
          <5> QED
            BY <5>20, <5>5, <5>6, <5>17, <5>21
        <4> QED
          BY <4>1, <4>2 DEF OpNames, OpToInvocLine, TypeOK
      <3>2. ASSUME NEW p \in ProcSet, L1(p)
            PROVE  S' # {}
\*        BY <3>2 DEF Inv2, L1, TypeOK, Inv1
      <3>3. ASSUME NEW p \in ProcSet, L2(p)
            PROVE  S' # {}
\*        BY <3>3 DEF L2
      <3>4. ASSUME NEW p \in ProcSet, L3(p)
            PROVE  S' # {}
\*        BY <3>4 DEF L3
      <3>5. ASSUME NEW p \in ProcSet, L4(p)
            PROVE  S' # {}
\*        BY <3>5 DEF L4
      <3>6. ASSUME NEW p \in ProcSet, L5(p)
            PROVE  S' # {}
        <4>1. CASE (j[p] = l[p])
\*          BY <3>6, <4>1, Zenon DEF L5, TypeOK
        <4>2. CASE (j[p] # l[p] /\ A[j[p]] = BOT)
\*          BY <3>6, <4>2, Zenon DEF L5, TypeOK
        <4>3. CASE (j[p] # l[p] /\ A[j[p]] # BOT)
\*          BY <3>6, <4>3, Zenon DEF L5, TypeOK
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>7. ASSUME NEW p \in ProcSet, L6(p)
            PROVE  S' # {}
\*        BY <3>7 DEF L6
      <3>8. CASE UNCHANGED vars
        <4> USE <3>8 DEF vars, algvars, TypeOK
        <4> DEFINE IdxSet == {i \in 0..(L-1) : A[i] # BOT}
        <4>5. \A m \in IdxSet : Val(m) # BOT
          BY DEF Val
        <4>6. \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
          OBVIOUS
        <4>7. IdxSet \in SUBSET Int
          OBVIOUS
        <4>8. IsFiniteSet(0..(L-1))
          BY FS_Interval
        <4>9. IsFiniteSet(IdxSet)
          BY <4>8, FS_Subset
        <4>10. PICK alpha \in Perm(IdxSet) : \A m, n \in 1..Len(alpha) : m < n => alpha[m] < alpha[n]
          BY <4>7, <4>9, FS_SortedPermutation, Zenon
        <4>11. Justified(alpha)'
          BY <4>10 DEF Justified
        <4> DEFINE val == [i \in 1..Len(alpha) |-> Val(alpha[i])]
        <4>12. \A i \in 1..Len(alpha) : val[i] \in EltDomain
          BY DEF Val, Perm
        <4>13. val \in StateDomain
          BY <4>12 DEF Perm, StateDomain
        <4> DEFINE op == [q \in ProcSet |-> CASE pc[q] = "L0" -> BOT
                                              [] pc[q] = "L1" -> "ENQ"
                                              [] pc[q] = "L2" -> "ENQ"
                                              [] pc[q] = "L3" -> "ENQ"
                                              [] pc[q] = "L4" -> "DEQ"
                                              [] pc[q] = "L5" -> "DEQ"
                                              [] pc[q] = "L6" -> "DEQ"]
        <4>14. op \in [ProcSet -> OpDomain]
          BY DEF OpDomain
        <4> DEFINE carg == [q \in ProcSet |-> CASE pc[q] = "L0" -> BOT
                                                [] pc[q] = "L1" -> arg[q]
                                                [] pc[q] = "L2" -> arg[q]
                                                [] pc[q] = "L3" -> arg[q]
                                                [] pc[q] = "L4" -> BOT
                                                [] pc[q] = "L5" -> BOT
                                                [] pc[q] = "L6" -> BOT]
        <4>15. carg \in [ProcSet -> ArgDomain]
          BY DEF ArgDomain
        <4> DEFINE res == [q \in ProcSet |-> CASE pc[q] = "L0" -> BOT
                                               [] pc[q] = "L1" -> BOT
                                               [] pc[q] = "L2" /\ l[q] \notin IdxSet -> BOT
                                               [] pc[q] = "L2" /\ l[q] \in IdxSet    -> ACK
                                               [] pc[q] = "L3" -> ACK
                                               [] pc[q] = "L4" -> BOT
                                               [] pc[q] = "L5" -> BOT
                                               [] pc[q] = "L6" -> v[q]]
        <4>16. res \in [ProcSet -> ResDomain]
          BY DEF ResDomain
        <4> DEFINE c == [state |-> val, op |-> op, arg |-> carg, res |-> res]
        <4> DEFINE WF0(q) == c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
        <4> DEFINE WF1(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
        <4> DEFINE WF2A(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
        <4> DEFINE WF2B(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
        <4> DEFINE WF3(q) == c.op[q] = "ENQ" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK
        <4> DEFINE WF4(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
        <4> DEFINE WF5(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = BOT
        <4> DEFINE WF6(q) == c.op[q] = "DEQ" /\ c.arg[q] = BOT /\ c.res[q] = v[q]
        <4>17. c \in ConfigDomain
          BY <4>13, <4>14, <4>15, <4>16 DEF ConfigDomain
        <4>18. WellFormed(c, IdxSet)' = \A q \in ProcSet : 
                 (CASE pc'[q] = "L0" -> WF0(q)'
                    [] pc'[q] = "L1" -> WF1(q)'
                    [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                    [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                    [] pc'[q] = "L3" -> WF3(q)'
                    [] pc'[q] = "L4" -> WF4(q)'
                    [] pc'[q] = "L5" -> WF5(q)'
                    [] pc'[q] = "L6" -> WF6(q)')
          BY Z3T(30) DEF WellFormed
        <4>19. WellFormed(c, IdxSet)'
          <5>0. SUFFICES ASSUME NEW q \in ProcSet
                         PROVE  CASE pc'[q] = "L0" -> WF0(q)'
                                  [] pc'[q] = "L1" -> WF1(q)'
                                  [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                                  [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                                  [] pc'[q] = "L3" -> WF3(q)'
                                  [] pc'[q] = "L4" -> WF4(q)'
                                  [] pc'[q] = "L5" -> WF5(q)'
                                  [] pc'[q] = "L6" -> WF6(q)'
            BY <4>18, Zenon DEF WellFormed
          <5> DEFINE cases == CASE pc'[q] = "L0" -> WF0(q)'
                                [] pc'[q] = "L1" -> WF1(q)'
                                [] pc'[q] = "L2" /\ l'[q] \notin IdxSet -> WF2A(q)'
                                [] pc'[q] = "L2" /\ l'[q] \in IdxSet    -> WF2B(q)'
                                [] pc'[q] = "L3" -> WF3(q)'
                                [] pc'[q] = "L4" -> WF4(q)'
                                [] pc'[q] = "L5" -> WF5(q)'
                                [] pc'[q] = "L6" -> WF6(q)'
          <5> SUFFICES ASSUME TRUE 
                       PROVE cases
            BY Zenon
          <5>1. CASE pc'[q] = "L0"
            BY <5>1, Zenon
          <5>2. CASE pc'[q] = "L1"
            BY <5>2, Zenon
          <5>3. CASE pc'[q] = "L2" /\ l'[q] \notin IdxSet
            <6>1. cases = WF2A(q)'
              BY <5>3
            <6> HIDE DEF cases
            <6>2. c.op[q] = "ENQ" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT
              BY <5>3
            <6>3. WF2A(q)'
              BY <6>2
            <6> QED  
              BY <6>1, <6>3, Zenon
          <5>4. CASE pc'[q] = "L2" /\ l'[q] \in IdxSet
            <6>1. cases = WF2B(q)'
              BY <5>4
            <6> HIDE DEF cases
            <6>2. c.op[q] = "ENQ" /\ c.arg[q] = arg'[q] /\ c.res[q] = ACK
              BY <5>4
            <6>3. WF2B(q)'
              BY <6>2
            <6> QED  
              BY <6>1, <6>3, Zenon
          <5>5. CASE pc'[q] = "L3"
            BY <5>5, Zenon
          <5>6. CASE pc'[q] = "L4"
            BY <5>6, Zenon
          <5>7. CASE pc'[q] = "L5"
            BY <5>7, Zenon
          <5>8. CASE pc'[q] = "L6"
            BY <5>8, Zenon
          <5> HIDE DEF cases
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, RemDef
        <4> SUFFICES c \in S'
          OBVIOUS
\*        S == {c \in ConfigDomain : 
\*        \E IdxSet \in SUBSET 0..(L-1) :
\*            /\ \A m \in IdxSet : Val(m) # BOT
\*            /\ \A m \in 0..(L-1) : A[m] # BOT => m \in IdxSet
\*            /\ \E alpha \in Perm(IdxSet) : 
\*               /\ Justified(alpha)
\*               /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
\*               /\ WellFormed(c, IdxSet)}
        <4>A. S' = {d \in ConfigDomain : 
                        \E iset \in SUBSET 0..(L'-1) :
                            /\ \A m \in iset : Val(m)' # BOT                  
                            /\ \A m \in 0..(L'-1) : A'[m] # BOT => m \in iset  
                            /\ \E alph \in Perm(iset) : 
                                /\ Justified(alph)'
                                /\ d.state = [i \in 1..Len(alph) |-> Val(alph[i])']
                                /\ WellFormed(d, iset)'}
          BY DEF S
        <4>B. L = L'
          OBVIOUS
        <4>C. S' = {d \in ConfigDomain : 
                        \E iset \in SUBSET 0..(L-1) :
                            /\ \A m \in iset : Val(m)' # BOT                  
                            /\ \A m \in 0..(L-1) : A'[m] # BOT => m \in iset  
                            /\ \E alph \in Perm(iset) : 
                                /\ Justified(alph)'
                                /\ d.state = [i \in 1..Len(alph) |-> Val(alph[i])']
                                /\ WellFormed(d, iset)'}
          BY <4>A, <4>B DEF Val
        <4> DEFINE Q(d, iset) == \E alph \in Perm(iset) : 
                                      /\ Justified(alph)'
                                      /\ d.state = [i \in 1..Len(alph) |-> Val(alph[i])]
                                      /\ WellFormed(d, iset)'
        <4>20. S' = {d \in ConfigDomain : 
                        \E iset \in SUBSET 0..(L-1) :
                            /\ \A m \in iset : Val(m) # BOT                  
                            /\ \A m \in 0..(L-1) : A[m] # BOT => m \in iset  
                            /\ Q(d, iset)}
          BY DEF S, Val
        <4>21. Q(c, IdxSet)
          <5> SUFFICES /\ Justified(alpha)'
                       /\ c.state = [i \in 1..Len(alpha) |-> Val(alpha[i])]
                       /\ WellFormed(c, IdxSet)'
            BY <4>10, Zenon
          <5> QED
            BY <4>11, <4>12, <4>19, Zenon
        <4> HIDE DEF c, Q
        <4> QED
          BY <4>20, <4>5, <4>6, <4>17, <4>21
      <3>9. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next, IntLine, IntLines, RetLine, RetLines 
    <2>10. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Inv
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Fri Feb 02 19:17:03 EST 2024 by uguryavuz
\* Created Wed Jan 10 07:15:14 EST 2024 by uguryavuz
