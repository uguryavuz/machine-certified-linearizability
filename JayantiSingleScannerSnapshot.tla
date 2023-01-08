-------------------------- MODULE JayantiSingleScannerSnapshot --------------------------

EXTENDS Integers, TLC, FiniteSets, TLAPS

CONSTANTS ACK, BOT, N, N_COMPS
VARIABLES pc, X, A, B, a, i, v, j, M
vars == <<pc, X, A, B, a, i, v, j, M>>

\* A few useful definitions
IndexSet == 0..(N_COMPS-1)
WProcSet == 1..N
S        == N+1      \* N+1 is the scanner.
AllProcs == 1..S

\* Assumptions
ASSUME AckBotDef == /\ ACK \notin Nat
                    /\ BOT \notin Nat
                    /\ ACK /= BOT
                    /\ BOT \notin [IndexSet -> Nat]
                    
ASSUME PDef ==  /\ N \in Nat \ {0}
                /\ N_COMPS \in Nat \ {0}

\* Defining the domain of tuples
tTypeOK(t) == /\ \A p \in WProcSet : /\ pc[p] \in 0..1 => t.res[p] = BOT
                                     /\ pc[p] \in 2..4 => t.res[p] \in {ACK, BOT}
              /\ pc[S] \in 5..8  => t.res[S] = BOT
              /\ pc[S] \in 9..10 => t.res[S] \in [IndexSet -> Nat]

CorrectTupleDomain == {t \in [state: [IndexSet -> Nat], 
                              res: [AllProcs -> [IndexSet -> Nat] \union {ACK, BOT}]] : tTypeOK(t)}

\* Some useful expressions
Map(d, e)   == [x \in {d} |-> e]
Merge(f, g) == [x \in (DOMAIN f) \cup (DOMAIN g) |-> IF x \in DOMAIN f THEN f[x] ELSE g[x]]

TypeOK == /\ pc \in [AllProcs -> 0..10]
          /\ \A p \in WProcSet : pc[p] \in 0..4
          /\ i \in [WProcSet -> IndexSet]
          /\ \A p, q \in WProcSet : (i[p] = i[q] /\ pc[p] /= 0 /\ pc[q] /= 0) => p = q
          /\ v \in [WProcSet -> Nat]
          /\ pc[S] \in 5..10
          /\ X \in BOOLEAN
          /\ A \in [IndexSet -> Nat]
          /\ B \in [IndexSet -> Nat \union {BOT}]
          /\ a \in [IndexSet -> Nat]
          /\ j \in 0..N_COMPS
          /\ M \in SUBSET CorrectTupleDomain
             
\* Delta, set of possible return values for the kth component
D(k) == CASE pc[S] = 5  -> {A[k]}
          [] pc[S] = 6  -> (CASE (k < j /\ B[k] /= BOT) -> {A[k], B[k]}
                              [] OTHER                  -> {A[k]})
          [] pc[S] = 7  -> (CASE (B[k] /= BOT)          -> {A[k], B[k]}
                              [] (k < j /\ B[k] = BOT)  -> {A[k], a[k]}
                              [] OTHER                  -> {A[k]})
          [] pc[S] = 8  -> (CASE (B[k] /= BOT)          -> {A[k], B[k]}
                              [] OTHER                  -> {A[k], a[k]})
          [] pc[S] = 9  -> LET kActiveWriter == (\E p \in WProcSet : pc[p] = 3 /\ i[p] = k)
                           IN (CASE (kActiveWriter  /\ B[k] /= BOT  /\ k >= j) -> {A[k], B[k]}
                                 [] (kActiveWriter  /\ B[k] = BOT   /\ k >= j) -> {A[k], a[k]}
                                 [] (~kActiveWriter /\ B[k] /= BOT  /\ k >= j) -> {B[k]}
                                 [] OTHER                                      -> {a[k]})
          [] pc[S] = 10 -> {a[k]}
          
\* Initial configuration
Init == /\ pc = Merge([p \in WProcSet |-> 0], Map(S, 5))
        /\ X = FALSE
        /\ A \in [IndexSet -> Nat]
        /\ B \in [IndexSet -> Nat \union {BOT}]
        /\ a \in [IndexSet -> Nat]
        /\ i \in [WProcSet -> IndexSet]
        /\ v \in [WProcSet -> Nat]
        /\ j \in 0..N_COMPS
        /\ M = {[state |-> A, res |-> [p \in AllProcs |-> BOT]]}
        


\* Write(i, v)
\* -----------
\* 1.  A[i] <- v
\* 2.  if X:
\* 3.     B[i] <- v
\* 4.  return ack

L00(p) == /\ pc[p] = 0
          /\ \E k \in IndexSet : /\ \A q \in WProcSet : pc[q] /= 0 => i[q] /= k
                                 /\ i' = [i EXCEPT ![p] = k]
          /\ \E w \in Nat : v' = [v EXCEPT ![p] = w]
          /\ pc' = [pc EXCEPT ![p] = 1]
          /\ UNCHANGED <<X, A, B, a, j, M>>

L01(p) == /\ pc[p] = 1
          /\ A' = [A EXCEPT ![i[p]] = v[p]]
          /\ M' = M \union {[state |-> [t.state EXCEPT ![i[p]] = v[p]], 
                             res   |-> [t.res   EXCEPT ![p]    = ACK]]: t \in M}
          /\ pc' = [pc EXCEPT ![p] = 2]
          /\ UNCHANGED <<X, B, a, i, v, j>>
    
L02(p) == /\ pc[p] = 2
          /\ IF X = TRUE
                THEN pc' = [pc EXCEPT ![p] = 3]
                ELSE pc' = [pc EXCEPT ![p] = 4]
          /\ UNCHANGED <<X, A, B, a, i, v, j, M>>
          
L03(p) == /\ pc[p] = 3
          /\ B' = [B EXCEPT ![i[p]] = v[p]]
          /\ pc' = [pc EXCEPT ![p] = 4]
          /\ UNCHANGED <<X, A, a, i, v, j, M>>
          
L04(p) == /\ pc[p] = 4
          /\ M' = {[state |-> t.state,
                    res   |-> [t.res EXCEPT ![p] = BOT]] : t \in {u \in M : u.res[p] = ACK}}
          /\ pc' = [pc EXCEPT ![p] = 0]
          /\ UNCHANGED <<X, A, B, a, i, v, j>>
          
\* Scan()
\* ------
\* 5.  X <- true
\* 6.  for j <- 0..N_COMPS-1: B[j] <- BOT
\* 7.  for j <- 0..N_COMPS-1: a[j] <- A[j]
\* 8.  X <- false
\* 9.  for j <- 0..N_COMPS-1:
\*         if B[j] != BOT:
\*            a[j] <- B[j]
\* 10. return ack

L05    == /\ pc[S] = 5
          /\ X' = TRUE
          /\ pc' = [pc EXCEPT ![S] = 6]
          /\ j' = 0
          /\ UNCHANGED <<A, B, a, i, v, M>>
          
L06    == /\ pc[S] = 6
          /\ IF j < N_COMPS
                THEN /\ pc' = pc
                     /\ j' = j + 1
                     /\ B' = [B EXCEPT ![j] = BOT]
                ELSE /\ pc' = [pc EXCEPT ![S] = 7]
                     /\ j' = 0
                     /\ B' = B
          /\ UNCHANGED <<X, A, a, i, v, M>>
          
L07    == /\ pc[S] = 7
          /\ IF j < N_COMPS
                THEN /\ pc' = pc
                     /\ j' = j + 1
                     /\ a' = [a EXCEPT ![j] = A[j]]
                ELSE /\ pc' = [pc EXCEPT ![S] = 8]
                     /\ j' = j
                     /\ a' = a
          /\ UNCHANGED <<X, A, B, i, v, M>>
          
L08    == /\ pc[S] = 8
          /\ X' = FALSE
          /\ pc' = [pc EXCEPT ![S] = 9]
          /\ j' = 0
          /\ M' = {[state |-> A,
                    res   |-> Merge([p \in WProcSet |-> IF pc[p] \in {0, 1} THEN BOT ELSE ACK], Map(S, t.state))]: t \in M}
          /\ UNCHANGED <<A, B, a, i, v>>
          
L09   == /\ pc[S] = 9
         /\ IF j < N_COMPS
               THEN /\ pc' = pc
                    /\ j' = j + 1
                    /\ IF B[j] /= BOT
                          THEN a' = [a EXCEPT ![j] = B[j]]
                          ELSE a' = a
               ELSE /\ pc' = [pc EXCEPT ![S] = 10]
                    /\ j' = j
                    /\ a' = a
         /\ UNCHANGED <<X, A, B, i, v, M>>
         
L10   == /\ pc[S] = 10
         /\ M' = {[state |-> t.state,
                   res   |-> [t.res EXCEPT ![S] = BOT]] : t \in {u \in M : u.res[S] = a}}
         /\ pc' = [pc EXCEPT ![S] = 5]
         /\ UNCHANGED <<X, A, B, a, i, v, j>>

Next  == \/ \E p \in WProcSet : \/ L00(p)
                                \/ L01(p)
                                \/ L02(p)
                                \/ L03(p)
                                \/ L04(p)
         \/ L05
         \/ L06
         \/ L07
         \/ L08
         \/ L09
         \/ L10
         
Spec  == /\ Init
         /\ [][Next]_vars

InvNL == M /= {}

InvC == \A p, q \in WProcSet: (pc[p] \in 1..4 /\ pc[q] \in 1..4 /\ i[p] = i[q]) => p = q 

Inv00 == \A p \in WProcSet : pc[p] = 0 => \A t \in M : t.res[p] = BOT

Inv01 == \A p \in WProcSet : pc[p] = 1 => \A t \in M : t.state[i[p]] = A[i[p]] /\ t.res[p] = BOT

Inv_W1 == \A p \in WProcSet : pc[p] \in 2..4 => \A t \in M : t.state[i[p]] /= A[i[p]] => t.res[p] = BOT

Inv_W2 == \A p \in WProcSet : pc[p] \in 2..4 => \A t \in M : \E u \in M : /\ u.state = [t.state EXCEPT ![i[p]] = A[i[p]]]
                                                                          /\ u.res = [t.res EXCEPT ![p] = ACK]

Inv_W3 == \A p \in WProcSet : pc[p] \in 2..4 => A[i[p]] = v[p]

Inv_W4 == \A k \in IndexSet : (\A p \in WProcSet : pc[p] = 0 \/ i[p] /= k) => \A t \in M : t.state[k] = A[k]

InvW == /\ Inv_W3
        /\ Inv_W2
        /\ Inv_W1
        /\ InvC
        /\ Inv_W4

AlphaDomain == {f \in [IndexSet -> UNION {D(k) : k \in IndexSet}] : (\A k \in IndexSet : f[k] \in D(k))}

Inv05 == pc[S] = 5 => \A t \in M : t.res[S] = BOT

InvS_1 == pc[S] \in 5..8 => \A alpha \in AlphaDomain : \E t \in M : /\ t.state = alpha
                                                                    /\ t.res[S] = BOT
                                                                    
InvS_2 == pc[S] \in 9..10 => \A alpha \in AlphaDomain : \E t \in M : /\ t.state = A
                                                                     /\ t.res[S] = alpha
                                                                     
InvS_3 == pc[S] \in 6..8 <=> X = TRUE

InvS_4 == \A k \in IndexSet : (/\ (pc[S] = 8 \/ (pc[S] = 7 /\ k < j)) 
                               /\ B[k] = BOT 
                               /\ (\A p \in WProcSet : i[p] = k => pc[p] \in {0, 1, 4})) => A[k] = a[k]
                               
InvS_5 == \A k \in IndexSet : (/\ (pc[S] \in 7..8 \/ (pc[S] = 6 /\ k < j)) 
                               /\ B[k] /= BOT
                               /\ (\A p \in WProcSet : i[p] = k => pc[p] \in {0, 1, 4})) => A[k] = B[k]

InvS == /\ InvS_1
        /\ InvS_2
        /\ InvS_3
        /\ InvS_4
        /\ InvS_5

Inv == /\ TypeOK
       /\ InvNL
       /\ InvW
       /\ InvS
       /\ Inv00
       /\ Inv01
       /\ Inv05

ISpec == /\ Inv
         /\ [][Next]_vars


THEOREM Spec => []Inv
<1> USE AckBotDef, PDef DEFS Inv, Map, Merge, AllProcs, WProcSet, S
<1> SUFFICES /\ (Init => Inv)
             /\ (Inv /\ [Next]_vars => Inv')
  BY PTL DEF Spec
<1>1. Init => Inv
  <2> USE DEF Init
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    <3>1. pc \in [AllProcs -> 0..10]
      BY DEF TypeOK
    <3>2. \A p \in WProcSet : pc[p] \in 0..4
      BY DEF TypeOK
    <3>3. i \in [WProcSet -> IndexSet]
      BY DEF TypeOK
    <3>4. \A p, q \in WProcSet : (i[p] = i[q] /\ pc[p] /= 0 /\ pc[q] /= 0) => p = q
      BY DEF TypeOK
    <3>5. v \in [WProcSet -> Nat]
      BY DEF TypeOK
    <3>6. pc[S] \in 5..10
      BY DEF TypeOK
    <3>7. X \in BOOLEAN
      BY DEF TypeOK
    <3>8. A \in [IndexSet -> Nat]
      BY DEF TypeOK
    <3>9. B \in [IndexSet -> Nat \union {BOT}]
      BY DEF TypeOK
    <3>10. a \in [IndexSet -> Nat]
      BY DEF TypeOK
    <3>11. j \in 0..N_COMPS
      BY DEF TypeOK
    <3>12. M \in SUBSET CorrectTupleDomain
      BY DEF CorrectTupleDomain, TypeOK, tTypeOK
    <3>13. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
        
  <2>2. InvNL
    BY DEF InvNL
  <2>3. InvW
    <3>1. Inv_W3
      BY DEF Inv_W3
    <3>2. Inv_W2
      BY DEF Inv_W2
    <3>3. Inv_W1
      BY DEF Inv_W1
    <3>4. InvC
      BY DEF InvC
    <3>5. Inv_W4
      BY DEF Inv_W4
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF InvW
  <2>4. InvS
    <3>1. InvS_1
      BY DEF D, AlphaDomain, InvS_1
    <3>2. InvS_2
      BY DEF InvS_2
    <3>3. InvS_3
      BY DEF InvS_3
    <3>4. InvS_4
      BY DEF InvS_4
    <3>5. InvS_5
      BY DEF InvS_5
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF InvS
  <2>5. Inv00
    BY DEF Inv00  
  <2>6. Inv01
    BY DEF Inv01
  <2>7. Inv05
    BY DEF Inv05
  <2>8. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> USE DEFS Next, vars
  <2> SUFFICES ASSUME Inv /\ [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. TypeOK'
    <3> USE DEF TypeOK, CorrectTupleDomain, tTypeOK  
    <3>1. CASE \E p \in WProcSet : \/ L00(p)
                                   \/ L01(p)
                                   \/ L02(p)
                                   \/ L03(p)
                                   \/ L04(p)
      <4> SUFFICES ASSUME NEW p \in WProcSet,
                          \/ L00(p)
                          \/ L01(p)
                          \/ L02(p)
                          \/ L03(p)
                          \/ L04(p)
                   PROVE  TypeOK'
        BY <3>1 
      <4>1. CASE L00(p)
        BY <4>1, <3>1 DEF L00
      <4>2. CASE L01(p)
        <5> USE <4>2, <3>1 DEF L01
        <5>1. (pc \in [AllProcs -> 0..10])'
          OBVIOUS
        <5>2. (\A p_1 \in WProcSet : pc[p_1] \in 0..4)'
          OBVIOUS
        <5>3. (i \in [WProcSet -> IndexSet])'
          OBVIOUS
        <5>4. (\A p_1, q \in WProcSet : (i[p_1] = i[q] /\ pc[p_1] /= 0 /\ pc[q] /= 0) => p_1 = q)'
          OBVIOUS
        <5>5. (v \in [WProcSet -> Nat])'
          OBVIOUS
        <5>6. (pc[S] \in 5..10)'
          OBVIOUS
        <5>7. (X \in BOOLEAN)'
          OBVIOUS
        <5>8. (A \in [IndexSet -> Nat])'
          OBVIOUS
        <5>9. (B \in [IndexSet -> Nat \union {BOT}])'
          OBVIOUS
        <5>10. (a \in [IndexSet -> Nat])'
          OBVIOUS
        <5>11. (j \in 0..N_COMPS)'
          OBVIOUS
        <5>12. (M \in SUBSET CorrectTupleDomain)'
          <6> SUFFICES ASSUME NEW u \in M'
                       PROVE  u \in CorrectTupleDomain'
            OBVIOUS
          <6>1. CASE u \in M
            BY <6>1
          <6>2. CASE u \in {[state |-> [t.state EXCEPT ![i[p]] = v[p]], res |-> [t.res EXCEPT ![p] = ACK]] : t \in M}
            <7> USE <6>2
            <7>1. PICK t \in M : u = [state |-> [t.state EXCEPT ![i[p]] = v[p]], res |-> [t.res EXCEPT ![p] = ACK]]
              OBVIOUS
            <7>2. /\ u \in [state: [IndexSet -> Nat], res: [AllProcs -> [IndexSet -> Nat] \union {ACK, BOT}]]
                  /\ \A q \in AllProcs : p /= q => u.res[q] = t.res[q]
                  /\ /\ pc'[p] = 2
                     /\ u.res[p] = ACK
              BY <7>1 DEF TypeOK
            <7>3. tTypeOK(u)'
              BY <7>1, <7>2 DEF TypeOK
            <7>5. QED
              BY <7>1, <7>3
          <6>3. QED
            BY <6>1, <6>2
        <5>13. QED
          BY <5>1, <5>10, <5>11, <5>12, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9 DEF TypeOK

      <4>3. CASE L02(p)
        BY <4>3, <3>1 DEF L02
      <4>4. CASE L03(p)
        BY <4>4, <3>1 DEF L03
      <4>5. CASE L04(p)
        <5>1. (pc \in [AllProcs -> 0..10])'
          BY <4>5, <3>1 DEF L04
        <5>2. (\A p_1 \in WProcSet : pc[p_1] \in 0..4)'
          BY <4>5, <3>1 DEF L04
        <5>3. (i \in [WProcSet -> IndexSet])'
          BY <4>5, <3>1 DEF L04
        <5>4. (\A p_1, q \in WProcSet : (i[p_1] = i[q] /\ pc[p_1] /= 0 /\ pc[q] /= 0) => p_1 = q)'
          BY <4>5, <3>1 DEF L04
        <5>5. (v \in [WProcSet -> Nat])'
          BY <4>5, <3>1 DEF L04
        <5>6. (pc[S] \in 5..10)'
          BY <4>5, <3>1 DEF L04
        <5>7. (X \in BOOLEAN)'
          BY <4>5, <3>1 DEF L04
        <5>8. (A \in [IndexSet -> Nat])'
          BY <4>5, <3>1 DEF L04
        <5>9. (B \in [IndexSet -> Nat \union {BOT}])'
          BY <4>5, <3>1 DEF L04
        <5>10. (a \in [IndexSet -> Nat])'
          BY <4>5, <3>1 DEF L04
        <5>11. (j \in 0..N_COMPS)'
          BY <4>5, <3>1 DEF L04
        <5>12. (M \in SUBSET CorrectTupleDomain)'
          <6> USE <4>5, <3>1 DEF L04
          <6> SUFFICES ASSUME NEW u \in M'
                   PROVE u \in CorrectTupleDomain'
            OBVIOUS
          <6>1. \E t \in M : /\ u = [state |-> t.state, res |-> [t.res EXCEPT ![p] = BOT]]
                             /\ t.res[p] = ACK
            OBVIOUS
          <6>2. u \in [state: [IndexSet -> Nat], res: [AllProcs -> [IndexSet -> Nat] \union {ACK, BOT}]]
            BY <6>1
          <6>3. tTypeOK(u)'
            BY <6>1
          <6> QED
            BY <6>2, <6>3
        <5>13. QED
          BY <5>1, <5>10, <5>11, <5>12, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9 DEF TypeOK
        
      <4>6. QED
        BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5
    <3>2. CASE L05
      BY <3>2 DEF L05
    <3>3. CASE L06
      BY <3>3 DEF L06
    <3>4. CASE L07
      <4>1. (pc \in [AllProcs -> 0..10])'
        BY <3>4 DEF L07
      <4>2. (\A p \in WProcSet : pc[p] \in 0..4)'
        BY <3>4 DEF L07
      <4>3. (i \in [WProcSet -> IndexSet])'
        BY <3>4 DEF L07
      <4>4. (\A p, q \in WProcSet : (i[p] = i[q] /\ pc[p] /= 0 /\ pc[q] /= 0) => p = q)'
        BY <3>4 DEF L07
      <4>5. (v \in [WProcSet -> Nat])'
        BY <3>4 DEF L07
      <4>6. (pc[S] \in 5..10)'
        BY <3>4 DEF L07
      <4>7. (X \in BOOLEAN)'
        BY <3>4 DEF L07
      <4>8. (A \in [IndexSet -> Nat])'
        BY <3>4 DEF L07
      <4>9. (B \in [IndexSet -> Nat \union {BOT}])'
        BY <3>4 DEF L07
      <4>10. (a \in [IndexSet -> Nat])'
        BY <3>4 DEF L07
      <4>11. (j \in 0..N_COMPS)'
        BY <3>4 DEF L07
      <4>12. (M \in SUBSET CorrectTupleDomain)'
        BY <3>4 DEF L07
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF TypeOK
      
    <3>5. CASE L08
      <4>1. (pc \in [AllProcs -> 0..10])'
        BY <3>5 DEF L08
      <4>2. (\A p \in WProcSet : pc[p] \in 0..4)'
        BY <3>5 DEF L08
      <4>3. (i \in [WProcSet -> IndexSet])'
        BY <3>5 DEF L08
      <4>4. (\A p, q \in WProcSet : (i[p] = i[q] /\ pc[p] /= 0 /\ pc[q] /= 0) => p = q)'
        BY <3>5 DEF L08
      <4>5. (v \in [WProcSet -> Nat])'
        BY <3>5 DEF L08
      <4>6. (pc[S] \in 5..10)'
        BY <3>5 DEF L08
      <4>7. (X \in BOOLEAN)'
        BY <3>5 DEF L08
      <4>8. (A \in [IndexSet -> Nat])'
        BY <3>5 DEF L08
      <4>9. (B \in [IndexSet -> Nat \union {BOT}])'
        BY <3>5 DEF L08
      <4>10. (a \in [IndexSet -> Nat])'
        BY <3>5 DEF L08
      <4>11. (j \in 0..N_COMPS)'
        BY <3>5 DEF L08
      <4>12. (M \in SUBSET CorrectTupleDomain)'
        <5> SUFFICES ASSUME NEW t \in M'
                     PROVE t \in CorrectTupleDomain'
          OBVIOUS
        <5>1. QED
          BY <3>5 DEF L08
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF TypeOK
    <3>6. CASE L09
      <4>1. (pc \in [AllProcs -> 0..10])'
        BY <3>6 DEF L09
      <4>2. (\A p \in WProcSet : pc[p] \in 0..4)'
        BY <3>6 DEF L09
      <4>3. (i \in [WProcSet -> IndexSet])'
        BY <3>6 DEF L09
      <4>4. (\A p, q \in WProcSet : (i[p] = i[q] /\ pc[p] /= 0 /\ pc[q] /= 0) => p = q)'
        BY <3>6 DEF L09
      <4>5. (v \in [WProcSet -> Nat])'
        BY <3>6 DEF L09
      <4>6. (pc[S] \in 5..10)'
        BY <3>6 DEF L09
      <4>7. (X \in BOOLEAN)'
        BY <3>6 DEF L09
      <4>8. (A \in [IndexSet -> Nat])'
        BY <3>6 DEF L09
      <4>9. (B \in [IndexSet -> Nat \union {BOT}])'
        BY <3>6 DEF L09
      <4>10. (a \in [IndexSet -> Nat])'
        BY <3>6 DEF L09
      <4>11. (j \in 0..N_COMPS)'
        BY <3>6 DEF L09
      <4>12. (M \in SUBSET CorrectTupleDomain)'
        BY <3>6 DEF L09
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF TypeOK
      
    <3>7. CASE L10
      <4>1. (pc \in [AllProcs -> 0..10])'
        BY <3>7 DEF L10
      <4>2. (\A p \in WProcSet : pc[p] \in 0..4)'
        BY <3>7 DEF L10
      <4>3. (i \in [WProcSet -> IndexSet])'
        BY <3>7 DEF L10
      <4>4. (\A p, q \in WProcSet : (i[p] = i[q] /\ pc[p] /= 0 /\ pc[q] /= 0) => p = q)'
        BY <3>7 DEF L10
      <4>5. (v \in [WProcSet -> Nat])'
        BY <3>7 DEF L10
      <4>6. (pc[S] \in 5..10)'
        BY <3>7 DEF L10
      <4>7. (X \in BOOLEAN)'
        BY <3>7 DEF L10
      <4>8. (A \in [IndexSet -> Nat])'
        BY <3>7 DEF L10
      <4>9. (B \in [IndexSet -> Nat \union {BOT}])'
        BY <3>7 DEF L10
      <4>10. (a \in [IndexSet -> Nat])'
        BY <3>7 DEF L10
      <4>11. (j \in 0..N_COMPS)'
        BY <3>7 DEF L10
      <4>12. (M \in SUBSET CorrectTupleDomain)'
        <5> USE <3>7 DEF L10
        <5> SUFFICES ASSUME NEW u \in M'
                     PROVE u \in CorrectTupleDomain'
          OBVIOUS
        <5>1. \E t \in M : /\ u = [state |-> t.state, res |-> [t.res EXCEPT ![S] = BOT]]
                           /\ t.res[S] = a
           OBVIOUS
        <5>2. u \in [state: [IndexSet -> Nat], res: [AllProcs -> [IndexSet -> Nat] \union {ACK, BOT}]]
          BY <5>1
        <5>3. tTypeOK(u)'
          BY <5>1
        <5>4. QED
            BY <5>2, <5>3
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF TypeOK
    <3>8. CASE UNCHANGED vars
      BY <3>8
    <3>9. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8 DEF Next
  <2>2. InvNL'
    <3> USE DEF InvNL
    <3>1. ASSUME NEW p \in WProcSet,
                 L00(p)
          PROVE  InvNL'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in WProcSet,
                 L01(p)
          PROVE  InvNL'
      BY <3>2 DEF L01
    <3>3. ASSUME NEW p \in WProcSet,
                 L02(p)
          PROVE  InvNL'
      BY <3>3 DEF L02
    <3>4. ASSUME NEW p \in WProcSet,
                 L03(p)
          PROVE  InvNL'
      BY <3>4 DEF L03
    <3>5. ASSUME NEW p \in WProcSet,
                 L04(p)
          PROVE  InvNL'
      <4> USE <3>5 DEF L04
      <4>1. PICK t \in M : TRUE
        OBVIOUS
      <4>2. PICK u \in M : /\ u.state = [t.state EXCEPT ![i[p]] = A[i[p]]]
                           /\ u.res = [t.res EXCEPT ![p] = ACK]
        BY <4>1, Isa DEF InvW, Inv_W2, TypeOK
      <4>3. u.res[p] = ACK
        BY <4>2 DEF TypeOK, CorrectTupleDomain
      <4> QED
        BY <4>3
    <3>6. CASE L05
      BY <3>6 DEF L05
    <3>7. CASE L06
      BY <3>7 DEF L06
    <3>8. CASE L07
      BY <3>8 DEF L07
    <3>9. CASE L08
      BY <3>9 DEF L08
    <3>10. CASE L09
      BY <3>10 DEF L09
    <3>11. CASE L10
      <4> USE <3>11 DEF L10
      <4>1. \A k \in IndexSet : D(k) = {a[k]}
        BY DEF D
      <4>2. PICK alpha \in AlphaDomain : alpha = a
        BY <4>1 DEF AlphaDomain, IndexSet, TypeOK
      <4>3. \E t \in M : t.res[S] = a
        BY <4>2 DEF InvS, InvS_2, TypeOK
      <4> QED
        BY <4>2, <4>3
    <3>12. CASE UNCHANGED vars
      BY <3>12 DEF vars
    <3>13. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
  <2>3. InvW'
    <3> USE DEF InvW
    <3>1. Inv_W3'
      <4> USE DEF Inv_W3
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  Inv_W3'
        BY <4>1 DEF L00
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  Inv_W3'
        BY <4>2 DEF L01, TypeOK
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  Inv_W3'
        BY <4>3 DEF L02, TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  Inv_W3'
        BY <4>4 DEF L03
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  Inv_W3'
        BY <4>5 DEF L04
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        BY <4>11 DEF L10
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
      
    <3>2. Inv_W2'
      <4> USE DEF Inv_W2
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  Inv_W2'
        BY <4>1 DEF L00
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  Inv_W2'
        <5> USE <4>2 DEF L01
        <5> SUFFICES ASSUME NEW q \in WProcSet,
                    pc'[q] \in 2..4,
                    NEW t \in M'
             PROVE  \E u \in M' : /\ u.state = [t.state EXCEPT ![i'[q]] = A'[i'[q]]]
                                  /\ u.res = [t.res EXCEPT ![q] = ACK]
          BY Zenon
        <5>1. CASE p = q
          <6> USE <5>1
          <6>1. CASE t \in M
            <7> USE <6>1
            <7>1. PICK u \in M' : u = [state |-> [t.state EXCEPT ![i[q]] = v[q]], res |-> [t.res EXCEPT ![q] = ACK]]
              BY Zenon
            <7> QED
              BY <3>1, <7>1 DEF Inv_W3
          <6>2. CASE t \notin M
            BY <3>1, <6>2 DEF Inv_W3
          <6>3. QED
            BY <6>1, <6>2
        <5>2. CASE p /= q
          <6> USE <5>2
          <6>1. CASE t \in M
            <7> USE <6>1
            <7>1. \E u \in M : /\ u.state = [t.state EXCEPT ![i[q]] = A[i[q]]]
                               /\ u.res = [t.res EXCEPT ![q] = ACK]
              OBVIOUS
            <7>2. /\ i[q] = i'[q]
                  /\ A'[i'[q]] = A[i[q]]
              BY DEF InvC
            <7>3. QED
              BY <7>1, <7>2
          <6>2. CASE t \notin M
            <7> USE <6>2
            <7>1. PICK t_ \in M : t = [state |-> [t_.state EXCEPT ![i[p]] = v[p]], 
                                       res   |-> [t_.res   EXCEPT ![p]    = ACK]]
              OBVIOUS
            <7>2. PICK u_ \in M : /\ u_.state = [t_.state EXCEPT ![i[q]] = A[i[q]]]
                                  /\ u_.res = [t_.res EXCEPT ![q] = ACK]
              BY <7>1
            <7>3. /\ i[q] = i'[q]
                  /\ A'[i'[q]] = A[i[q]]
              BY DEF InvC
            <7>4. PICK u \in M' : u = [state |-> [u_.state EXCEPT ![i[p]] = v[p]], 
                                       res   |-> [u_.res   EXCEPT ![p]    = ACK]]
              BY Zenon
            <7>5. u.state = [t.state EXCEPT ![i'[q]] = A'[i'[q]]]
              BY <7>1, <7>2, <7>3, <7>4
            <7>6. u.res = [t.res EXCEPT ![q] = ACK]
              BY <7>1, <7>2, <7>3, <7>4
            <7> QED
              BY <7>5, <7>6
          <6>3. QED
            BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>2 DEF L01
        
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  Inv_W2'
        BY <4>3 DEF L02, TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  Inv_W2'
        BY <4>4 DEF L03
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  Inv_W2'
        <5> USE <4>5 DEF L04
        <5> SUFFICES ASSUME NEW q \in WProcSet,
                            (pc[q] \in 2..4)',
                            NEW u \in M'
                     PROVE  \E w \in M' : /\ w.state = [u.state EXCEPT ![i'[q]] = A'[i'[q]]]
                                          /\ w.res = [u.res EXCEPT ![q] = ACK]
          OBVIOUS
        <5>1. PICK t_1 \in M : /\ u = [state |-> t_1.state,
                                       res   |-> [t_1.res EXCEPT ![p] = BOT]]
                               /\ t_1.res[p] = ACK
          OBVIOUS
        <5>2. PICK t \in M : /\ t.state = [t_1.state EXCEPT ![i'[q]] = A'[i'[q]]]
                             /\ t.res = [t_1.res EXCEPT ![q] = ACK]
          BY <5>1
        <5>3. t.res[p] = ACK
          BY <5>1, <5>2
        <5>4. PICK w \in M' : w = [state |-> t.state,
                                   res   |-> [t.res EXCEPT ![p] = BOT]]
          BY <5>3
        <5>5. w.state = [u.state EXCEPT ![i'[q]] = A'[i'[q]]]
          BY <5>1, <5>2, <5>4
        <5>6. p /= q
          BY DEF TypeOK
        <5>7. w.res = [u.res EXCEPT ![q] = ACK]
          BY <5>1, <5>2, <5>4, <5>6
        <5> QED
          BY <5>4, <5>5, <5>7
        
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        <5> USE <4>9 DEF L08
        <5> SUFFICES ASSUME NEW p \in WProcSet,
                            pc'[p] \in 2..4,
                            NEW u \in M'
                     PROVE  \E w \in M' : /\ w.state = [u.state EXCEPT ![i'[p]] = A'[i'[p]]]
                                          /\ w.res = [u.res EXCEPT ![p] = ACK]
          BY DEF TypeOK
        <5>1. PICK t_1 \in M : u = [state |-> A,
                                    res   |-> Merge([q \in WProcSet |-> IF pc[q] \in {0, 1} THEN BOT ELSE ACK],
                                                    Map(S, t_1.state))]
          OBVIOUS
        <5>2. u.state[i'[p]] = A'[i'[p]]
          BY <5>1
        <5>3. u.res[p] = ACK
          BY <5>1
        <5>4. /\ u.state = [u.state EXCEPT ![i'[p]] = A'[i'[p]]]
              /\ u.res = [u.res EXCEPT ![p] = ACK]
          BY <5>2, <5>3 DEF TypeOK, CorrectTupleDomain
        <5> QED
          BY <5>4
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        <5> USE <4>11 DEF L10
        <5> SUFFICES ASSUME NEW p \in WProcSet,
                            pc'[p] \in 2..4,
                            NEW u \in M'
                     PROVE  \E w \in M' : /\ w.state = [u.state EXCEPT ![i'[p]] = A'[i'[p]]]
                                          /\ w.res = [u.res EXCEPT ![p] = ACK]
          BY DEF TypeOK
        <5>1. PICK t_1 \in M : /\ u = [state |-> t_1.state,
                                       res   |-> [t_1.res EXCEPT ![S] = BOT]]
                               /\ t_1.res[S] = a
          OBVIOUS
        <5>2. PICK t \in M : /\ t.state = [t_1.state EXCEPT ![i[p]] = A[i[p]]]
                             /\ t.res = [t_1.res EXCEPT ![p] = ACK]
          OBVIOUS
        <5>3.  t.res[S] = a
          BY <5>1, <5>2 DEF TypeOK
        <5>4. PICK w \in M' : w = [state |-> t.state,
                                   res   |-> [t.res EXCEPT ![S] = BOT]]
          BY Isa, <5>2, <5>3
        <5>5. w.state = [u.state EXCEPT ![i'[p]] = A'[i'[p]]]
          BY <5>1, <5>2, <5>4
        <5>6. w.res = [u.res EXCEPT ![p] = ACK]
          BY <5>1, <5>2, <5>4
        <5> QED
          BY <5>4, <5>5, <5>6
        
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
    <3>3. Inv_W1'
      <4> USE DEF Inv_W1
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  Inv_W1'
        BY <4>1 DEF L00
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  Inv_W1'
        <5> USE <4>2 DEF L01
        <5> SUFFICES ASSUME NEW q \in WProcSet',
                            pc'[q] \in 2..4,
                            NEW u \in M',
                            u.state[i[q]] /= A'[i[q]]
                     PROVE  u.res[q] = BOT
          OBVIOUS
        <5>1. CASE u \in M
          <6> USE <5>1
          <6>1. CASE q /= p
            <7> USE <6>1
            <7>1. A'[i[q]] = A[i[q]]
              BY DEF TypeOK
            <7> QED
              BY <7>1
          <6>2. CASE q = p 
            <7> QED
              BY <6>1 DEF Inv01
          <6> QED
            BY <6>1, <6>2
        <5>2. CASE u \notin M
          <6> USE <5>2
          <6>1. PICK t \in M : u = [state |-> [t.state EXCEPT ![i[p]] = v[p]], 
                                    res   |-> [t.res   EXCEPT ![p]    = ACK]]
            OBVIOUS
          <6>2. CASE q /= p
            <7> USE <6>2
            <7>1. A'[i[q]] = A[i[q]]
              BY DEF TypeOK
            <7>2. u.state[i[q]] = t.state[i[q]]
              BY <6>1 DEF TypeOK
            <7> QED
              BY <6>1, <7>1, <7>2
          <6>3. CASE q = p
            <7> USE <6>3
            <7>1. u.state[i[p]] = A'[i[p]]
              BY <6>1 DEF TypeOK, CorrectTupleDomain
            <7> QED
              BY <7>1
          <6> QED
            BY <6>2, <6>3
        <5> QED
          BY <5>1, <5>2
        
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  Inv_W1'
        BY <4>3 DEF L02, TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  Inv_W1'
        BY <4>4 DEF L03
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  Inv_W1'
        <5> USE <4>5 DEF L04
        <5> SUFFICES ASSUME NEW q \in WProcSet,
                            pc'[q] \in 2..4,
                            NEW u \in M',
                            (u.state[i[q]] /= A[i[q]])'
                     PROVE  (u.res[q] = BOT)'
          BY DEF Inv_W1
        <5>1. PICK t \in M : u = [state |-> t.state,
                                  res   |-> [t.res EXCEPT ![p] = BOT]]
          OBVIOUS
        <5> QED
          BY <5>1
        
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        <5> USE <4>11 DEF L10
        <5> SUFFICES ASSUME NEW p \in WProcSet,
                            (pc[p] \in 2..4)',
                            NEW u \in M',
                            (u.state[i[p]] /= A[i[p]])'
                     PROVE  (u.res[p] = BOT)'
          OBVIOUS
        <5>1. PICK t \in M : u = [state |-> t.state,
                                  res   |-> [t.res EXCEPT ![S] = BOT]]
          OBVIOUS
        <5> QED
          BY <5>1
        
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
            
    <3>4. InvC'
      <4> USE DEF InvC
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  InvC'
        BY <4>1 DEF L00, TypeOK
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  InvC'
        BY <4>2 DEF L01
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  InvC'
        BY <4>3 DEF L02, TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  InvC'
        BY <4>4 DEF L03
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  InvC'
        BY <4>5 DEF L04
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        BY <4>11 DEF L10
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
      
    <3>5. Inv_W4'
      <4> USE DEF Inv_W4
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  Inv_W4'
        BY <4>1 DEF L00, TypeOK
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  Inv_W4'
        <5> USE <4>2 DEF L01
        <5> SUFFICES ASSUME NEW k \in IndexSet,
                            \A q \in WProcSet : pc[q] = 0 \/ i[q] /= k,
                            NEW t \in M'
                     PROVE  t.state[k] = A'[k]
          BY DEF Inv_W4
        <5>1. CASE k /= i[p]
          BY <5>1 DEF TypeOK, CorrectTupleDomain
        <5>2. CASE k = i[p]
          BY <5>2
        <5> QED
          BY <5>1, <5>2
        
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  Inv_W4'
        BY <4>3 DEF L02, TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  Inv_W4'
        BY <4>4 DEF L03
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  Inv_W4'
        <5> USE <4>5 DEF L04
        <5> SUFFICES ASSUME NEW k \in IndexSet,
                            \A q \in WProcSet : pc'[q] = 0 \/ i'[q] /= k,
                            NEW u \in M'
                     PROVE  u.state[k] = A[k]
          OBVIOUS
        <5>1. CASE k /= i[p]
          BY <5>1
        <5>2. CASE k = i[p]
          <6> USE <5>2
          <6>1. PICK t \in M : /\ u = [state |-> t.state, res |-> [t.res EXCEPT ![p] = BOT]]
                               /\ t.res[p] = ACK
            OBVIOUS
          <6>2. t.state[k] = A[k]
            BY <6>1 DEF Inv_W1, TypeOK
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>2
        
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        BY <4>11 DEF L10
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
            
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF InvW
  <2>4. InvS'
    <3> USE DEF InvS
    <3>1. InvS_1'
      <4> USE DEF InvS_1
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  InvS_1'
        <5> USE <4>1 DEF L00
        <5>1. pc[S] = pc[S]'
          OBVIOUS
        <5>2. \A k \in IndexSet : D(k) = D(k)'
          BY <5>1 DEF D
        <5>3. AlphaDomain = AlphaDomain'
          BY <5>2 DEF AlphaDomain
        <5> QED
          BY <5>3
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  InvS_1'
        <5> USE <4>2 DEF L01
        <5> SUFFICES ASSUME pc[S]' \in 5..8,
                            NEW beta \in AlphaDomain'
                     PROVE  \E u \in M' : /\ u.state = beta
                                          /\ u.res[S] = BOT
          BY DEF InvS_1
        <5>1. pc[S] = pc[S]'
          OBVIOUS
        <5>2. CASE beta[i[p]] = A[i[p]]'
          <6> USE <5>2
          <6>1. PICK alpha \in AlphaDomain : \A k \in IndexSet : (k /= i[p]) => alpha[k] = beta[k]
            <7>1. \A k \in IndexSet : k /= i[p] => D(k) = D(k)'
              BY <5>1 DEF D 
            <7>2. PICK d \in D(i[p]) : d \in Nat
              BY DEF D, TypeOK
            <7>3. DEFINE alpha == [k \in IndexSet |-> IF k /= i[p] THEN beta[k] ELSE d]
            <7>4. \A k \in IndexSet : (k /= i[p]) => alpha[k] \in D(k)
              BY <7>1 DEF AlphaDomain
            <7>5. alpha[i[p]] \in D(i[p])
              BY <7>2 DEF TypeOK
            <7>6. alpha \in AlphaDomain
              BY <7>4, <7>5 DEF AlphaDomain
            <7> QED
              BY <7>6
          <6>2. PICK t \in M : /\ t.state = alpha
                               /\ t.res[S] = BOT
            BY <6>1
          <6>3. PICK u \in M' : u = [state |-> [t.state EXCEPT ![i[p]] = v[p]], 
                                     res   |-> [t.res   EXCEPT ![p]    = ACK]]
            BY <6>2
          <6>4. u.state = beta
            <7>1. \A k \in IndexSet : u.state[k] = beta[k]
              <8>1. \A k \in IndexSet : (k /= i[p]) => u.state[k] = beta[k]
                BY <6>1, <6>2, <6>3
              <8>2. beta[i[p]] = v[p]
                BY DEF TypeOK
              <8>3. u.state[i[p]] = v[p]
                BY <6>3 DEF TypeOK, CorrectTupleDomain
              <8> QED
                BY <8>1, <8>2, <8>3
            <7>2. beta \in [IndexSet -> Nat]
              <8>1. \A k \in IndexSet : D(k)' \in SUBSET Nat
                BY DEF D, TypeOK
              <8> QED
                BY <8>1 DEF AlphaDomain
            <7>3. u.state \in [IndexSet -> Nat]
              BY <6>3 DEF TypeOK, CorrectTupleDomain
            <7> QED
              BY <7>1, <7>2, <7>3
          <6>5. u.res[S] = BOT
            BY <6>2, <6>3
          <6> QED
            BY <6>3, <6>4, <6>5
        <5>3. CASE beta[i[p]] /= A[i[p]]'
          <6> USE <5>3
          <6>1. \A k \in IndexSet : k /= i[p] => D(k) = D(k)'
            BY <5>1 DEF D
          <6>2. beta[i[p]] \in D(i[p])'
            BY DEF AlphaDomain, TypeOK
          <6>3. beta[i[p]] \in D(i[p])
            BY <6>2 DEF D
          <6>4. beta \in AlphaDomain
            BY <6>1, <6>3 DEF AlphaDomain
          <6> QED
            BY <6>4
        <5> QED
          BY <5>2, <5>3
        
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  InvS_1'
        <5> USE <4>3 DEF L02
        <5>1. pc[S] = pc[S]'
          BY DEF TypeOK, IndexSet
        <5>2. \A k \in IndexSet : D(k) = D(k)'
          BY <5>1 DEF D
        <5>3. AlphaDomain = AlphaDomain'
          BY <5>2 DEF AlphaDomain
        <5> QED
          BY <5>3 DEF TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  InvS_1'
        <5> USE <4>4 DEF L03
        <5> SUFFICES ASSUME (pc[S] \in 5..8)',
                            NEW alpha \in AlphaDomain'
                     PROVE  \E t \in M' : /\ t.state = alpha
                                          /\ t.res[S] = BOT
          OBVIOUS
        <5>1. \A k \in IndexSet : k /= i[p] => D(k) = D(k)'
          BY DEF D
        <5>2. B'[i[p]] = A'[i[p]] /\ B'[i[p]] /= BOT
          BY DEF InvW, Inv_W3, TypeOK
        <5>3. D(i[p])' \in SUBSET D(i[p])
          BY <5>2 DEF D
        <5>4. alpha[i[p]] \in D(i[p])
          BY <5>3 DEF AlphaDomain, TypeOK, IndexSet
        <5>6. alpha \in AlphaDomain
          BY <5>1, <5>4 DEF AlphaDomain
        <5> QED
          BY <5>6
        
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  InvS_1'
        <5> USE <4>5 DEF L04
        <5> SUFFICES ASSUME pc'[S] \in 5..8,
                            NEW alpha \in AlphaDomain'
                     PROVE  \E u \in M' : /\ u.state = alpha
                                          /\ u.res[S] = BOT
          BY DEF InvS_1
        <5>1. \A k \in IndexSet : D(k) = D(k)'
          BY DEF D, TypeOK
        <5>2. AlphaDomain = AlphaDomain'
          BY <5>1 DEF AlphaDomain
        <5>3. PICK t_1 \in M : /\ t_1.state = alpha
                               /\ t_1.res[S] = BOT
          BY <5>2
        <5>4. PICK t \in M : /\ t.state = [t_1.state EXCEPT ![i[p]] = A[i[p]]]
                             /\ t.res = [t_1.res EXCEPT ![p] = ACK]
          BY DEF InvW, Inv_W2
        <5>5. t_1.state[i[p]] = A[i[p]]
          <6>1. alpha[i[p]] \in D(i[p])
            BY <5>1, <5>3 DEF AlphaDomain, TypeOK
          <6>2. CASE /\ B[i[p]] = BOT
                     /\ (\/ pc[S] = 8 
                         \/ (pc[S] = 7 /\ i[p] < j))
                     
            <7> USE <6>2
            <7>1. alpha[i[p]] \in {A[i[p]], a[i[p]]}
              BY <6>1 DEF D
            <7>2. A[i[p]] = a[i[p]]
              BY DEF InvS, InvS_4, TypeOK
            <7> QED
              BY <5>3, <7>1, <7>2
          <6>3. CASE /\ B[i[p]] /= BOT
                     /\ (\/ pc[S] \in 7..8 
                         \/ (pc[S] = 6 /\ i[p] < j))
            <7> USE <6>3
            <7>1. alpha[i[p]] \in {A[i[p]], B[i[p]]}
              BY <6>1 DEF D
            <7>2. A[i[p]] = B[i[p]]
              BY DEF InvS, InvS_5, TypeOK
            <7> QED
              BY <5>3, <7>1, <7>2
          <6>4. CASE \/ pc[S] = 5
                     \/ (pc[S] = 6 /\ (B[i[p]] = BOT \/ i[p] >= j))
                     \/ (pc[S] = 7 /\ i[p] >= j /\ B[i[p]] = BOT)
            <7> USE <6>4
            <7>1. alpha[i[p]] \in {A[i[p]]}
              BY <6>1 DEF D, TypeOK, IndexSet
            <7> QED
              BY <5>3, <7>1
          <6> QED
            BY <6>2, <6>3, <6>4 DEF TypeOK, IndexSet
        <5>6. t_1.state = t.state
          BY <5>4, <5>5 DEF TypeOK, CorrectTupleDomain
        <5>7. /\ t.res[p] = ACK
              /\ t.res[S] = BOT
          BY <5>3, <5>4 DEF TypeOK, CorrectTupleDomain
        <5>8. PICK u \in M' : u = [state |-> t.state, res |-> [t.res EXCEPT ![p] = BOT]]
          BY <5>4, <5>7
        <5>9. /\ u.state = alpha
              /\ u.res[S] = BOT
          BY <5>3, <5>6, <5>7, <5>8
        <5> QED
          BY <5>8, <5>9
      <4>6. CASE L05
        <5> USE <4>6 DEF L05, IndexSet
        <5>1. \A k \in IndexSet : k >= j'
          OBVIOUS
        <5>2. \A k \in IndexSet : D(k)' = {A[k]}
          BY <5>1 DEF D
        <5>3. \A k \in IndexSet : D(k) = D(k)'
          BY <5>2 DEF D
        <5>4. AlphaDomain = AlphaDomain'
          BY <5>3 DEF AlphaDomain
        <5> QED
          BY <5>4

      <4>7. CASE L06
        <5> USE <4>7 DEF L06
        <5>1. CASE j < N_COMPS
          <6> USE <5>1
          <6>1. \A k \in IndexSet : D(k) = D(k)'
            <7> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  D(k) = D(k)'
              OBVIOUS
            <7>1. A'[k] = A[k]
              OBVIOUS
            <7>2. B' = [B EXCEPT ![j] = BOT]
              OBVIOUS
            <7>3. CASE k /= j
              <8> USE <7>3
              <8>1. B'[k] = B[k]
                BY <7>2
              <8>2. (k < j) = (k < j')
                BY DEF IndexSet, TypeOK
              <8> QED
                BY <8>1, <8>2, <7>1 DEF D
            <7>4. CASE k = j
              <8> USE <7>4
              <8>1. B'[k] = BOT
                BY <7>2 DEF TypeOK
              <8>2. D(k)' = {A[k]}
                BY <7>1, <8>1 DEF D
              <8>3. D(k) = {A[k]}
                BY DEF D, TypeOK
              <8> QED
                BY <8>2, <8>3
            <7> QED
              BY <7>3, <7>4
          <6>2. AlphaDomain = AlphaDomain'
            BY <6>1 DEF AlphaDomain
          <6> QED
            BY <6>2
        <5>2. CASE j = N_COMPS
          <6> USE <5>2 DEF IndexSet
          <6>1. \A k \in IndexSet : D(k) = D(k)'
            <7> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  D(k) = D(k)'
              OBVIOUS
            <7>1. D(k) = CASE (B[k] /= BOT) -> {A[k], B[k]}
                           [] OTHER         -> {A[k]}
              BY DEF D
            <7>3. D(k)' = CASE (B'[k] /= BOT) -> {A'[k], B'[k]}
                            [] OTHER          -> {A'[k]}
              BY DEF D, TypeOK
            <7>5. B = B'
              OBVIOUS
            <7>6. D(k) = D(k)'
              BY <7>1, <7>3, <7>5
            <7> QED
              BY <7>6
          <6>2. AlphaDomain = AlphaDomain'
            BY <6>1 DEF AlphaDomain
          <6> QED
            BY <6>2
        <5> QED
          BY <5>1, <5>2 DEF TypeOK
        
      <4>8. CASE L07
        <5> USE <4>8 DEF L07
        <5>1. CASE j < N_COMPS
          <6> USE <5>1
          <6>1. \A k \in IndexSet : D(k) = D(k)'
            <7> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  D(k) = D(k)'
              OBVIOUS
            <7>1. A'[k] = A[k]
              OBVIOUS
            <7>2. a' = [a EXCEPT ![j] = A[j]]
              OBVIOUS
            <7>3. CASE k /= j
              <8> USE <7>3
              <8>1. (k < j) = (k < j')
                BY DEF IndexSet, TypeOK
              <8>2. a'[k] = a[k]
                BY <7>2
              <8> QED
                BY <7>1, <8>1, <8>2 DEF D
            <7>4. CASE k = j
              <8> USE <7>4
              <8>1. CASE B[k] = BOT
                <9> USE <8>1
                <9>1. a'[k] = A[k]
                  BY <7>2 DEF TypeOK
                <9>2. D(k)' = {A'[k]}
                  BY <9>1 DEF D
                <9>3. D(k) = {A[k]}
                  BY DEF D, TypeOK
                <9> QED
                  BY <7>1, <9>2, <9>3 DEF D
              <8>2. CASE B[k] /= BOT
                BY <8>2 DEF D
              <8> QED
                BY <8>1, <8>2
            <7> QED
              BY <7>3, <7>4
          <6>2. AlphaDomain = AlphaDomain'
            BY <6>1 DEF AlphaDomain
          <6> QED
            BY <6>2
        <5>2. CASE j = N_COMPS
          <6> USE <5>2 DEF IndexSet
          <6>1. \A k \in IndexSet : D(k) = D(k)'
            <7> SUFFICES ASSUME NEW k \in IndexSet
                         PROVE  D(k) = D(k)'
              OBVIOUS
            <7>1. D(k) = CASE (B[k] /= BOT) -> {A[k], B[k]}
                           [] OTHER         -> {A[k], a[k]}
              BY DEF D
            <7>2. D(k)' = CASE (B'[k] /= BOT) -> {A'[k], B'[k]}
                            [] OTHER          -> {A'[k], a'[k]}
              BY DEF D, TypeOK
            <7>3. a = a'
              OBVIOUS
            <7> QED
              BY <7>1, <7>2, <7>3
          <6>2. AlphaDomain = AlphaDomain'
            BY <6>1 DEF AlphaDomain
          <6> QED
            BY <6>2
        <5> QED
          BY <5>1, <5>2 DEF TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08, TypeOK
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        <5> USE <4>11 DEF L10
        <5> SUFFICES ASSUME pc'[S] \in 5..8,
                            NEW alpha \in AlphaDomain'
                     PROVE  \E t \in M' : /\ t.state = alpha
                                          /\ t.res[S] = BOT
          BY DEF InvS_1
        <5>1. \A k \in IndexSet : D(k) = {a[k]}
          BY DEF D
        <5>2. a \in AlphaDomain
          BY <5>1 DEF AlphaDomain, TypeOK, IndexSet
        <5>3. PICK t \in M : /\ t.state = A
                             /\ t.res[S] = a
          BY <5>2 DEF InvS_2
        <5>4. t \in {u \in M : u.res[S] = a}
          BY <5>3
        <5>5. PICK u \in M' : u = [state |-> t.state, res |-> [t.res EXCEPT ![S] = BOT]]
          BY <5>3, <5>4
        <5>6. u.state = A'
          BY <5>3, <5>5
        <5>7. u.res[S] = BOT
          BY <5>5 DEF TypeOK, CorrectTupleDomain
        <5>8. alpha = A'
          <6>1. \A k \in IndexSet : D(k)' = {A'[k]}
            BY DEF D, TypeOK 
          <6> QED
            BY <6>1 DEF AlphaDomain, TypeOK
        <5> QED
          BY <5>5, <5>6, <5>7, <5>8
          
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars, AlphaDomain, D
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
      
    <3>2. InvS_2'
      <4> USE DEF InvS_2
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  InvS_2'
        <5> USE <4>1 DEF L00
        <5>1. pc[S] = pc[S]'
          OBVIOUS
        <5>2. \A k \in IndexSet : D(k) = D(k)'
          BY <5>1 DEF D
        <5>3. AlphaDomain = AlphaDomain'
          BY <5>2 DEF AlphaDomain
        <5> QED
          BY <5>3
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  InvS_2'
        <5> USE <4>2 DEF L01
        <5> SUFFICES ASSUME pc'[S] \in 9..10,
                            NEW alpha \in AlphaDomain'
                     PROVE  \E u \in M' : /\ u.state = A'
                                          /\ u.res[S] = alpha
          OBVIOUS
        <5>1. \A k \in IndexSet : k /= i[p] => D(k) = D(k)'
          BY DEF TypeOK, D
        <5>2. D(i[p]) = D(i[p])'
          BY DEF TypeOK, D
        <5>3. \A k \in IndexSet : D(k) = D(k)'
          BY <5>1, <5>2
        <5>4. AlphaDomain = AlphaDomain'
          BY <5>3 DEF AlphaDomain
        <5>5. PICK t \in M : /\ t.state = A
                             /\ t.res[S] = alpha
          BY <5>4
        <5>6. PICK u \in M' : u = [state |-> [t.state EXCEPT ![i[p]] = v[p]],
                                   res   |-> [t.res   EXCEPT ![p]    = ACK]]
          OBVIOUS
        <5>7. /\ u.state = A'
              /\ u.res[S] = alpha
          BY <5>5, <5>6
        <5> QED
          BY <5>6, <5>7
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  InvS_2'
        <5> USE <4>3 DEF L02
        <5>1. pc[S] = pc[S]'
          BY DEF TypeOK, IndexSet
        <5>2. \A k \in IndexSet : D(k) = D(k)'
          BY <5>1 DEF D
        <5>3. AlphaDomain = AlphaDomain'
          BY <5>2 DEF AlphaDomain
        <5> QED
          BY <5>3 DEF TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  InvS_2'
        <5> USE <4>4 DEF L03
        <5> SUFFICES ASSUME pc'[S] \in 9..10,
                            NEW alpha \in AlphaDomain'
                     PROVE  \E t \in M' : /\ t.state = A
                                          /\ t.res[S] = alpha
          OBVIOUS
        <5>1. \A k \in IndexSet : k /= i[p] => D(k) = D(k)'
          BY DEF D
        <5>2. B'[i[p]] = A'[i[p]] /\ B'[i[p]] /= BOT
          BY DEF InvW, Inv_W3, TypeOK
        <5>3. D(i[p])' \in SUBSET D(i[p])
          BY <5>2 DEF D
        <5>4. alpha[i[p]] \in D(i[p])
          BY <5>3 DEF AlphaDomain, TypeOK, IndexSet
        <5>6. alpha \in AlphaDomain
          BY <5>1, <5>4 DEF AlphaDomain
        <5> QED
          BY <5>6
        
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  InvS_2'
        <5> USE <4>5 DEF L04
        <5> SUFFICES ASSUME pc'[S] \in 9..10,
                            NEW alpha \in AlphaDomain'
                     PROVE  \E u \in M' : /\ u.state = A
                                          /\ u.res[S] = alpha
          OBVIOUS
        <5>1. \A k \in IndexSet : D(k)' = D(k)
          BY DEF D
        <5>2. AlphaDomain = AlphaDomain'
          BY <5>1 DEF AlphaDomain
        <5>3. PICK t_1 \in M : /\ t_1.state = A
                               /\ t_1.res[S] = alpha
          BY <5>2
        <5>4. pc[p] \in 2..4
          OBVIOUS
        <5>5. PICK t \in M : /\ t.state = [t_1.state EXCEPT ![i[p]] = A[i[p]]]
                             /\ t.res = [t_1.res EXCEPT ![p] = ACK]
          BY <5>4 DEF InvW, Inv_W2
        <5>6. /\ t.res[p] = ACK
              /\ t.state = A
              /\ t.res[S] = alpha
          BY <5>3, <5>5 DEF TypeOK, CorrectTupleDomain
        <5>7. PICK u \in M' : u = [state |-> t.state,
                                   res   |-> [t.res EXCEPT ![p] = BOT]]
          BY <5>5, <5>6
        <5>8. /\ u.state = A
              /\ u.res[S] = alpha
          BY <5>6, <5>7
        <5> QED
          BY <5>7, <5>8
        
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        <5> USE <4>9 DEF L08
        <5> SUFFICES ASSUME pc'[S] \in 9..10,
                            NEW alpha \in AlphaDomain'
                     PROVE  \E u \in M' : /\ u.state = A
                                          /\ u.res[S] = alpha
          OBVIOUS
        <5>1. \A k \in IndexSet : D(k)' \in SUBSET D(k)
          BY DEF D, TypeOK, IndexSet
        <5>2. AlphaDomain' \in SUBSET AlphaDomain
          BY <5>1 DEF AlphaDomain
        <5>3. PICK t \in M : /\ t.state = alpha
                             /\ t.res[S] = BOT
          BY <5>2 DEF InvS_1
        <5>4. PICK u \in M' : u = [state |-> A,
                                   res   |-> Merge([p \in WProcSet |-> IF pc[p] \in {0, 1} THEN BOT ELSE ACK],
                                                    Map(S, t.state))]
          BY <5>3
        <5>5. /\ u.state = A
              /\ u.res[S] = alpha
          BY <5>3, <5>4
        <5> QED
          BY <5>4, <5>5
        
      <4>10. CASE L09
        <5> USE <4>10 DEF L09
        <5>1. CASE j < N_COMPS
          <6> USE <5>1
          <6>1. \A k \in IndexSet : k /= j => D(k) = D(k)'
            <7> SUFFICES ASSUME NEW k \in IndexSet,
                                k /= j
                         PROVE  D(k) = D(k)'
              OBVIOUS
            <7>1. (k >= j) = (k >= j')
              BY DEF IndexSet, TypeOK
            <7>2. a'[k] = a[k]
              BY DEF TypeOK
            <7> QED
              BY <7>1, <7>2 DEF D
          <6>2. \A k \in IndexSet : k = j => D(k)' \in SUBSET D(k)
            <7> SUFFICES ASSUME NEW k \in IndexSet,
                                k = j
                         PROVE  D(k)' \in SUBSET D(k)
              OBVIOUS
            <7>1. CASE B[k] /= BOT
              <8> USE <7>1
              <8>1. a'[k] = B[k]
                BY DEF TypeOK, IndexSet
              <8>2. {B[k]} \in SUBSET D(k)
                BY DEF D, TypeOK
              <8>3. D(k)' = {a'[k]}
                BY DEF D, IndexSet, TypeOK
              <8> QED
                BY <8>1, <8>2, <8>3
            <7>2. CASE B[j] = BOT
              <8> USE <7>2
              <8>1. a'[k] = a[k]
                BY DEF TypeOK, IndexSet
              <8>2. {a[k]} \in SUBSET D(k)
                BY DEF D, TypeOK
              <8>3. D(k)' = {a'[k]}
                BY DEF D, IndexSet, TypeOK
              <8> QED
                BY <8>1, <8>2, <8>3
            <7> QED
              BY <7>1, <7>2
          <6>3. AlphaDomain' \in SUBSET AlphaDomain
            BY <6>1, <6>2 DEF AlphaDomain
          <6> QED
            BY <6>3
        <5>2. CASE j = N_COMPS
          <6> USE <5>2
          <6>1 \A k \in IndexSet : k < j
            BY DEF IndexSet
          <6>2. \A k \in IndexSet : D(k) = {a[k]}
            BY <6>1 DEF D, IndexSet
          <6>3. \A k \in IndexSet : D(k)' = {a[k]}
            BY DEF D, TypeOK
          <6>4. AlphaDomain = AlphaDomain'
            BY <6>2, <6>3 DEF AlphaDomain
          <6> QED
            BY <6>4
        <5> QED
          BY <5>1, <5>2 DEF TypeOK
          
      <4>11. CASE L10
        BY <4>11 DEF L10, TypeOK
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars, D, AlphaDomain
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
      
    <3>3. InvS_3'
      <4> USE DEF InvS_3
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  InvS_3'
        BY <4>1 DEF L00
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  InvS_3'
        BY <4>2 DEF L01
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  InvS_3'
        BY <4>3 DEF L02, TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  InvS_3'
        BY <4>4 DEF L03
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  InvS_3'
        BY <4>5 DEF L04
      <4>6. CASE L05
        BY <4>6 DEF L05, TypeOK
      <4>7. CASE L06
        BY <4>7 DEF L06, TypeOK
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08, TypeOK
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        BY <4>11 DEF L10, TypeOK
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
      
    <3>4. InvS_4'
      <4> USE DEF InvS_4
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  InvS_4'
        BY <4>1 DEF InvS_4, L00
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  InvS_4'
        BY <4>2 DEF InvS_4, L01, TypeOK
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  InvS_4'
        <5> USE <4>3 DEF L02
        <5>1. CASE X = TRUE
          BY <5>1 DEF TypeOK
        <5>2. CASE X = FALSE
          <6> USE <5>2
          <6>1. pc'[S] \in {5, 9, 10}
            BY DEF InvS, InvS_3, TypeOK
          <6> QED
            BY <6>1
        <5> QED
          BY <5>1, <5>2 DEF TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  InvS_4'
        BY <4>4 DEF L03, TypeOK
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  InvS_4'
        BY <4>5 DEF L04
      <4>6. CASE L05
        BY <4>6 DEF L05
      <4>7. CASE L06
        <5> USE <4>7 DEF L06
        <5>1. CASE j < N_COMPS
          BY <5>1 DEF TypeOK
        <5>2. CASE j = N_COMPS
          <6> USE <5>2
          <6>1. \A k \in IndexSet : (pc'[S] = 8 \/ k < j') = FALSE
            BY DEF TypeOK, IndexSet
          <6> QED
            BY <6>1
        <5> QED
          BY <5>1, <5>2 DEF TypeOK
      <4>8. CASE L07
        <5> USE <4>8 DEF L07
        <5> SUFFICES ASSUME NEW k \in IndexSet,
                             /\ pc'[S] = 8 \/ (pc'[S] = 7 /\ k < j')
                             /\ B'[k] = BOT 
                             /\ (\A p \in WProcSet : i[p] = k => pc[p] \in {0, 1, 4})
                     PROVE A'[k] = a'[k]
          BY DEF TypeOK
        <5>1. CASE k < j
          <6> USE <5>1
          <6>1. a'[k] = a[k]
            BY DEF TypeOK
          <6> QED
            BY <6>1
        <5>2. CASE k = j
          <6> USE <5>2
          <6>1. j < N_COMPS
            BY DEF IndexSet
          <6>2. a'[k] = A[k]
            BY <6>1 DEF TypeOK
          <6> QED
            BY <6>2
        <5> QED
          BY <5>1, <5>2 DEF TypeOK, IndexSet
        
      <4>9. CASE L08
        BY <4>9 DEF TypeOK, L08
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        BY <4>11 DEF L10
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
          
    <3>5. InvS_5'
      <4> USE DEF InvS_5
      <4>1. ASSUME NEW p \in WProcSet,
                   L00(p)
            PROVE  InvS_5'
        BY <4>1 DEF L00
      <4>2. ASSUME NEW p \in WProcSet,
                   L01(p)
            PROVE  InvS_5'
        BY <4>2 DEF L01, TypeOK
      <4>3. ASSUME NEW p \in WProcSet,
                   L02(p)
            PROVE  InvS_5'
        <5> USE <4>3 DEF L02
        <5>1. CASE X = TRUE
          BY <5>1 DEF TypeOK
        <5>2. CASE X = FALSE
          <6> USE <5>2
          <6>1. pc'[S] \in {5, 9, 10}
            BY DEF InvS, InvS_3, TypeOK
          <6> QED
            BY <6>1
        <5> QED
          BY <5>1, <5>2 DEF TypeOK
      <4>4. ASSUME NEW p \in WProcSet,
                   L03(p)
            PROVE  InvS_5'
        BY <4>4 DEF L03, TypeOK, InvW, Inv_W3
      <4>5. ASSUME NEW p \in WProcSet,
                   L04(p)
            PROVE  InvS_5'
        BY <4>5 DEF L04
      <4>6. CASE L05
        <5> USE <4>6 DEF L05
        <5>1. \A k \in IndexSet : pc'[S] = 6 /\ ((k < j') = FALSE)
          BY DEF TypeOK, IndexSet
        <5> QED
          BY <5>1
      <4>7. CASE L06
        <5> USE <4>7 DEF L06
        <5> SUFFICES ASSUME NEW k \in IndexSet,
                             /\ (pc'[S] \in 7..8 \/ (pc'[S] = 6 /\ k < j')) 
                             /\ B'[k] /= BOT
                             /\ (\A p \in WProcSet : i[p] = k => pc[p] \in {0, 1, 4})
                     PROVE  A'[k] = B'[k]
          BY DEF TypeOK
        <5>1. CASE k < j
          <6> USE <5>1
          <6>1. B'[k] = B[k]
            BY DEF TypeOK
          <6> QED
            BY <6>1
        <5>2. CASE k = j
          <6> USE <5>2
          <6>1. j < N_COMPS
            BY DEF IndexSet
          <6>2. B'[k] = BOT
            BY <6>1 DEF TypeOK
          <6> QED
            BY <6>2
        <5> QED
          BY <5>1, <5>2 DEF TypeOK, IndexSet
        
        
      <4>8. CASE L07
        BY <4>8 DEF L07, TypeOK
      <4>9. CASE L08
        BY <4>9 DEF L08, TypeOK
      <4>10. CASE L09
        BY <4>10 DEF L09, TypeOK
      <4>11. CASE L10
        BY <4>11 DEF L10
      <4>12. CASE UNCHANGED vars
        BY <4>12 DEF vars
      <4>13. QED
        BY <4>1, <4>10, <4>11, <4>12, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Next
      
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF InvS
    
  <2>5. Inv00'
    <3> USE DEF Inv00
    <3>1. ASSUME NEW p \in WProcSet,
                 L00(p)
          PROVE  Inv00'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in WProcSet,
                 L01(p)
          PROVE  Inv00'
      <4> USE <3>2 DEF L01
      <4> SUFFICES ASSUME NEW q \in WProcSet',
                          pc[q] = 0,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        OBVIOUS
      <4>1. CASE u \in M
        BY <4>1
      <4>2. CASE u \notin M
        <5> USE <4>2
        <5>1.  PICK t \in M : u = [state |-> [t.state EXCEPT ![i[p]] = v[p]], 
                                   res   |-> [t.res   EXCEPT ![p]    = ACK]]
          OBVIOUS
        <5> QED
          BY <5>1
      <4> QED
        BY <4>1, <4>2
      
    <3>3. ASSUME NEW p \in WProcSet,
                 L02(p)
          PROVE  Inv00'
      BY <3>3 DEF L02, TypeOK
    <3>4. ASSUME NEW p \in WProcSet,
                 L03(p)
          PROVE  Inv00'
      BY <3>4 DEF L03
    <3>5. ASSUME NEW p \in WProcSet,
                 L04(p)
          PROVE  Inv00'
      <4> USE <3>5 DEF L04
      <4> SUFFICES ASSUME NEW q \in WProcSet',
                          pc'[q] = 0,
                          NEW u \in M'
                   PROVE  u.res[q] = BOT
        OBVIOUS
      <4>1. PICK t \in M : u = [state |-> t.state,
                                res   |-> [t.res EXCEPT ![p] = BOT]]
        OBVIOUS
      <4>2. CASE q /= p
        BY <4>1, <4>2
      <4>3. CASE q = p
        BY <4>1, <4>3 DEF TypeOK, CorrectTupleDomain
      <4> QED
        BY <4>2, <4>3
    <3>6. CASE L05
      BY <3>6 DEF L05, TypeOK
    <3>7. CASE L06
      BY <3>7 DEF L06, TypeOK
    <3>8. CASE L07
      BY <3>8 DEF L07, TypeOK
    <3>9. CASE L08
      BY <3>9 DEF L08
    <3>10. CASE L09
      BY <3>10 DEF L09, TypeOK
    <3>11. CASE L10
      <4> USE <3>11 DEF L10
      <4> SUFFICES ASSUME NEW p \in WProcSet,
                          pc[p] = 0,
                          NEW u \in M'
                   PROVE  u.res[p] = BOT
        OBVIOUS
      <4>1. PICK t \in M : u = [state |-> t.state,
                                res   |-> [t.res EXCEPT ![S] = BOT]]
        OBVIOUS
      <4> QED
        BY <4>1
      
    <3>12. CASE UNCHANGED vars
      BY <3>12 DEF vars
    <3>13. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>6. Inv01'
    <3> USE DEF Inv01
    <3>1. ASSUME NEW p \in WProcSet,
                 L00(p)
          PROVE  Inv01'
      <4> USE <3>1 DEF L00
      <4> SUFFICES ASSUME NEW q \in WProcSet',
                          pc'[q] = 1,
                          NEW t \in M
                   PROVE  /\ t.state[i'[q]] = A[i'[q]]
                          /\ t.res[q] = BOT
        OBVIOUS
      <4>1. CASE q /= p
        BY <4>1
      <4>2. CASE q = p
        <5> USE <4>2
        <5>1. t.state[i'[q]] = A[i'[q]]
          BY DEF InvW, Inv_W4, TypeOK
        <5>2. t.res[q] = BOT
          BY DEF Inv00
        <5> QED
          BY <5>1, <5>2
      <4> QED
        BY <4>1, <4>2
    <3>2. ASSUME NEW p \in WProcSet,
                 L01(p)
          PROVE  Inv01'
      BY <3>2 DEF L01, TypeOK, CorrectTupleDomain
    <3>3. ASSUME NEW p \in WProcSet,
                 L02(p)
          PROVE  Inv01'
      BY <3>3 DEF L02, TypeOK
    <3>4. ASSUME NEW p \in WProcSet,
                 L03(p)
          PROVE  Inv01'
      BY <3>4 DEF L03
    <3>5. ASSUME NEW p \in WProcSet,
                 L04(p)
          PROVE  Inv01'
      BY <3>5 DEF L04, TypeOK, CorrectTupleDomain
    <3>6. CASE L05
      BY <3>6 DEF L05
    <3>7. CASE L06
      BY <3>7 DEF L06, TypeOK
    <3>8. CASE L07
      BY <3>8 DEF L07, TypeOK
    <3>9. CASE L08
      BY <3>9 DEF L08
    <3>10. CASE L09
      BY <3>10 DEF L09, TypeOK
    <3>11. CASE L10
      BY <3>11 DEF L10, TypeOK, CorrectTupleDomain
    <3>12. CASE UNCHANGED vars
      BY <3>12 DEF vars
    <3>13. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
      
  <2>7. Inv05'
    <3> USE DEF Inv05
    <3>1. ASSUME NEW p \in WProcSet,
                 L00(p)
          PROVE  Inv05'
      BY <3>1 DEF L00
    <3>2. ASSUME NEW p \in WProcSet,
                 L01(p)
          PROVE  Inv05'
      BY <3>2 DEF L01, TypeOK, CorrectTupleDomain
    <3>3. ASSUME NEW p \in WProcSet,
                 L02(p)
          PROVE  Inv05'
      BY <3>3 DEF L02, TypeOK
    <3>4. ASSUME NEW p \in WProcSet,
                 L03(p)
          PROVE  Inv05'
      BY <3>4 DEF L03
    <3>5. ASSUME NEW p \in WProcSet,
                 L04(p)
          PROVE  Inv05'
      BY <3>5 DEF L04, TypeOK, CorrectTupleDomain
    <3>6. CASE L05
      BY <3>6 DEF L05
    <3>7. CASE L06
      BY <3>7 DEF L06, TypeOK
    <3>8. CASE L07
      BY <3>8 DEF L07, TypeOK
    <3>9. CASE L08
      BY <3>9 DEF L08
    <3>10. CASE L09
      BY <3>10 DEF L09, TypeOK
    <3>11. CASE L10
      BY <3>11 DEF L10, TypeOK, CorrectTupleDomain
    <3>12. CASE UNCHANGED vars
      BY <3>12 DEF vars
    <3>13. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>8. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Inv
  
<1> QED
 BY <1>1, <1>2

=========================================================================================
\* Modification History
\* Last modified Tue May 17 02:35:29 EDT 2022 by lizziehernandez
\* Created Wed Feb 16 17:04:23 EST 2022 by lizziehernandez
