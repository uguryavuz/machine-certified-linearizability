----------------------- MODULE QueueHW_Implementation -----------------------
EXTENDS Queue_Type, Integers
CONSTANT RemainderID
VARIABLES pc, A, L, l, j, v, arg, ret
algvars == <<A, L, l, j, v>>

\* Line 1 -- l <- F&I(L)
L1(p) == /\ pc[p] = "L1"
         /\ l' = [l EXCEPT ![p] = L]
         /\ L' = L+1
         /\ pc' = [pc EXCEPT ![p] = "L2"]
         /\ UNCHANGED <<A, j, v, arg, ret>>
         
\* Line 2 -- A[l] <- arg
L2(p) == /\ pc[p] = "L2"
         /\ A' = [A EXCEPT ![l[p]] = arg[p]]
         /\ pc' = [pc EXCEPT ![p] = "L3"]
         /\ UNCHANGED <<L, l, j, v, arg, ret>>
         
\* Line 3 -- return ack
L3(p) == /\ pc[p] = "L3"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, L, l, j, v, arg>>
         /\ ret' = [ret EXCEPT ![p] = ACK]
         
\* Line 4 -- l <- L
\*           j <- 1
L4(p) == /\ pc[p] = "L4"
         /\ l' = [l EXCEPT ![p] = L]
         /\ j' = [j EXCEPT ![p] = 0]
         /\ pc' = [pc EXCEPT ![p] = "L5"]
         /\ UNCHANGED <<A, L, v, arg, ret>>
         
\* Line 5 -- if j = l: goto L4
\*           v <- swap(A[j], BOT)
\*           if v # BOT: goto L6 (v on this line is A[j])
\*           else j <- j+1 & goto L5
L5(p) == /\ pc[p] = "L5"
         /\ CASE (j[p] = l[p]) 
                 -> /\ pc' = [pc EXCEPT ![p] = "L4"]
                    /\ UNCHANGED <<A, L, l, j, v, arg, ret>>
              [] (j[p] # l[p] /\ A[j[p]] = BOT)
                 -> /\ A' = [A EXCEPT ![j[p]] = BOT]
                    /\ v' = [v EXCEPT ![p] = A[j[p]]]
                    /\ j' = [j EXCEPT ![p] = j[p]+1]
                    /\ pc' = [pc EXCEPT ![p] = "L5"]
                    /\ UNCHANGED <<L, l, arg, ret>>
              [] (j[p] # l[p] /\ A[j[p]] # BOT) 
                 -> /\ A' = [A EXCEPT ![j[p]] = BOT]
                    /\ v' = [v EXCEPT ![p] = A[j[p]]]
                    /\ pc' = [pc EXCEPT ![p] = "L6"]
                    /\ UNCHANGED <<L, l, j, arg, ret>>

\* Originally:
\*         /\ IF j[p] = l[p]
\*               THEN /\ pc' = [pc EXCEPT ![p] = "L4"]
\*                    /\ UNCHANGED <<A, L, l, j, v, arg, ret>>
\*               ELSE /\ v' = [v EXCEPT ![p] = A[j[p]]]
\*                    /\ IF A[j[p]] # BOT
\*                          THEN /\ pc' = [pc EXCEPT ![p] = "L6"]
\*                               /\ UNCHANGED <<A, L, l, j, arg, ret>>
\*                          ELSE /\ pc' = [pc EXCEPT ![p] = "L5"]
\*                               /\ j' = [j EXCEPT ![p] = j[p]+1]
\*                               /\ UNCHANGED <<A, L, l, arg, ret>>

\* Line 6 -- return v
L6(p) == /\ pc[p] = "L6"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, L, l, j, v, arg>>
         /\ ret' = [ret EXCEPT ![p] = v[p]]
         
Init == /\ pc = [p \in ProcSet |-> RemainderID]
        /\ A = [i \in Nat |-> BOT]
        /\ L = 0
        /\ l \in [ProcSet -> Nat]
        /\ j \in [ProcSet -> Nat]
        /\ v \in [ProcSet -> EltDomain \union {BOT}]
        /\ arg \in [ProcSet -> EltDomain]
        /\ ret \in [ProcSet -> RetDomain]

InvocLineIDs == {"L1", "L4"}
OpToInvocLine(op) == CASE op = "ENQ" -> "L1"
                       [] op = "DEQ" -> "L4"

LineIDs == {RemainderID, "L1", "L2", "L3", "L4", "L5", "L6"}
IntLines(p) == {L1(p), L2(p), L4(p), L5(p)}
RetLines(p) == {L3(p), L6(p)}


=============================================================================
\* Modification History
\* Last modified Thu Jan 11 11:18:03 EST 2024 by uguryavuz
\* Created Tue Jan 09 17:05:56 EST 2024 by uguryavuz
