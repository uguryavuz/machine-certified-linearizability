------------------------ MODULE RWCAS_Implementation ------------------------
EXTENDS RW_Type
CONSTANT RemainderID
VARIABLES pc, X, x, arg, ret
algvars == <<X, x>>

\* Line 1 -- x_pi <- X
L1(p) == /\ pc[p] = "L1"
         /\ x' = [x EXCEPT ![p] = X]
         /\ pc' = [pc EXCEPT ![p] = "L2"]
         /\ UNCHANGED <<X, arg, ret>> 

\* Line 2 -- return x_pi
L2(p) == /\ pc[p] = "L2"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<X, x, arg>>
         /\ ret' = [ret EXCEPT ![p] = x[p]]

\* Line 3 -- x_pi <- X
L3(p) == /\ pc[p] = "L3"
         /\ x' = [x EXCEPT ![p] = X]
         /\ pc' = [pc EXCEPT ![p] = "L4"]
         /\ UNCHANGED <<X, arg, ret>>

\* Line 4 -- CAS(X, x_pi, v_pi)
L4(p) == /\ pc[p] = "L4"
         /\ IF X = x[p] 
               THEN X' = arg[p]
               ELSE X' = X
         /\ pc' = [pc EXCEPT ![p] = "L5"]
         /\ UNCHANGED <<x, arg, ret>>

\* Line 5 -- return ack
L5(p) == /\ pc[p] = "L5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<X, x, arg>>
         /\ ret' = [ret EXCEPT ![p] = ACK]

InitState == CHOOSE val \in StateDomain : TRUE

Init == /\ pc = [p \in ProcSet |-> RemainderID]
        /\ X = InitState
        /\ x \in [ProcSet -> StateDomain]
        /\ arg \in [ProcSet -> StateDomain]
        /\ ret \in [ProcSet -> RetDomain]

\* IdleLine(p) == L0(p)
InvocLineIDs == {"L1", "L3"}
OpToInvocLine(op) == CASE op = "R" -> "L1"
                       [] op = "W" -> "L3"
\*LineIDtoOp(Line) == CASE Line = "L1" -> "R"
\*                      [] Line = "L2" -> "R"
\*                      [] Line = "L3" -> "W"
\*                      [] Line = "L4" -> "W"
\*                      [] Line = "L5" -> "W"
\*                      [] OTHER       -> BOT
LineIDs == {RemainderID, "L1", "L2", "L3", "L4", "L5"}
IntLines(p) == {L1(p), L3(p), L4(p)}
RetLines(p) == {L2(p), L5(p)}


=============================================================================
\* Modification History
\* Last modified Mon Jan 08 20:36:33 EST 2024 by uguryavuz
\* Created Fri Jan 05 20:56:01 EST 2024 by uguryavuz
