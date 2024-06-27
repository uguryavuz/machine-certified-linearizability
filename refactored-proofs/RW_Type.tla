------------------------------ MODULE RW_Type -------------------------------
CONSTANTS ACK, BOT, ProcSet, StateDomain

OpNames == {"R", "W"}
OpDomain == {"R", "W", BOT}
ArgDomain == StateDomain \union {BOT}
RetDomain == StateDomain \union {ACK}
ResDomain == StateDomain \union {ACK, BOT}

ArgsOf(op) == CASE op = "R" -> {BOT}
                [] op = "W" -> StateDomain
                [] OTHER    -> {}

ConfigDomain == [state: StateDomain, 
                 op: [ProcSet -> OpDomain], 
                 arg: [ProcSet -> ArgDomain], 
                 res: [ProcSet -> ResDomain]]

Delta(C, p, D) == CASE (C.op[p] = "R" /\ C.arg[p] \in ArgsOf("R") /\ C.res[p] = BOT)
                       -> /\ D.state = C.state
                          /\ D.op    = C.op
                          /\ D.arg   = C.arg
                          /\ D.res   = [C.res EXCEPT ![p] = C.state]
                    [] (C.op[p] = "W" /\ C.arg[p] \in ArgsOf("W") /\ C.res[p] = BOT)
                       -> /\ D.state = C.arg[p]
                          /\ D.op    = C.op
                          /\ D.arg   = C.arg
                          /\ D.res   = [C.res EXCEPT ![p] = ACK]
                    [] OTHER -> FALSE

=============================================================================
\* Modification History
\* Last modified Mon Jan 08 20:33:09 EST 2024 by uguryavuz
\* Created Fri Jan 05 17:48:58 EST 2024 by uguryavuz

