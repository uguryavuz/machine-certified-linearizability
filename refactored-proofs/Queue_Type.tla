----------------------------- MODULE Queue_Type -----------------------------
EXTENDS Sequences
CONSTANTS ACK, BOT, ProcSet, EltDomain

OpNames == {"ENQ", "DEQ"}
OpDomain == {"ENQ", "DEQ", BOT}
StateDomain == Seq(EltDomain)
ArgDomain == EltDomain \union {BOT}
RetDomain == EltDomain \union {ACK}
ResDomain == EltDomain \union {ACK, BOT}

ArgsOf(op) == CASE op = "ENQ" -> EltDomain
                [] op = "DEQ" -> {BOT}
                [] OTHER      -> {}

ConfigDomain == [state: StateDomain, 
                 op: [ProcSet -> OpDomain], 
                 arg: [ProcSet -> ArgDomain], 
                 res: [ProcSet -> ResDomain]]
                 
Delta(C, p, D) == CASE (C.op[p] = "ENQ" /\ C.arg[p] \in ArgsOf("ENQ") /\ C.res[p] = BOT)
                       -> /\ D.state = Append(C.state, C.arg[p])
                          /\ D.op    = C.op
                          /\ D.arg   = C.arg
                          /\ D.res   = [C.res EXCEPT ![p] = ACK]
                    [] (C.state # << >> /\ C.op[p] = "DEQ" /\ C.arg[p] \in ArgsOf("DEQ") /\ C.res[p] = BOT)
                       -> /\ D.state = Tail(C.state)
                          /\ D.op    = C.op
                          /\ D.arg   = C.arg
                          /\ D.res   = [C.res EXCEPT ![p] = Head(C.state)]
                    [] OTHER -> FALSE

=============================================================================
\* Modification History
\* Last modified Tue Jan 09 16:53:45 EST 2024 by uguryavuz
\* Created Tue Jan 09 16:33:49 EST 2024 by uguryavuz
