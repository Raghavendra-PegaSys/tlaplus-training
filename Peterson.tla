------------------------------ MODULE Peterson ------------------------------
EXTENDS TLAPS

VARIABLES flag, turn, pc

vars == <<flag, turn, pc>>

Not(i) == IF i = 0 THEN 1 ELSE 0

Init == /\ flag = [i \in {0,1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in {0,1} |-> "a0"]
        
a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED <<flag, turn>>
            
a1(self) == /\ pc[self] = "a1"
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ turn' = turn
            
a2(self) == /\ pc[self] = "a2"
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ flag' = flag
            /\ turn' = Not(self)
            
a3a(self) == /\ pc[self] = "a3a"
            /\ (IF flag[Not(self)]
                    THEN /\ pc' = [pc EXCEPT ![self] = "a3b"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"])
            /\ UNCHANGED <<flag, turn>>

a3b(self) == /\ pc[self] = "a3b"
            /\ (IF turn = Not(self)
                THEN /\ pc' = [pc EXCEPT ![self] = "a3a"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "cs"])
            /\ UNCHANGED <<flag, turn>>
                        
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED <<flag, turn>>
            
a4(self) == /\ pc[self] = "a4"
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ turn' = turn            
            
proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ cs(self) \/ a4(self) \/ a3a(self) \/ a3b(self)

Next == \E self \in {0,1}: proc(self)

\* Properties are specified as a temporal property from the starting state
\* Here we are specifying the possible executions of the system
\* Any run whose first state satisfies Init, and every state and its next satisfies 
\* Next is a valid behaviour of the system.

Spec == Init /\ [][Next]_vars

MutualExclusion == (pc[0] # "cs") \/ (pc[1] # "cs")

TypeOK == 
    /\ flag  \in [{0,1} -> BOOLEAN]
    /\ pc \in [{0, 1} -> {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}]
    /\ turn \in {0,1}
    
I == \A i \in {0,1}:
    /\ (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i])
    /\ (pc[i] \in {"cs", "a4"}) => /\ ~(pc[Not(i)] \in {"cs","a4"})
                                 /\ (pc[Not(i)] \in {"a3a","a3b"} => turn = i) 

Inv == TypeOK /\ I

\* For any valid, MutualExclusion is satisfied in all states. 
THEOREM Spec => []MutualExclusion
<1>1 Init => Inv
    BY DEF Init, Inv, TypeOK, I
<1>2 Inv /\ [Next]_vars => Inv'
    <2>1 SUFFICES ASSUME Inv, Next
            PROVE Inv'
        BY DEF Inv, TypeOK, I, vars
    <2>2 TypeOK'
        BY <2>1 DEF Inv, Next, a0, a1, a2, a3a, a3b, cs, a4, proc, TypeOK, Not
    <2>3 I'
        <3>1 SUFFICES ASSUME NEW j \in {0,1}
                PROVE I!(j)'
            BY DEF I
        <3>2 PICK i \in {0,1} : proc(i)
            BY <2>1 DEF Next
        <3>3 CASE i = j
            BY <2>1, <3>2, <3>3 DEF Inv, I, TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
        <3>4 CASE i # j
            BY <2>1, <3>2, <3>4 DEF Inv, I, TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
        <3>5 QED
            BY <3>3, <3>4
    <2>4 QED          
        BY <2>2, <2>3 DEF TypeOK, I, Not, Inv
<1>3 Inv => MutualExclusion
    BY DEF Inv, MutualExclusion, TypeOK, I, Not
<1>4 QED
    \* Temporal reasoning is required to prove 
    \* []Inv => []MutualExclusion from Inv => MutualExclusion
    \* Init /\ [][Next]_vars => []Inv from Init /\ [Next]_vars => Inv
    BY <1>1, <1>2, <1>3, PTL DEF Spec, MutualExclusion, Inv, TypeOK, I, Init, Next, vars, Not

\* Liveness
Wait(i) == (pc[i] = "a3a") \/ (pc[i] = "a3b")
Blocked(i) == (flag[Not(i)] /\ turn = Not(i))
CS(i) == pc[i] = "cs"
FairSpec == Spec /\ WF_vars(proc(0)) /\ WF_vars(proc(1))
\*Success == (Wait(0) ~> CS(0)) /\ (Wait(1) ~> CS(1))
Success == (Wait(0) ~> CS(0))

LEMMA Invariance == Spec => []Inv

\* Liveness Theorem
THEOREM Liveness == FairSpec => Success
<1>1 []Inv /\ [][Next]_vars /\ WF_vars(proc(0)) => Success
\*    <2>1 SUFFICES [][Next]_vars /\ WF_vars(proc(0)) => ((Inv /\ Wait(0)) ~> CS(0))
    <2>1 SUFFICES ASSUME [][Next]_vars /\ WF_vars(proc(0))
                    PROVE (Inv /\ Wait(0)) ~> CS(0)
        BY PTL DEF Success
    <2>2 Inv /\ Wait(0) ~> (Wait(0) /\ ~Blocked(0) /\ ENABLED <<(a3a(0) /\ a3b(0))>>_vars)
        <3> QED
\*    <2>3 Wait(0) /\ ~Blocked(0) /\ <<(a3a(0) /\ a3b(0))>>_vars => CS(0)'
\*        BY DEF Inv, Wait, proc, TypeOK, I, CS, Not, a3a, a3b, vars
    <2>4 QED
        BY <2>2 DEF Inv, Wait, CS, Blocked, TypeOK, I
<1>2 QED   
    BY Invariance, <1>1 DEF FairSpec, Init, Spec, Success, Wait, CS, Next, proc, Inv, TypeOK, I, Not

=============================================================================
\* Modification History
\* Last modified Mon Sep 07 12:36:01 AEST 2020 by raghavendra
\* Created Mon Aug 31 12:09:32 AEST 2020 by raghavendra