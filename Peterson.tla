------------------------------ MODULE Peterson ------------------------------
EXTENDS TLAPS

VARIABLES flag, turn, pc

vars == <<flag, turn, pc>>

Not(i) == IF i = 0 THEN 1 ELSE 0

Init == /\ flag = [i \in {0,1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in {0,1} |-> "a1"]
        
a1(self) == /\ pc[self] = "a1"
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ turn' = turn
            
a2(self) == /\ pc[self] = "a2"
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ flag' = flag
            /\ turn' = Not(self)
            
\*a3a(self) == /\ pc[self] = "a3a"
\*            /\ (IF flag[Not(self)]
\*                    THEN /\ pc' = [pc EXCEPT ![self] = "a3b"]
\*                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"])
\*            /\ UNCHANGED <<flag, turn>>

a3a_cs(self) == 
    /\ pc[self] = "a3a"
    /\ ~flag[Not(self)]
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<flag, turn>>
    
a3a_a3b(self) == 
    /\ pc[self] = "a3a"
    /\ flag[Not(self)]
    /\ pc' = [pc EXCEPT ![self] = "a3b"]
    /\ UNCHANGED <<flag, turn>>
    
\*a3b(self) == /\ pc[self] = "a3b"
\*            /\ (IF turn = Not(self)
\*                THEN /\ pc' = [pc EXCEPT ![self] = "a3a"]
\*                ELSE /\ pc' = [pc EXCEPT ![self] = "cs"])
\*            /\ UNCHANGED <<flag, turn>>

a3b_cs(self) == 
    /\ pc[self] = "a3b"
    /\ turn = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<flag, turn>>
   
a3b_a3a(self) == 
    /\ pc[self] = "a3b"
    /\ turn = Not(self)
    /\ pc' = [pc EXCEPT ![self] = "a3a"]
    /\ UNCHANGED <<flag, turn>>
                     
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED <<flag, turn>>
            
a4(self) == /\ pc[self] = "a4"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ turn' = turn            
            
proc(self) == 
    \/ a1(self) 
    \/ a2(self) 
    \/ cs(self) 
    \/ a4(self) 
    \/ a3a_cs(self) 
    \/ a3a_a3b(self) 
    \/ a3b_cs(self)
    \/ a3b_a3a(self)

Next == \E self \in {0,1}: proc(self)

\* Properties are specified as a temporal property from the starting state
\* Here we are specifying the possible executions of the system
\* Any run whose first state satisfies Init, and every state and its next satisfies 
\* Next is a valid behaviour of the system.

Spec == Init /\ [][Next]_vars

MutualExclusion == (pc[0] # "cs") \/ (pc[1] # "cs")

TypeOK == 
    /\ flag  \in [{0,1} -> BOOLEAN]
    /\ pc \in [{0, 1} -> {"a1", "a2", "a3a", "a3b", "cs", "a4"}]
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
        BY <2>1 DEF Inv, Next, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, proc, TypeOK, Not
    <2>3 I'
        <3>1 SUFFICES ASSUME NEW j \in {0,1}
                PROVE I!(j)'
            BY DEF I
        <3>2 PICK i \in {0,1} : proc(i)
            BY <2>1 DEF Next
        <3>3 CASE i = j
            BY <2>1, <3>2, <3>3 DEF Inv, I, TypeOK, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
        <3>4 CASE i # j
            BY <2>1, <3>2, <3>4 DEF Inv, I, TypeOK, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
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
CS(i) == pc[i] = "cs"
A(i) == a3a_cs(i) \/ a3b_cs(i)
WillEnterCSNext(i) == 
    /\ (pc[i] = "a3a" => ~flag[Not(i)])
    /\ (pc[i] = "a3b" => turn = i)     

LEMMA Invariance == Spec => []Inv

\* ENABLED action required here is A(0)
P1 == Inv /\ Wait(0) /\ WillEnterCSNext(0) /\ ~(pc[1] = "a1")

LEMMA L1P1 == [Next]_vars /\ P1 => P1' \/ CS(0)'
    <1>1 Next /\ P1 => P1' \/ CS(0)'
        <2>1 proc(0) /\ P1 => CS(0)'
            BY DEF P1, CS, Wait, WillEnterCSNext, Inv, TypeOK, I, a3a_cs, a3b_cs, Not, proc, a1, a2, a3a_a3b, a3b_a3a, a4, cs
        <2>2 proc(1) /\ P1 => P1'
            BY DEF proc, P1, Inv, TypeOK, I, Not, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, a4, cs, Wait, WillEnterCSNext
        <2>3 QED
            BY <2>1, <2>2 DEF Next 
    <1>2 vars' = vars /\ P1 => P1'
        BY DEF P1, Wait, WillEnterCSNext, Inv, TypeOK, I, vars
    <1>6 QED
        BY <1>1, <1>2

LEMMA L2P1 == <<Next /\ proc(0)>>_vars /\ P1 => CS(0)'
    <1>1 SUFFICES <<(a3a_cs(0) \/ a3b_cs(0))>>_vars /\ P1 => CS(0)'
        BY DEF a3a_cs, a3b_cs, Next, proc, Not, P1, Wait, WillEnterCSNext, CS, Inv, TypeOK, I, a1, a2, a3a_a3b, a3b_a3a, cs, a4
    <1>2 pc[0] = "a3a" /\ a3a_cs(0) /\ P1 => CS(0)'
        BY DEF a3a_cs, CS, P1, Wait, WillEnterCSNext, Not, Inv, TypeOK, I
    <1>3 pc[0] = "a3b" /\ a3b_cs(0) /\ P1 => CS(0)'
        BY DEF a3b_cs, CS, P1, Wait, WillEnterCSNext, Not, Inv, TypeOK, I
    <1>6 QED 
        BY <1>2, <1>3 DEF P1, Wait, WillEnterCSNext, Inv, TypeOK, I, a3a_cs, a3b_cs
    
LEMMA L3P1 == P1 => ENABLED <<proc(0)>>_vars
    <1>1 SUFFICES P1 => ENABLED <<a3a_cs(0) \/ a3b_cs(0)>>_vars
        BY DEF proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, a4, cs, Not, vars
    <1>6 QED
    
LEMMA LP1 == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P1 ~> CS(0)
    BY L1P1, L2P1, L3P1, PTL

P2 == Inv /\ Wait(0) /\ WillEnterCSNext(0) /\ pc[1] = "a1"
P2a == Inv /\ Wait(0) /\ pc[1] = "a2"
P2b == Inv /\ Wait(0) /\ pc[1] = "a3a" /\ turn = 0
P2c == Inv /\ pc[0] = "a3b" /\ turn = 0 /\ Wait(1)

\* ENABLED action required here is a1(1)
\*LEMMA M1 == [Next]_vars /\ P2 => P2' \/ CS(0)'
\*    <1>1 Next /\ P2 => P2' \/ P2a'
\*        <2>1 proc(1) /\ P2 => P2a'
\*            BY DEF proc, P2, a1, P2a, Inv, TypeOK, I, Wait, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
\*        <2>2 proc(0) /\ P2 => P2a'
\*        <2>6 QED
\*    <1>2 vars' = vars /\ P2 => P2'
\*        BY DEF vars, P2, Inv, Wait, WillEnterCSNext, TypeOK, I, vars        
\*    <1>6 QED
\*        BY <1>1, <1>2
        
\* ENABLED action required here is a1(1)
LEMMA L1P2 == [Next]_vars /\ P2 => P2' \/ P2a' \/ CS(0)'
    <1>1 Next /\ P2 => P2a' \/ CS(0)'
        <2>1 proc(1) /\ P2 => P2a'
            BY DEF proc, P2, a1, P2a, Inv, TypeOK, I, Wait, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
        <2>2 proc(0) /\ P2 => CS(0)'
            BY DEF proc, P2, a3a_cs, a3b_cs, CS, Wait, WillEnterCSNext, Inv, TypeOK, I, a1, a2, a3a_a3b, a3b_a3a, a4, cs, Not
        <2>6 QED
            BY <2>1, <2>2 DEF CS, Next
    <1>2 vars' = vars /\ P2 => P2'
        BY DEF vars, P2, Inv, Wait, WillEnterCSNext, TypeOK, I, vars        
    <1>6 QED
        BY <1>1, <1>2
        
LEMMA L2P2 == <<Next /\ proc(0) /\ proc(1)>>_vars /\ P2 => P2a' \/ CS(0)'
LEMMA L3P2 == P2 => ENABLED <<proc(0)>>_vars 
LEMMA L4P2 == P2 => ENABLED <<proc(1)>>_vars 

LEMMA M1 == [][proc(0)]_vars /\ WF_vars(proc(0)) => P2 ~> CS(0)
LEMMA M2 == [][proc(1)]_vars /\ WF_vars(proc(1)) => P2 ~> P2a

LEMMA LP2 == [][proc(0) \/ proc(1)]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P2 ~> (P2a \/ CS(0))
\*    BY L1P2, L2P2, L3P2, L4P2, PTL
    BY M1, M2, PTL DEF Next 

\* ENABLED action required here is a2(1)
LEMMA L1P2a == [Next]_vars /\ P2a => P2a' \/ P2b'
LEMMA L2P2a == <<Next>>_vars /\ P2a => P2b'
LEMMA L3P2a == P2a => ENABLED <<Next>>_vars
LEMMA LP2a == [][Next]_vars /\ WF_vars(Next) => P2a ~> P2b
BY L1P2a, L2P2a, L3P2a, PTL DEF Next, proc

LEMMA LP2c1 == [][Next]_vars /\ WF_vars(a3b_cs(0)) => (pc[0] = "a3b" /\ P2b) ~> P2c
LEMMA LP2c2 == [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => P2c ~> CS(0)

\* Case pc[0] = a3b. Then P2b ~> P2c ~> CS(0)
LEMMA LP2c == [][Next]_vars /\ WF_vars(a3b_cs(0)) => (pc[0] = "a3b" /\ P2b) ~> CS(0)
    BY LP2c1, LP2c2, PTL

\* Case pc[0] = a3a /\ flag[1]. Then P2b ~> P2c
LEMMA LP2c3 == [][Next]_vars /\ WF_vars(a3b_cs(0)) => (pc[0] = "a3a" /\ flag[1] /\ P2b) ~> P2c

\* Case pc[0] = a3a /\ ~flag[1]. Then P2b ~> CS(0). This is the same as LP1.
LEMMA P1a == (pc[0] = "a3a") /\ ~flag[1] /\ P2b => P1
    BY DEF P1, P2b, WillEnterCSNext, Not

LEMMA LP2b == [][Next]_vars /\ WF_vars(Next) => P2b ~> CS(0)
    \* Case pc[0] = a3a /\ ~flag[1]. Then P2b ~> CS(0). This is the same as LP1.
    <1>1 [][Next]_vars /\ WF_vars(Next) => pc[0] = "a3a" /\ ~flag[1] /\ P2b ~> CS(0)
        BY P1a, LP1 DEF P1, WillEnterCSNext, Not, P2b
    \* Case pc[0] = a3a /\ flag[1]. Then P2b ~> P2c
    <1>2 [][Next]_vars /\ WF_vars(Next) => pc[0] = "a3a" /\ flag[1] /\ P2b ~> P2c
        <2>6 QED
    <1>3 [][Next]_vars /\ WF_vars(Next) => pc[0] = "a3a" /\ flag[1] /\ P2b ~> CS(0)
        BY <1>2, LP2c2, PTL
    <1>4 [][Next]_vars /\ WF_vars(Next) => pc[0] = "a3a" /\ P2b ~> CS(0)
        BY <1>1, <1>3, PTL
    \* Case pc[0] = a3b. Then P2b ~> P2c ~> CS(0)
    <1>5 [][Next]_vars /\ WF_vars(Next) => (pc[0] = "a3b" /\ P2b) ~> CS(0)
        <2>6 QED    
\*    BY LP2c3, P1a, LP1, LP2c , PTL DEF P2b, Wait, P1, WillEnterCSNext, Not, Inv, TypeOK, I
    <1>6 QED
        BY <1>4, <1>5, PTL DEF Wait, P2b

LEMMA LLP2 == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P2 ~> CS(0)
    \* TODO: With the new definition separate WF conditions on proc(0) and proc(1), things might be 
    \* simpler, and we might not need to split into two cases of P1 and P2. REVISIT.
    \* When proc(0) step taken then CS(0) is reached 
    \* Suppose proc(1) step taken. Then process 1 reaches a2
\*    BY LP2, LP2a, LP2b, PTL
    <1>1 [][proc(0)]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P2 ~> CS(0)
        <2>6 QED
    <1>2 [][proc(1)]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P2 ~> CS(0)
        <2>6 QED
    <1>6 QED
        BY <1>1, <1>2, PTL DEF Next       

Q1 == Inv /\ Wait(0) /\ ~WillEnterCSNext(0)

LEMMA 2_3_NOT_WAIT == TypeOK => (~Wait(1) <=> (pc[1] = "cs" \/ pc[1] = "a4" \/ pc[1] = "a1" \/ pc[1] = "a2"))
    BY DEF Wait, TypeOK
    
LEMMA 2_3_CASE_a4_1 == [][Next]_vars /\ WF_vars(Next) => (pc[1] = "a4" /\ Q1) ~> CS(0)
    <1>1 [][Next]_vars /\ WF_vars(Next) => (pc[1] = "a4" /\ Q1) ~> P1
        <2>6 QED
    <1>2 QED
        BY <1>1, LP1, PTL    

LEMMA 2_3_CASE_CS_1 == [][Next]_vars /\ WF_vars(Next) => (pc[1] = "cs" /\ Q1) ~> CS(0)
    <1>1 [][Next]_vars /\ WF_vars(Next) => (pc[1] = "cs" /\ Q1) ~> (pc[1] = "a4" /\ Q1)
        <2>6 QED
    <1>2 QED
        BY <1>1, 2_3_CASE_a4_1, PTL

LEMMA 2_3_CASE_WAIT_1 == [][Next]_vars /\ WF_vars(Next) => (Wait(1) /\ Q1) ~> CS(0)
    <1>1 [][Next]_vars /\ WF_vars(Next) => (Wait(1) /\ Q1) ~> (pc[1] = "cs" /\ Q1)
        <2>6 QED
    <1>2 QED
        BY <1>1, 2_3_CASE_CS_1, PTL

LEMMA 2_3_CASE_a2_1 == [][Next]_vars /\ WF_vars(Next) => (pc[1] = "a2" /\ Q1) ~> CS(0)
    <1>1 [][Next]_vars /\ WF_vars(Next) => (pc[1] = "a2" /\ Q1) ~> P1
        <2>6 QED
    <1>2 QED
        BY <1>1, LP1, PTL

LEMMA 2_3_CASE_a1_1 == [][Next]_vars /\ WF_vars(Next) => (pc[1] = "a1" /\ Q1) ~> CS(0)
    <1>1 [][Next]_vars /\ WF_vars(Next) => (pc[1] = "a1" /\ Q1) ~> (pc[1] = "a2" /\ Q1)
        <2>6 QED
    <1>2 QED
        BY <1>1, 2_3_CASE_a2_1, PTL


LEMMA 2_3_CASE_WAIT_2 == [][Next]_vars /\ WF_vars(Next) => (~Wait(1) /\ Q1) ~> CS(0)
    BY 2_3_CASE_CS_1, 2_3_CASE_a4_1, 2_3_CASE_a1_1, 2_3_CASE_a2_1, 2_3_NOT_WAIT, PTL DEF Wait, Q1, Inv, TypeOK

THEOREM Liveness == Spec /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => Wait(0) ~> CS(0)
<1>1 []Inv /\ [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => Wait(0) ~> CS(0)
    <2>1 SUFFICES [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Inv /\ Wait(0)) ~> CS(0)
        BY PTL
    <2>2 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Inv /\ Wait(0) /\ WillEnterCSNext(0)) ~> CS(0)
        BY LP1, LLP2, PTL DEF P1, P2
    <2>3 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Inv /\ Wait(0) /\ ~WillEnterCSNext(0)) ~> CS(0)
        BY 2_3_CASE_WAIT_1, 2_3_CASE_WAIT_2, PTL DEF Wait, Q1, Inv, TypeOK, Not
    <2>5 QED
        BY <2>2, <2>3, PTL DEF Q1
<1>2 QED   
    BY Invariance, <1>1 DEF Init, Spec, Wait, CS, Next, proc, Inv, TypeOK, I, Not
    
=============================================================================
\* Modification History
\* Last modified Fri Sep 18 12:46:51 AEST 2020 by raghavendra
\* Created Mon Aug 31 12:09:32 AEST 2020 by raghavendra