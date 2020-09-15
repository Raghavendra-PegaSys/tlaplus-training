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
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ turn' = turn            
            
proc(self) == 
    \/ a0(self) 
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
        BY <2>1 DEF Inv, Next, a0, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, proc, TypeOK, Not
    <2>3 I'
        <3>1 SUFFICES ASSUME NEW j \in {0,1}
                PROVE I!(j)'
            BY DEF I
        <3>2 PICK i \in {0,1} : proc(i)
            BY <2>1 DEF Next
        <3>3 CASE i = j
            BY <2>1, <3>2, <3>3 DEF Inv, I, TypeOK, proc, a0, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
        <3>4 CASE i # j
            BY <2>1, <3>2, <3>4 DEF Inv, I, TypeOK, proc, a0, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
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
WF(i) == 
    /\ WF_vars(a0(i))
    /\ WF_vars(a1(i))
    /\ WF_vars(a2(i))
    /\ WF_vars(a3a_cs(i) \/ a3b_cs(i))
    /\ WF_vars(a3a_a3b(i) \/ a3b_a3a(i))
    /\ WF_vars(cs(i))
    /\ WF_vars(a4(i))
A(i) == a3a_cs(i) \/ a3b_cs(i)
WillEnterCSNext(i) == 
    /\ (pc[i] = "a3a" => ~flag[Not(i)])
    /\ (pc[i] = "a3b" => turn = i)     
FairSpec == Spec /\ WF(0) /\ WF(1)

LEMMA Invariance == Spec => []Inv

P1 == Inv /\ Wait(0) /\ WillEnterCSNext(0) /\ ~(pc[1] = "a1")
LEMMA L1P1 == [Next]_vars /\ P1 => P1' \/ CS(0)'
LEMMA L2P1 == <<Next /\ A(0)>>_vars /\ P1 => CS(0)'
LEMMA L3P1 == P1 => ENABLED <<A(0)>>_vars
LEMMA LP1 == [][Next]_vars /\ WF_vars(A(0)) => P1 ~> CS(0)
BY L1P1, L2P1, L3P1, PTL

P2 == Inv /\ Wait(0) /\ WillEnterCSNext(0) /\ pc[1] = "a1"
P2a == Inv /\ Wait(0) /\ pc[1] = "a2"
P2b == Inv /\ Wait(0) /\ pc[1] = "a3a" /\ turn = 0
P2c == Inv /\ pc[0] = "a3b" /\ turn = 0 /\ Wait(1)

LEMMA L1P2 == [Next]_vars /\ P2 => P2' \/ P2a'
LEMMA L2P2 == <<Next /\ a1(1)>>_vars /\ P2 => P2a'
LEMMA L3P2 == P2 => ENABLED <<a1(1)>>_vars
LEMMA LP2 == [][Next]_vars /\ WF_vars(a1(1)) => P2 ~> P2a
BY L1P2, L2P2, L3P2, PTL

LEMMA L1P2a == [Next]_vars /\ P2a => P2a' \/ P2b'
LEMMA L2P2a == <<Next /\ a2(1)>>_vars /\ P2a => P2b'
LEMMA L3P2a == P2a => ENABLED <<a2(1)>>_vars
LEMMA LP2a == [][Next]_vars /\ WF_vars(a2(1)) => P2a ~> P2b
BY L1P2a, L2P2a, L3P2a, PTL

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

LEMMA LP2b == [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => P2b ~> CS(0)
    \* Case pc[0] = a3a /\ ~flag[1]. Then P2b ~> CS(0). This is the same as LP1.
    <1>1 [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => pc[0] = "a3a" /\ ~flag[1] /\ P2b ~> CS(0)
\*        <2>6 QED
        BY P1a, LP1 DEF P1, WillEnterCSNext, Not, P2b
    \* Case pc[0] = a3a /\ flag[1]. Then P2b ~> P2c
    <1>2 [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => pc[0] = "a3a" /\ flag[1] /\ P2b ~> P2c
        <2>6 QED
    <1>3 [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => pc[0] = "a3a" /\ flag[1] /\ P2b ~> CS(0)
        BY <1>2, LP2c2, PTL
    <1>4 [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => pc[0] = "a3a" /\ P2b ~> CS(0)
        BY <1>1, <1>3, PTL
    \* Case pc[0] = a3b. Then P2b ~> P2c ~> CS(0)
    <1>5 [][Next]_vars /\ WF_vars(a3a_cs(0) \/ a3a_a3b(0) \/ a3b_cs(0)) => (pc[0] = "a3b" /\ P2b) ~> CS(0)
        <2>6 QED    
\*    BY LP2c3, P1a, LP1, LP2c , PTL DEF P2b, Wait, P1, WillEnterCSNext, Not, Inv, TypeOK, I
    <1>6 QED
        BY <1>4, <1>5, PTL DEF Wait, P2b

LEMMA LLP2 == 
\*LEMMA L1P2c == [Next]_vars /\ pc[0] = "a3a" /\ P2b => (pc[0] = "a3a" /\ P2b)' \/ P2c'
\*LEMMA L2P2c == <<Next /\ a3a_a3b(0)>>_vars /\ (pc[0] = "a3a" /\ P2b) => P2c'
\*LEMMA L3P2c == pc[0] = "a3a" /\ P2b => ENABLED <<a3a_a3b(0)>>_vars
\*LEMMA LP2c == [][Next]_vars /\ WF_vars(a3a_a3b(0)) => (pc[0] = "a3a" /\ P2b) ~> P2c
\*BY L1P2c, L2P2c, L3P2c, PTL

\*LEMMA P2bP2c == ~(pc[0] = "a3a") /\ P2b = P2c
\*BY PTL DEF P2b, P2c, Inv, TypeOK, I
\*
\*LEMMA LP2b == [][Next]_vars /\ WF_vars(a3b_cs(0)) => P2c ~> CS(0)
\*BY LP1 DEF P1, P2b, A, WillEnterCSNext, P2c

THEOREM FairSpec => Wait(0) ~> CS(0)
<1>1 []Inv /\ [][Next]_vars /\ WF(0) /\ WF(1) => Wait(0) ~> CS(0)
    <2>1 SUFFICES [][Next]_vars /\ WF(0) /\ WF(1) => (Inv /\ Wait(0)) ~> CS(0)
        BY PTL
    <2>2 SUFFICES [][Next]_vars /\ WF_vars(A(0)) => (Inv /\ Wait(0)) ~> CS(0)
        BY DEF A, WF
    <2>3 [][Next]_vars /\ WF_vars(A(0)) => (Inv /\ Wait(0) /\ WillEnterCSNext(0)) ~> CS(0)
        <3>1 [][Next]_vars /\ WF_vars(A(0)) => P1 ~> CS(0)
            BY LP1 
        <3>2 [][Next]_vars /\ WF_vars(A(0)) => P2 ~> CS(0)
            BY L1P2, L2P2, L3P2, PTL
        <3>3 QED
            BY <3>1, <3>2, PTL DEF P1, P2
    <2>4 [][Next]_vars /\ WF_vars(A(0)) => (Inv /\ Wait(0) /\ ~WillEnterCSNext(0)) ~> CS(0)    
    <2>5 QED
        BY <2>4, <2>3, PTL
<1>2 QED   
    BY Invariance, <1>1 DEF FairSpec, Init, Spec, Wait, CS, Next, proc, Inv, TypeOK, I, Not
    
=============================================================================
\* Modification History
\* Last modified Tue Sep 15 23:22:52 AEST 2020 by raghavendra
\* Created Mon Aug 31 12:09:32 AEST 2020 by raghavendra