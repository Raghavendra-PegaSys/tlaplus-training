----------------------------- MODULE Peterson3 -----------------------------
\* This is the version of Peterson's algorithm without the variable flag

EXTENDS TLAPS

VARIABLES turn, pc

vars == <<turn, pc>>

Not(i) == IF i = 0 THEN 1 ELSE 0

Init == 
    /\ turn = 0
    /\ pc = [self \in {0,1} |-> "a2"]
        
a2(self) == 
    /\ pc[self] = "a2"
    /\ pc' = [pc EXCEPT ![self] = "a3"]
    /\ turn' = Not(self)
                
a3_cs(self) == 
    /\ pc[self] = "a3"
    /\ turn = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<turn>>
   
a3_a3(self) == 
    /\ pc[self] = "a3"
    /\ turn = Not(self)
    /\ UNCHANGED <<pc, turn>>
                     
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED <<turn>>
            
proc(self) == 
    \/ a2(self) 
    \/ a3_cs(self) 
    \/ a3_a3(self) 
    \/ cs(self)
    
Next == proc(0) \/ proc(1)

Spec == Init /\ [][Next]_vars

MutualExclusion == (pc[0] # "cs") \/ (pc[1] # "cs")

TypeOK == 
    /\ pc \in [{0, 1} -> {"a2", "a3", "cs"}]
    /\ turn \in {0,1}
    
I == \A i \in {0,1}:
    pc[i] = "cs" =>  ~(pc[Not(i)] = "cs") /\ (pc[Not(i)] = "a3" => turn = i) 

Inv == TypeOK /\ I

LEMMA Invariance == Spec => []Inv
<1>1 Init => Inv
    BY DEF Init, Inv, TypeOK, I
<1>2 Inv /\ [Next]_vars => Inv'
    <2>1 SUFFICES ASSUME Inv, Next
            PROVE Inv'
        BY DEF Inv, TypeOK, I, vars
    <2>2 TypeOK'
        BY <2>1 DEF Inv, Next, a2,  a3_cs, a3_a3, cs, proc, TypeOK, Not
    <2>3 I'
        <3>1 SUFFICES ASSUME NEW j \in {0,1}
                PROVE I!(j)'
            BY DEF I
        <3>2 PICK i \in {0,1} : proc(i)
            BY <2>1 DEF Next
        <3>3 CASE i = j
            BY <2>1, <3>2, <3>3 DEF Inv, I, TypeOK, proc,  a2, a3_cs, a3_a3, cs, Not
        <3>4 CASE i # j
            BY <2>1, <3>2, <3>4 DEF Inv, I, TypeOK, proc,  a2, a3_cs, a3_a3, cs, Not
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
    
\* For any valid, MutualExclusion is satisfied in all states. 
THEOREM Spec => []MutualExclusion
    <1>1 Inv => MutualExclusion
        BY DEF Inv, TypeOK, I, Not, MutualExclusion
    <1>2 QED
        BY <1>1, Invariance, PTL DEF MutualExclusion, Inv, TypeOK, I, Not

P == Inv /\ pc[0] = "a3" /\ turn = 0

LEMMA LPb == <<Next /\ proc(0)>>_vars /\ P => (pc[0] = "cs")'
    BY DEF Next, proc, a2, a3_cs, a3_a3, cs, P, Inv, TypeOK, Not, I

LEMMA LPc == P => ENABLED <<proc(0)>>_vars
    PROOF OMITTED
    
LEMMA LPa == [Next]_vars /\ P => P' \/ (pc[0] = "cs")'
    <1>1 vars' = vars /\ P => P'
        BY DEF P, Inv, TypeOK, I, Not, vars
    <1>2 proc(1) /\ P => P'
        BY DEF P, Inv, TypeOK, I, Not, vars, proc, a2, a3_cs, a3_a3, cs        
    <1>6 QED
        BY LPb, <1>1, <1>2 DEF Next

LEMMA LP == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P ~> (pc[0] = "cs")
    BY LPa, LPb, LPc, PTL

Q == Inv /\ pc[0] = "a3" /\ turn = 1 

LEMMA LQ1b == <<Next /\ proc(1)>>_vars /\ (Q /\ pc[1] = "a2") => (P /\ pc[1] = "a3" )'
        BY DEF P, Inv, TypeOK, I, Not, vars, proc, a2, a3_cs, a3_a3, cs, Q        
    
LEMMA LQ1a == [Next]_vars /\ (Q /\ pc[1] = "a2") => (Q /\ pc[1] = "a2")' \/ (P /\ pc[1] = "a3")'
    <1>1 vars' = vars /\ (Q /\ pc[1] = "a2") => (Q /\ pc[1] = "a2")'
        BY DEF Inv, TypeOK, I, Not, vars, Q
    <1>2 proc(0) /\ (Q /\ pc[1] = "a2") => (Q /\ pc[1] = "a2")'
        BY DEF Inv, TypeOK, I, Not, vars, proc, a2, a3_cs, a3_a3, cs, Q        
    <1>6 QED
        BY LQ1b, <1>1, <1>2 DEF Next


LEMMA LQ1c == (Q /\ pc[1] = "a2") => ENABLED <<proc(1)>>_vars
    PROOF OMITTED
    
LEMMA LQ1 == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => 
    (Q /\ pc[1] = "a2") ~> (P /\ pc[1] = "a3" )
    BY LQ1a, LQ1b, LQ1c, PTL DEF Next
    
LEMMA LQ2 == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => 
    (Q /\ pc[1] = "cs") ~> (Q /\ pc[1] = "a2" )
    
LEMMA LQ3 == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => 
    (Q /\ pc[1] = "a3") ~> (Q /\ pc[1] = "cs" )
    
    
LEMMA LQ == [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => Q ~> (pc[0] = "cs")
<1>1 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Q /\ pc[1] = "a2") ~> (pc[0] = "cs")
            BY LQ1, LP, PTL
<1>2 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Q /\ pc[1] = "cs") ~> (pc[0] = "cs")
            BY LQ2, <1>1, PTL
<1>3 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Q /\ pc[1] = "a3") ~> (pc[0] = "cs")
            BY LQ3, <1>2, PTL
<1>4 Inv => pc[1] = "a2" \/ pc[1] = "a3" \/ pc[1] = "cs"
    BY DEF Inv, TypeOK                         
<1>6 QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Q   
 
THEOREM Liveness == Spec /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => pc[0] = "a3" ~> pc[0] = "cs"
<1>1 []Inv /\ [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => pc[0] = "a3" ~> pc[0] = "cs"
    <2>1 SUFFICES [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Inv /\ pc[0] = "a3") ~> pc[0] = "cs" 
        BY PTL
    <2>2 Inv => turn = 0 \/ turn = 1
        BY DEF Inv, TypeOK, Not
    <2>5 QED
        BY <2>2, LP, LQ, PTL DEF P, Q
<1>2 QED   
    BY Invariance, <1>1 DEF Init, Spec, Next, proc, Inv, TypeOK, I, Not


=============================================================================
\* Modification History
\* Last modified Thu Oct 01 23:33:36 AEST 2020 by raghavendra
\* Created Thu Oct 01 10:18:50 AEST 2020 by raghavendra
