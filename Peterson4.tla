----------------------------- MODULE Peterson4 -----------------------------
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

Next == proc(0) \/ proc(1)

Spec == Init /\ [][Next]_vars

MutualExclusion == (pc[0] # "cs") \/ (pc[1] # "cs")

TypeOK == 
    /\ flag  \in [{0,1} -> BOOLEAN]
    /\ pc \in [{0, 1} -> {"a1", "a2", "a3a", "a3b", "cs", "a4"}]
    /\ turn \in {0,1}
    
I == \A i \in {0,1}:
    /\ (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i])
    /\ (pc[i] = "a1" => ~flag[i])
    /\ (pc[i] \in {"cs", "a4"}) => /\ ~(pc[Not(i)] \in {"cs","a4"})
                                 /\ (pc[Not(i)] \in {"a3a","a3b"} => turn = i) 

Inv == TypeOK /\ I

LEMMA Invariance == Spec => []Inv
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
    
\* For any valid, MutualExclusion is satisfied in all states. 
THEOREM Spec => []MutualExclusion
    <1>1 Inv => MutualExclusion
        BY DEF Inv, TypeOK, I, Not, MutualExclusion
    <1>2 QED
        BY <1>1, Invariance, PTL DEF MutualExclusion, Inv, TypeOK, I, Not

\* Liveness
    
Wait(i) == (pc[i] = "a3a") \/ (pc[i] = "a3b")
CS(i) == pc[i] = "cs"
     
\**********
     
THEOREM Liveness == Spec /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => Wait(0) ~> CS(0)
<1>1 []Inv /\ [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => Wait(0) ~> CS(0)
    <2>1 SUFFICES [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => (Inv /\ Wait(0)) ~> CS(0)
        BY PTL
    <2>2 Inv => turn = 0 \/ turn = 1
        BY DEF Inv, TypeOK
    <2> DEFINE P == Inv /\ Wait(0) /\ turn = 0
    <2>LP [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  P ~> CS(0)
        <3> DEFINE P1 == Inv /\ pc[0] = "a3b" /\ turn = 0
        <3>LP1 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P1 ~> CS(0)
            <4>1 <<Next /\ proc(0)>>_vars /\ P1 => CS(0)'
                BY DEF CS, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
            <4>2 [Next]_vars /\ P1 => P1' \/ CS(0)'
                <5>1 vars' = vars /\ P1 => P1'
                    BY DEF vars, Inv, TypeOK, I  
                <5>2 proc(1) /\ P1 => (I /\ pc[0] = "a3b" /\ turn = 0)'
                    BY DEF Inv, TypeOK, I, proc, I, Not, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4          
                <5>3 proc(1) /\ P1 => (TypeOK)'
                    BY  DEF Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4
                <5>6 QED    
                    BY <5>1, <5>2, <5>3, <4>1 DEF Next, Inv
            <4>3 P1 => ENABLED <<proc(0)>>_vars
                PROOF OMITTED
            <4>4 QED
                BY <4>1, <4>2, <4>3, PTL DEF Next
        <3> DEFINE P2 == Inv /\ pc[0] = "a3a" /\ turn = 0
        <3>LP2 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) => P2 ~> P1 \/ CS(0)
            <4>1 <<Next /\ proc(0)>>_vars /\ P2 => P1' \/ CS(0)'
                BY DEF CS, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not
            <4>2 [Next]_vars /\ P2 => P2' \/ P1' \/ CS(0)'
                <5>1 vars' = vars /\ P2 => P2'
                    BY DEF vars, Inv, TypeOK, I        
                <5>2 proc(1) /\ P2 => TypeOK'
                    BY  DEF Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4
                <5>3 proc(1) /\ P2 => (I /\ pc[0] = "a3a" /\ turn = 0)'
                    BY  DEF Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4
                <5>6 QED    
                    BY <5>1, <5>2, <5>3, <4>1 DEF Next, Inv
            <4>3 P2 => ENABLED <<proc(0)>>_vars
                PROOF OMITTED
            <4>4 QED    
                BY <4>1, <4>2, <4>3, PTL DEF Next        
        <3> QED
            BY <3>LP1, <3>LP2, PTL DEF Wait
    <2> DEFINE  Q == Inv /\ Wait(0) /\ turn = 1
                Q1 == Inv /\ Wait(0) /\ turn = 1 /\ flag[1] /\ pc[1] = "a2"
                QA == Inv /\ Wait(0) /\ turn = 1 /\ ~flag[1]
                QB == Inv /\ Wait(0) /\ turn = 1 /\ flag[1]
    <2>LQ1 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q1 ~> P
        <3>1 <<Next /\ proc(1)>>_vars /\ Q1 => P'
            BY DEF CS, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
        <3>2 [Next]_vars /\ Q1 => Q1' \/ P'
            <4>1 vars' = vars /\ Q1 => Q1'
                BY DEF vars, Q1, Inv, TypeOK, I, Wait        
            <4>2 proc(0) /\ Q1 => Q1'
                BY  DEF Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Wait
            <4>6 QED    
                BY <4>1, <4>2, <3>1 DEF Next
        <3>3 Q1 => ENABLED <<proc(1)>>_vars
            PROOF OMITTED
        <3>4 QED    
            BY <3>1, <3>2, <3>3, PTL DEF Next                   
    <2>LQ [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q ~> CS(0)
        <3>LQA [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  QA ~> CS(0)
            <4> DEFINE  Q2 == Inv /\ pc[0] = "a3a" /\ turn = 1 /\ ~flag[1]
            <4>LQ2 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q2 ~> Q1 \/ CS(0) 
                <5>1 <<Next /\ proc(0)>>_vars /\ Q2 => CS(0)'
                    BY DEF CS, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>2 <<Next /\ proc(1)>>_vars /\ Q2 => Q1'
                    BY DEF CS, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>3 [Next]_vars /\ Q2 => Q2' \/ Q1' \/ CS(0)'
                    <6>1 vars' = vars /\ Q2 => Q2'
                        BY DEF vars, Inv, TypeOK, I, Wait        
                    <6>6 QED    
                        BY <6>1, <5>1, <5>2 DEF Next
                <5>4 Q2 => ENABLED <<proc(0)>>_vars
                    PROOF OMITTED
                <5>5 Q2 => ENABLED <<proc(1)>>_vars
                    PROOF OMITTED
                <5>6 QED       
                    BY <5>1, <5>2, <5>3, <5>4, <5>5, PTL DEF Next            
            <4> DEFINE Q3 == Inv /\ pc[0] = "a3b" /\ turn = 1 /\ ~flag[1]
            <4>LQ3 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q3 ~> Q1 \/ Q2
                <5>1 <<Next /\ proc(0)>>_vars /\ Q3 => Q2'
                    BY DEF Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>2 <<Next /\ proc(1)>>_vars /\ Q3 => Q1'
                    BY DEF Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>3 [Next]_vars /\ Q3 => Q3' \/ Q1' \/ Q2'
                    <6>1 vars' = vars /\ Q3 => Q3'
                        BY DEF vars, Q3, Inv, TypeOK, I, Wait        
                    <6>6 QED    
                        BY <6>1, <5>1, <5>2 DEF Next
                <5>4 Q3 => ENABLED <<proc(0)>>_vars
                    PROOF OMITTED
                <5>5 Q3 => ENABLED <<proc(1)>>_vars
                    PROOF OMITTED
                <5>6 QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5, PTL DEF Next                     
            <4> QED
              BY <4>LQ2, <4>LQ3, <2>LQ1, <2>LP, PTL DEF Wait
        <3>LQB [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  QB ~> CS(0)
            <4>1 Inv /\ flag[1] => pc[1] = "a2" \/ pc[1] = "a3a" \/ pc[1] = "a3b" \/ pc[1] = "cs" \/ pc[1] = "a4"
                BY DEF Inv, TypeOK, I
            <4> DEFINE  Q4 == Inv /\ Wait(0) /\ turn = 1 /\ flag[1] /\ pc[1] = "a3b" 
                        Q5 == Inv /\ Wait(0) /\ turn = 1 /\ flag[1] /\ pc[1] = "cs"
                        Q6 == Inv /\ Wait(0) /\ turn = 1 /\ flag[1] /\ pc[1] = "a3a"
                        Q7 == Inv /\ Wait(0) /\ turn = 1 /\ flag[1] /\ pc[1] = "a4"
            <4>LQ4 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q4 ~> Q5
                <5>1 <<Next /\ proc(1)>>_vars /\ Q4 => Q5'
                    BY DEF Q4, Q5, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>2 [Next]_vars /\ Q4 => Q4' \/ Q5'
                    <6>1 vars' = vars /\ Q4 => Q4'
                        BY DEF vars, Q4, Inv, TypeOK, I, Wait        
                    <6>2 proc(0) /\ Q4 => Q4'
                        BY  DEF Q4, Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Wait
                    <6>6 QED    
                        BY <6>1, <6>2, <5>1 DEF Next
                <5>3 Q4 => ENABLED <<proc(1)>>_vars
                    PROOF OMITTED
                <5>6 QED
                    BY <5>1, <5>2, <5>3, PTL DEF Next            
            <4>LQ6 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q6 ~> Q4
                <5>1 <<Next /\ proc(1)>>_vars /\ Q6 => Q4'
                    BY DEF Q6, Q4, Q5, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>2 [Next]_vars /\ Q6 => Q6' \/ Q4' 
                    <6>1 vars' = vars /\ Q6 => Q6'
                        BY DEF vars, Q6, Inv, TypeOK, I, Wait        
                    <6>2 proc(0) /\ Q6 => Q6'
                        BY  DEF Q6, Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Wait
                    <6>6 QED    
                        BY <6>1, <6>2, <5>1 DEF Next
                <5>3 Q6 => ENABLED <<proc(1)>>_vars
                    PROOF OMITTED
                <5>4 QED 
                    BY <5>1, <5>2, <5>3, PTL DEF Next             
            <4>LQ5 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q5 ~> Q7
                <5>1 <<Next /\ proc(1)>>_vars /\ Q5 => Q7'
                    BY DEF Q5, Q7, Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>2 [Next]_vars /\ Q5 => Q5' \/ Q7'
                    <6>1 vars' = vars /\ Q5 => Q5'
                        BY DEF vars, Q5, Inv, TypeOK, I, Wait        
                    <6>2 proc(0) /\ Q5 => Q5'
                        BY  DEF Q5, Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Wait
                    <6>6 QED    
                        BY <6>1, <6>2, <5>1 DEF Next
                <5>3 Q5 => ENABLED <<proc(1)>>_vars
                    PROOF OMITTED
                <5>4 QED
                    BY <5>1, <5>2, <5>3, PTL DEF Next            
            <4>LQ7 [][Next]_vars /\ WF_vars(proc(0)) /\ WF_vars(proc(1)) =>  Q7 ~> QA
                <5>1 <<Next /\ proc(1)>>_vars /\ Q7 => QA'
                    BY DEF Inv, TypeOK, I, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Not, Wait
                <5>2 [Next]_vars /\ Q7 => QA' \/ Q7'
                    <6>1 vars' = vars /\ Q7 => Q7'
                        BY DEF vars, Inv, TypeOK, I, Wait        
                    <6>2 proc(0) /\ Q7 => Q7'
                        BY  DEF Inv, TypeOK, I, Not, proc, a1, a2, a3a_cs, a3a_a3b, a3b_cs, a3b_a3a, cs, a4, Wait
                    <6>6 QED    
                        BY <6>1, <6>2, <5>1 DEF Next
                <5>3 Q7 => ENABLED <<proc(1)>>_vars
                    PROOF OMITTED
                <5>4 QED
                    BY <5>1, <5>2, <5>3, PTL DEF Next            
            <4>2 QED    
                BY <4>1, <2>LQ1, <2>LP, <4>LQ4, <4>LQ6, <4>LQ5, <4>LQ7, <3>LQA, PTL        
        <3> QED 
            BY <3>LQA, <3>LQB, PTL DEF Inv, TypeOK
    <2>5 QED
        BY <2>2, <2>LP, <2>LQ, PTL  
<1>2 QED   
    BY Invariance, <1>1 DEF Init, Spec, Wait, CS, Next, proc, Inv, TypeOK, I, Not    
=============================================================================
\* Modification History
\* Last modified Thu Oct 15 15:30:24 AEDT 2020 by roberto
\* Last modified Tue Oct 13 13:08:05 AEST 2020 by raghavendra
\* Created Mon Oct 05 23:14:50 AEST 2020 by raghavendra
