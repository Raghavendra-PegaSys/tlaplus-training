------------------------------- MODULE Euclid -------------------------------
EXTENDS Integers, TLAPS

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))
Number == Nat \ {0}

CONSTANTS M, N
VARIABLES x, y

Init == (x = M) /\ (y = N)

Next == \/  /\ x < y
            /\ y' = y - x
            /\ x' = x
        \/  /\ x > y
            /\ x' = x - y
            /\ y' = y
            
Spec == Init /\ [][Next]_<<x,y>> 

ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant == 
    /\ x \in Number
    /\ y \in Number
    /\ GCD(x,y) = GCD(M,N)
    
ASSUME NumberAssumption == M \in Number /\ N \in Number

THEOREM InitProperty == Init => InductiveInvariant  
    BY NumberAssumption DEF Init, InductiveInvariant                   
    
AXIOM GCDIdempotence == \A p \in Number : GCD(p, p) = p
AXIOM GCDCommutativity == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDExpansion == \A p,q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)

THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
<1> SUFFICES ASSUME InductiveInvariant, Next
             PROVE InductiveInvariant'
<1> USE DEF InductiveInvariant, Next
<1>1 (x < y) \/ (y < x)
<1>a CASE x < y
    <2>1 (y - x \in Number) /\ ~(y < x)
        BY <1>a DEF Number
    <2> QED
        BY <1>a, <2>1, GCDExpansion
<1>b CASE y < x
    <2>1 (x - y \in Number) /\ ~(x < y)
        BY <1>b DEF Number
    <2>2 GCD(y', x') = GCD(y, x)
        BY <1>b, <2>1, GCDExpansion
    <2> QED
        BY <1>b, <2>1, <2>2, GCDCommutativity
<1>2 QED
    BY <1>1, <1>a, <1>b 

THEOREM Correctness == Spec => []ResultCorrect
<1>1 InductiveInvariant /\ UNCHANGED <<x,y>> => InductiveInvariant'
    BY DEF InductiveInvariant
<1>2 Spec => []InductiveInvariant
    BY PTL, InitProperty, NextProperty, <1>1 DEF Spec
<1>3 InductiveInvariant => ResultCorrect
    BY GCDIdempotence DEF InductiveInvariant, ResultCorrect
<1> QED
    BY PTL, <1>2, <1>3
=============================================================================
\* Modification History
\* Last modified Mon Aug 31 14:27:36 AEST 2020 by raghavendra
\* Created Mon Aug 31 12:42:36 AEST 2020 by raghavendra

