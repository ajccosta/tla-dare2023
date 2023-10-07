-------------------------------- MODULE cas --------------------------------


EXTENDS Naturals, Integers, Sequences

CONSTANTS Process
                    

VARIABLES   pstate, (* Current Process state (running or not) *)
            memory, (* this can also be called a counter *)
            lastRead

Init == /\ memory =     0
        /\ lastRead =   [ p \in Process |-> 0 ]
        /\ pstate =     [p \in Process |-> "running"]

(* Reads the memory *)
Read(p) ==  /\ lastRead' = [ lastRead EXCEPT ![p] = memory]
            /\ UNCHANGED<<pstate, memory>>
                
(* Tries to update the value, if the last seen value is still the same *)
Compare_swap(p) == IF lastRead[p] /= memory
                        THEN
                            /\ memory' = lastRead[p] + 1
                            /\ lastRead' = [ lastRead EXCEPT ![p] = -1]
                            /\ UNCHANGED<<pstate>>
                        ELSE
                            /\ lastRead' = [ lastRead EXCEPT ![p] = 0]
                            /\ UNCHANGED<<memory, pstate>>
                            
(* Finishes a process *)                            
finish(p) ==    /\ pstate' = [pstate EXCEPT ![p] = "finish"]
                /\ lastRead' = [ lastRead EXCEPT ![p] = -1 ]
                /\ UNCHANGED<<memory>>            


fairness ==     \A p \in Process:
                    /\ WF_<<>>(pstate[p] /= "finish")
                    /\ WF_<<>>(lastRead[p] /= -1)

Next == \E p \in Process: /\ Read(p) \/ Compare_swap(p) \/ finish(p)
                              
Spec == Init /\ [][Next]_<<>> /\ fairness

TypeInv ==  /\ pstate \in {"running", "finish"}
            /\ memory \in Nat

THEOREM Spec => memory = 100


=============================================================================
\* Modification History
\* Last modified Sat Oct 07 23:27:26 WEST 2023 by monkey
\* Created Mon Oct 02 13:48:14 WEST 2023 by monkey
