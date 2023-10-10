-------------------------------- MODULE 3pc --------------------------------

EXTENDS Integers, FiniteSets

CONSTANT RM

VARIABLE    
    rmState,
    tmState,
    rmPrepared,
    rmPrecommitted,
    msgs
\*    timeout

vars == <<rmState, tmState, rmPrepared, rmPrecommitted, msgs>>

Message == [ type: {"prepare", "pre-commit", "commit", "abort"}] \cup
           [ type: {"prepared", "pre-ack", "abort"}, rm: RM ]

TypeOK ==
    /\ rmState \in [ RM |-> { "working", "prepared", "pre-committed", "committed", "aborted" } ]
    /\ tmState \in { "init", "committed", "aborted" }
    /\ rmPrepared \subseteq RM
    /\ rmPrecommitted \subseteq RM
    /\ msgs \subseteq Message
\*    /\ timeout \in BOOLEAN


Init ==
    /\ rmState = [r \in RM |-> "working"]
    /\ tmState = "init"
    /\ rmPrepared = {}
    /\ rmPrecommitted = {}
    /\ msgs = {}
\*    /\ timeout = FALSE
    
TMRcvPrepare(r) ==
    /\ tmState = "init"
    /\ [ type |-> "prepared", rm  |-> r ] \in msgs
    /\ r \notin rmPrepared
    /\ rmPrepared' = rmPrepared \cup {r}
    /\ UNCHANGED<<tmState, rmState, rmPrecommitted, msgs>>
    
TMRcvPrecommit(r) ==
    /\ tmState = "init"
    /\ [ type |-> "pre-ack", rm |-> r ] \in msgs
    /\ r \notin rmPrecommitted
    /\ rmPrecommitted' = rmPrecommitted \cup {r}
    /\ UNCHANGED<<tmState, rmState, rmPrepared, msgs>>
   
TMPrecommit ==
    /\ tmState = "init"
    /\ rmPrepared = RM
    /\ rmPrecommitted = {}
    /\ msgs' = msgs \cup {[ type |-> "pre-commit" ]}
    /\ UNCHANGED<<tmState, rmState, rmPrepared, rmPrecommitted>>
    
TMCommit ==
    /\ tmState = "init"
    /\ rmPrecommitted = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \cup {[ type |-> "commit" ]}
    /\ UNCHANGED<<rmState, rmPrepared, rmPrecommitted>>
    
RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \cup {[ type |-> "prepared", rm |-> r ]}
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted>>
    
RMPrecommit(r) ==
    /\ rmState[r] = "prepared"
    /\ [ type |-> "pre-commit" ] \in msgs
    /\ rmState' = [ rmState EXCEPT ![r] = "pre-committed" ]
    /\ msgs' = msgs \cup {[ type |-> "pre-ack", rm |-> r ]}
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted>>
    
RMCommit(r) ==
    /\ [ type |-> "commit" ] \in msgs
    /\ rmState[r] = "pre-committed"
    /\ rmState' = [ rmState EXCEPT ![r] = "committed" ]
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, msgs>>

3pcConsistent ==  
    \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                           /\ rmState[rm2] = "committed"

Next == \/ TMPrecommit \/ TMCommit
        \/ \E r \in RM:
                \/ TMRcvPrepare(r)
                \/ TMRcvPrecommit(r)
                \/ RMPrepare(r)
                \/ RMPrecommit(r)
                \/ RMCommit(r)
            
Spec == Init /\ [][Next]_vars

THEOREM Spec => 3pcConsistent /\ []TypeOK



=============================================================================
\* Modification History
\* Last modified Tue Oct 10 14:28:03 WEST 2023 by monkey
\* Last modified Tue Oct 10 12:16:15 WEST 2023 by andre
\* Created Fri Oct 06 12:09:27 WEST 2023 by monkey

