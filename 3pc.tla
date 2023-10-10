-------------------------------- MODULE 3pc --------------------------------

EXTENDS Naturals, Integers, Sequences, TLC, FiniteSets

CONSTANT RM

VARIABLE    
    rm,
    tm,
    tmPrepared,
    tmPrecommitted,
    msgs
\*    timeout
vars == <<rm, tm, tmPrepared, tmPrecommitted, msgs>>
Message == [ op: {"prepare", "pre-commit", "commit", "abort"}] \cup [ op: {"prepared", "pre-ack", "commit-ack", "abort"}, src: RM ]

TMState == { "working", "prepared", "pre-committed", "committed", "aborted" }

RMState == { "init", "committed", "aborted" }

TypeOK ==
    /\ msgs \subseteq Message
    /\ rm \in RMState
    /\ tm \in [ r \in RM |-> TMState ] 
    /\ tmPrepared \subseteq RM
    /\ tmPrecommitted \subseteq RM
\*    /\ timeout \in BOOLEAN

Init ==
    /\ msgs = {}
    /\ tm = [r \in RM |-> "working" ]
    /\ rm = "init"
    /\ tmPrepared = {}
    /\ tmPrecommitted = {}
\*    /\ timeout = FALSE

RMPrepare ==
    /\ rm = "init"
    /\ tmPrepared = {}
    /\ msgs' = msgs \cup {[ op |-> "prepare" ]}
    /\ UNCHANGED<<tm, rm, tmPrepared, tmPrecommitted>>
    
RMRcvPrepare(r) ==
    /\ rm = "init"
    /\ tm[r] = "prepared"
    /\ [ op |-> "prepared", src  |-> r ] \in msgs
    /\ tmPrepared' = tmPrepared \cup {r}
    /\ UNCHANGED<<rm, tm, tmPrecommitted>>
    
RMRcvPrecommit(r) ==
    /\ rm = "init"
    /\ tm[r] = "pre-committed"
    /\ [ op |-> "pre-ack", src |-> r ] \in msgs
    /\ tmPrecommitted' = tmPrecommitted \cup {r}
    
RMPrecommit ==
    /\ rm = "init"
    /\ tmPrepared = RM
    /\ tmPrecommitted = {}
    /\ msgs' = msgs \cup {[ op |-> "pre-commit" ]}
    /\ UNCHANGED<<tm, rm, tmPrepared, tmPrecommitted>>
    
TMPrepare(r) ==
    /\ tm[r] = "working"
\*    /\ [ op: "prepare" ] \in msgs
    /\ tm' = [ tm EXCEPT ![r] = "prepared" ]
    /\ msgs' = msgs \cup [ op |-> "prepared", src |-> r ]
    /\ UNCHANGED<<rm, tmPrepared, tmPrecommitted>>
    
TMPrecommit(r) ==
    /\ [ op: "pre-commit" ] \in msgs
    /\ tm[r] = "prepare"
    /\ tm' = [ tm EXCEPT ![r] = "pre-committed" ]
    /\ msgs' = msgs \cup [ op |-> "pre-ack", src |-> r ]
    /\ UNCHANGED<<rm, tmPrepared, tmPrecommitted>>

RMCommit ==
    /\ rm = "init"
    /\ tmPrecommitted = RM
    /\ rm' = "committed"
    /\ msgs' = msgs \cup {[ op |-> "commit" ]}
    
TMCommit(r) ==
    /\ [ op: "commit" ] \in msgs
    /\ tm[r] = "pre-committed"
    /\ tm' = [ tm EXCEPT ![r] = "committed" ]
    /\ msgs' = msgs \cup {[ op |-> "commit-ack", src |-> r ]}

3pcConsistent ==  
    \A rm1, rm2 \in RM : ~ /\ tm[rm1] = "aborted"
                           /\ tm[rm2] = "committed"

Next == \/ RMPrepare \/ RMPrecommit \/ RMCommit
        \/ { \E r \in RM:
            \/ TMPrepare(r)
            \/ TMPrecommit(r)
            \/ RMRcvPrepare(r)
            \/ RMRcvPrecommit(r)
            }
            
Spec == Init /\ [][Next]_<<vars>>

THEOREM Spec => 3pcConsistent /\ []TypeOK



=============================================================================
\* Modification History
\* Last modified Tue Oct 10 11:22:54 WEST 2023 by monkey
\* Created Fri Oct 06 12:09:27 WEST 2023 by monkey

