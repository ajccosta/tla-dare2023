-------------------------------- MODULE 3pc --------------------------------

EXTENDS Integers, FiniteSets 

CONSTANT RM

VARIABLE    
    rmState,
    tmState,
    rmPrepared,
    rmPrecommitted,
    msgs,
    timeout


_WORKING == "working"
_PREPARED == "prepared"
_PREPARE == "prepare"
_PRECOMMIT == "pre-commit"
_PRECOMMITTED == "pre-committed"
_COMMIT == "commit"
_COMMITTED == "committed"
_ABORT == "abort"
_ABORTED == "aborted"
_INIT == "init"

vars == <<rmState, tmState, rmPrepared, rmPrecommitted, msgs, timeout>>

Message == [ type: {_PREPARE, _PRECOMMIT, _COMMIT, _ABORT}] \cup
           [ type: {_PREPARED, _PRECOMMITTED, _ABORTED}, rm: RM ]

TypeOK ==
    /\ rmState \in [ RM -> { "working", _PREPARED, _PRECOMMITTED, _COMMITTED, _ABORTED } ]
    /\ tmState \in { _INIT, _COMMITTED, _ABORTED }
    /\ rmPrepared \subseteq RM
    /\ rmPrecommitted \subseteq RM
    /\ msgs \subseteq Message
    /\ timeout \in {"on", "off"}

Init ==
    /\ rmState = [r \in RM |-> "working" ]
    /\ tmState = _INIT
    /\ rmPrepared = {}
    /\ rmPrecommitted = {}
    /\ msgs = {}
    /\ timeout = "off"
    
TMRcvPrepare(r) ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ [ type |-> _PREPARED, rm  |-> r ] \in msgs
    /\ r \notin rmPrepared
    /\ rmPrepared' = rmPrepared \cup {r}
    /\ UNCHANGED<<tmState, rmState, rmPrecommitted, msgs, timeout>>
    
TMRcvPrecommit(r) ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ [ type |-> _PRECOMMITTED, rm |-> r ] \in msgs
    /\ r \notin rmPrecommitted
    /\ rmPrecommitted' = rmPrecommitted \cup {r}
    /\ UNCHANGED<<tmState, rmState, rmPrepared, msgs, timeout>>
   
TMPrecommit ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ rmPrepared = RM
    /\ rmPrecommitted = {}
    /\ [ type |-> _PRECOMMIT ] \notin msgs
    /\ msgs' = msgs \cup {[ type |-> _PRECOMMIT ]}
    /\ UNCHANGED<<tmState, rmState, rmPrepared, rmPrecommitted, timeout>>
    
TMCommit ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ rmPrecommitted = RM
    /\ tmState' = _COMMITTED
    /\ msgs' = msgs \cup {[ type |-> _COMMIT ]}
    /\ UNCHANGED<<rmState, rmPrepared, rmPrecommitted, timeout>>
    
TMAbort ==
    /\ timeout = "off"
    /\ rmPrecommitted = {}
    /\ ~ ([ type |-> _PRECOMMIT ] \in msgs \/ [ type |-> _COMMIT ] \in msgs)
    /\ tmState = _INIT
    /\ tmState' = _ABORTED
    /\ msgs' = msgs \cup {[type |-> _ABORT]}
    /\ UNCHANGED <<rmState, rmPrepared, rmPrecommitted, timeout>>

TMRcvAbort(r) ==
\*    /\ timeout = "off"
    /\ tmState = _INIT
    /\ [type |-> _ABORTED, rm |-> r] \in msgs
    /\ rmPrecommitted = {}
    /\ tmState' = _ABORTED
    /\ msgs' = msgs \cup {[type |-> _ABORT]}
    /\ UNCHANGED <<rmState, rmPrepared, rmPrecommitted, timeout>>

RMPrepare(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _WORKING
    /\ rmState' = [rmState EXCEPT ![r] = _PREPARED]
    /\ msgs' = msgs \cup {[ type |-> _PREPARED, rm |-> r ]}
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, timeout>>
    
RMPrecommit(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _PREPARED
    /\ [ type |-> _PRECOMMIT ] \in msgs
    /\ rmState' = [ rmState EXCEPT ![r] = _PRECOMMITTED ]
    /\ msgs' = msgs \cup {[ type |-> _PRECOMMITTED, rm |-> r ]}
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, timeout>>
    
RMCommit(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _PRECOMMITTED
    /\ [ type |-> _COMMIT ] \in msgs
    /\ rmState' = [ rmState EXCEPT ![r] = _COMMITTED ]
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, msgs, timeout>>
    
RMChooseToAbort(r) ==
    /\ rmState[r] = _WORKING
    /\ rmState' = [rmState EXCEPT ![r] = _ABORTED]
    /\ r \notin rmPrepared
    /\ msgs' = msgs \cup {[type |-> _ABORTED, rm |-> r ]}
    /\ UNCHANGED <<tmState, rmPrepared, rmPrecommitted, timeout>>

RMRcvAbortMsg(r) ==
    /\ rmState[r] = _PREPARED \/ rmState[r] = _WORKING
    /\ [type |-> _ABORT] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = _ABORTED]
    /\ UNCHANGED <<tmState, rmPrepared, rmPrecommitted, msgs, timeout>>

Timeout == 
    /\ ~ tmState = _COMMITTED
    /\ timeout = "off"
    /\ timeout' = "on"
    /\ UNCHANGED<<msgs, rmState, tmState, rmPrepared, rmPrecommitted>>

RMWhenTimeout(r) == 
    /\ timeout = "on"
    /\ rmState[r] \notin {_ABORTED, _COMMITTED}
    /\ IF rmPrecommitted # {}
                THEN
                    /\ rmState' = [rmState EXCEPT ![r] = _COMMITTED]
                ELSE
                    /\ rmState' = [rmState EXCEPT ![r] = _ABORTED]
    /\ UNCHANGED<<msgs,tmState, rmPrepared, rmPrecommitted, timeout>>
            
TMWhenTimeout == 
    /\ timeout = "on"
    /\ tmState = _INIT
    /\  IF rmPrecommitted # {} /\ ~ [ type |-> _ABORT ] \in msgs
        THEN
            /\ tmState' = _COMMITTED
        ELSE
            /\ tmState' = _ABORTED
    /\ UNCHANGED<<msgs,rmState, rmPrepared, rmPrecommitted, timeout>>
        
        



Agreement ==  
    \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = _ABORTED
                           /\ rmState[rm2] = _COMMITTED

Validity ==
    \E r \in RM: rmState[r] = _ABORTED ~> tmState = _ABORTED


Fairness == 
            \* For validity 1 and 2:
            /\ WF_vars(TMCommit)
            /\ WF_vars(TMAbort)
            /\ WF_vars(TMPrecommit)
            /\ \A r \in RM: WF_vars(TMRcvPrecommit(r))
            /\ \A r \in RM: WF_vars(TMRcvPrepare(r))
            /\ \A r \in RM: WF_vars(TMRcvAbort(r))
            /\ \A r \in RM: WF_vars(TMWhenTimeout)
            /\ \A r \in RM: WF_vars(RMWhenTimeout(r))
Next == 
        \/ TMPrecommit 
        \/ TMCommit 
        \/ TMAbort 
        \/ Timeout
        \/ \E r \in RM:
                \/ TMRcvPrepare(r)
                \/ TMRcvPrecommit(r)
                \/ RMPrepare(r)
                \/ RMPrecommit(r)
                \/ RMCommit(r)
                \/ TMWhenTimeout
                \/ RMWhenTimeout(r)
                \/ RMChooseToAbort(r)
                \/ RMRcvAbortMsg(r)
                \/ TMRcvAbort(r)
            
Spec == Init /\ [][Next]_<<vars>> /\ Fairness

THEOREM Spec => []TypeOK 
THEOREM Spec => <>Validity
THEOREM Spec => <>Agreement 

=============================================================================
\* Modification History
\* Last modified Wed Oct 11 15:43:49 WEST 2023 by monkey
\* Last modified Tue Oct 10 12:16:15 WEST 2023 by andre
\* Created Fri Oct 06 12:09:27 WEST 2023 by monkey

