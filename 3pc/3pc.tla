-------------------------------- MODULE 3pc --------------------------------

EXTENDS Integers 

CONSTANT RM \* The set of resource managers

VARIABLE    
    rmState,        \* State of each resource manager
    tmState,        \* State of the transaction manager
    rmPrepared,     \* The set of RMs from which the TM has received prepared messages
    rmPrecommitted, \* The set of RMs from which the TM has received pre-committed messages
    msgs,           \* Set of all messages
    timeout         \* Timeout flag

\* All possible states the RMs and TM can assume
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

\* The set of all possible messages.
Message == [ type: {_PREPARE, _PRECOMMIT, _COMMIT, _ABORT}] \cup
           [ type: {_PREPARED, _PRECOMMITTED, _ABORTED}, rm: RM ]

TypeOK ==
    /\ rmState \in [ RM -> { _WORKING, _PREPARED, _PRECOMMITTED, _COMMITTED, _ABORTED } ]
    /\ tmState \in { _INIT, _COMMITTED, _ABORTED }
    /\ rmPrepared \subseteq RM
    /\ rmPrecommitted \subseteq RM
    /\ msgs \subseteq Message
    /\ timeout \in {"on", "off"}

\* Initial State of the Spec
Init ==
    /\ rmState = [r \in RM |-> _WORKING ]
    /\ tmState = _INIT
    /\ rmPrepared = {}
    /\ rmPrecommitted = {}
    /\ msgs = {}
    /\ timeout = "off"

\* TM receives a prepare message from r
TMRcvPrepare(r) ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ [ type |-> _PREPARED, rm  |-> r ] \in msgs
    /\ r \notin rmPrepared
    /\ rmPrepared' = rmPrepared \cup {r}
    /\ UNCHANGED<<tmState, rmState, rmPrecommitted, msgs, timeout>>

\* TM receives a precommit message from r
TMRcvPrecommit(r) ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ [ type |-> _PRECOMMITTED, rm |-> r ] \in msgs
    /\ r \notin rmPrecommitted
    /\ rmPrecommitted' = rmPrecommitted \cup {r}
    /\ UNCHANGED<<tmState, rmState, rmPrepared, msgs, timeout>>

\* TM sends pre-commit message after receiving prepared message from RMs   
TMPrecommit ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ rmPrepared = RM
    /\ rmPrecommitted = {}
    /\ [ type |-> _PRECOMMIT ] \notin msgs
    /\ msgs' = msgs \cup {[ type |-> _PRECOMMIT ]}
    /\ UNCHANGED<<tmState, rmState, rmPrepared, rmPrecommitted, timeout>>

\* TM changes to the commit state and sends message to commit    
TMCommit ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ rmPrecommitted = RM
    /\ tmState' = _COMMITTED
    /\ msgs' = msgs \cup {[ type |-> _COMMIT ]}
    /\ UNCHANGED<<rmState, rmPrepared, rmPrecommitted, timeout>>

\* TM decides to abort the transaction
TMAbort ==
    /\ timeout = "off"
    /\ rmPrecommitted = {}
    /\ ~ ([ type |-> _PRECOMMIT ] \in msgs \/ [ type |-> _COMMIT ] \in msgs)
    /\ tmState = _INIT
    /\ tmState' = _ABORTED
    /\ msgs' = msgs \cup {[type |-> _ABORT]}
    /\ UNCHANGED <<rmState, rmPrepared, rmPrecommitted, timeout>>

\* TM decides to abort the transaction after seeing an aborted message and sends abort message
TMRcvAbort(r) ==
    /\ timeout = "off"
    /\ tmState = _INIT
    /\ [type |-> _ABORTED, rm |-> r] \in msgs
    /\ rmPrecommitted = {}
    /\ tmState' = _ABORTED
    /\ msgs' = msgs \cup {[type |-> _ABORT]}
    /\ UNCHANGED <<rmState, rmPrepared, rmPrecommitted, timeout>>

\* RM decides to go into prepare state
RMPrepare(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _WORKING
    /\ rmState' = [rmState EXCEPT ![r] = _PREPARED]
    /\ msgs' = msgs \cup {[ type |-> _PREPARED, rm |-> r ]}
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, timeout>>

\* RM decides to pre-commit after seeing a pre-commit message from TM
RMPrecommit(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _PREPARED
    /\ [ type |-> _PRECOMMIT ] \in msgs
    /\ rmState' = [ rmState EXCEPT ![r] = _PRECOMMITTED ]
    /\ msgs' = msgs \cup {[ type |-> _PRECOMMITTED, rm |-> r ]}
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, timeout>>

\* RM decides to commit after seeing a commit message from TM
RMCommit(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _PRECOMMITTED
    /\ [ type |-> _COMMIT ] \in msgs
    /\ rmState' = [ rmState EXCEPT ![r] = _COMMITTED ]
    /\ UNCHANGED<<tmState, rmPrepared, rmPrecommitted, msgs, timeout>>

\* RM Chooses to abort during the prepare phase
RMChooseToAbort(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _WORKING
    /\ rmState' = [rmState EXCEPT ![r] = _ABORTED]
    /\ r \notin rmPrepared
    /\ msgs' = msgs \cup {[type |-> _ABORTED, rm |-> r ]}
    /\ UNCHANGED <<tmState, rmPrepared, rmPrecommitted, timeout>>

\* RM decides to abort after seeing the abort message from TM
RMRcvAbortMsg(r) ==
    /\ timeout = "off"
    /\ rmState[r] = _PREPARED \/ rmState[r] = _WORKING
    /\ [type |-> _ABORT] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = _ABORTED]
    /\ UNCHANGED <<tmState, rmPrepared, rmPrecommitted, msgs, timeout>>

\* Timeout happens during execution
Timeout == 
    /\ timeout = "off"
    /\ timeout' = "on"
    /\ UNCHANGED<<msgs, rmState, tmState, rmPrepared, rmPrecommitted>>


\* RM has to decide to abort or commit after seeing a timeout
RMWhenTimeout(r) == 
    /\ timeout = "on"
    /\ rmState[r] \notin {_ABORTED, _COMMITTED}
    /\ IF rmPrecommitted # {}
                THEN
                    /\ rmState' = [rmState EXCEPT ![r] = _COMMITTED]
                ELSE
                    /\ rmState' = [rmState EXCEPT ![r] = _ABORTED]
    /\ UNCHANGED<<msgs,tmState, rmPrepared, rmPrecommitted, timeout>>

\* TM has to decide to abort or commit after seeing a timeout
TMWhenTimeout == 
    /\ timeout = "on"
    /\ tmState \notin {_ABORTED, _COMMITTED}
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
        \/ TMWhenTimeout
        \/ \E r \in RM:
                \/ TMRcvPrepare(r)
                \/ TMRcvPrecommit(r)
                \/ TMRcvAbort(r)
                \/ RMPrepare(r)
                \/ RMPrecommit(r)
                \/ RMCommit(r)
                \/ RMWhenTimeout(r)
                \/ RMChooseToAbort(r)
                \/ RMRcvAbortMsg(r)
            
Spec == Init /\ [][Next]_<<vars>> /\ Fairness

THEOREM Spec => []TypeOK 
THEOREM Spec => <>Validity
THEOREM Spec => <>Agreement 

=============================================================================
\* Modification History
\* Last modified Thu Oct 12 10:43:54 WEST 2023 by monkey
\* Last modified Tue Oct 10 12:16:15 WEST 2023 by andre
\* Created Fri Oct 06 12:09:27 WEST 2023 by monkey

