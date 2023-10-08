-------------------------------- MODULE 3pc --------------------------------

EXTENDS Naturals, Integers, Sequences, TLC, FiniteSets

CONSTANT RM

VARIABLE    
    rmState,
    msgsInTransit,
    msgsReceived,
    msgs,
    coordinator

Message == [ type: { "prepare", "prepared", "pre-commit", "commit", "ack", "done", "abort"}, src: RM, dest: RM]

RMState == [ state: { "working"}, step: {"working", "prepare", "pre-commit", "commit", "done", "aborted"}, role: {"participant", "coordinator"} ]
 
Init ==     /\ rmState = [ r \in RM |-> [ state |-> "working", step |-> "working" , role |-> "participant" ] ]
            /\ msgsInTransit = {}
            /\ msgsReceived = [ r \in RM |-> {} ]
            /\ msgs = {}
            /\ coordinator = RandomElement(RM)
(***************************************************************************
Auxiliar Functions
 ***************************************************************************)

HasSentEveryMessageRound(type) == Cardinality({ msg \in msgs: msg.type = type /\ msg.src = coordinator}) /= Cardinality(RM) - 1

ReceivedEveryMessage(type) == Cardinality({ msg \in msgsReceived[coordinator]: msg.type = type }) /= Cardinality(RM) - 1
            

(***************************************************************************
Message Handling Actions
 ***************************************************************************)

SendMessage(msg) == /\ ~ msg \in msgs
                    /\ msgs' = msgs \cup msg
                    /\ msgsInTransit' = msgsInTransit \cup msg
                    /\ UNCHANGED<<msgsReceived, rmState, coordinator>>

DeliverMessage ==   /\ IF Cardinality(msgsInTransit) > 0 
                        THEN
                            LET msg == Head(msgsInTransit) IN
                                /\ msgsInTransit' = msgsInTransit \ msg
                                /\ msgsReceived' = [msgsReceived EXCEPT ![msg.dest] = @ \cup msg]
                                /\ UNCHANGED<<rmState,coordinator, msgs>>
                        ELSE
                            UNCHANGED<<msgsInTransit, msgs, msgsReceived, rmState, coordinator>>
            
UpgradeToCoordinator == /\ CHOOSE r \in RM: rmState' = [rmState EXCEPT ![r].role = "coordinator"]
                        /\ UNCHANGED<<msgsInTransit, msgsReceived, msgs, coordinator>>


(***************************************************************************
Coordinator Functions
 ***************************************************************************)
 
 
BeginTransaction == /\ rmState[coordinator].step = "working"
                    /\ rmState' = [rmState EXCEPT ![coordinator].step = "prepare"]
                    /\ UNCHANGED<<msgsInTransit, msgsReceived, msgs, coordinator>>
                    



(***************************************************************************
Prepare Actions
 ***************************************************************************)

SendPrepare(r) ==   /\ rmState[coordinator].step = "prepare"
                    /\ r # coordinator
                    /\ ~ HasSentEveryMessageRound("prepare") 
                    /\ SendMessage([ type |-> "prepare", src |-> coordinator, dest |-> r ])
                    /\ UNCHANGED<<msgsReceived, rmState, coordinator>>


Prepare(r) == /\ rmState[r].state = "working"
              /\ rmState[r].step = "working"
              /\ r # coordinator
              /\ [ type |-> "prepare", src |-> coordinator, dest |-> r] \in msgsReceived[r]
              /\ rmState' = [rmState EXCEPT ![r].step = "prepare"]
              /\ SendMessage([ type |-> "prepared", src |-> r, dest |-> coordinator ])
              /\ UNCHANGED<<msgs, msgsReceived, msgsInTransit, coordinator>>
              
              
(***************************************************************************
Pre-commit Actions
 ***************************************************************************)

StartPre_commit ==  /\ rmState[coordinator].step = "prepare"
                    /\ rmState' = [rmState EXCEPT ![coordinator].step = "pre-commit"]
                    /\ ReceivedEveryMessage("prepared")
                    /\ UNCHANGED<<msgs, msgsReceived, msgsInTransit, coordinator>>
                    
finish == /\ rmState[coordinator].step = "pre-commit"
          /\ \A r \in RM: rmState' = [rmState EXCEPT ![r].step = "done"]
          /\ UNCHANGED<<msgs, msgsReceived, msgsInTransit, coordinator>>

\*SendPre_commit(r) ==    /\ coordinator.step = "pre-commit"
\*                        /\ ~ HasSentEveryMessageRound("pre-commit") 
\*                        /\ r # coordinator
\*                        /\ SendMessage([ type |-> "pre-commit", src |-> coordinator, dest |-> r ])
\*
\*Pre_commit(r) ==    /\ r.state = "working"
\*                    /\ r # coordinator
\*                    /\ r.step = "prepare"
\*                    /\ [ type |-> "pre-commit", src |-> coordinator, dest |-> r] \in msgsReceived[r]
\*                    /\ rmState' = [rmState EXCEPT ![r].step = "pre-commit"]
\*                    /\ SendMessage([ type |-> "pre-commit", src |-> r, dest |-> coordinator ])

(***************************************************************************
Commit Actions
 ***************************************************************************)

\*StartCommit ==  /\ coordinator.step = "pre-commit"
\*                /\ rmState' = [rmState EXCEPT ![coordinator].step = "commit"]
\*                /\ ReceivedEveryMessage("pre-commit") 
\*
\*SendCommit(r) ==    /\ coordinator.step = "commit"
\*                    /\ ~ HasSentEveryMessageRound("commit") 
\*                    /\ r # coordinator
\*                    /\ SendMessage([ type |-> "commit", src |-> coordinator, dest |-> r ])
\*                    
\*                    

(***************************************************************************
Spec
 ***************************************************************************)
             
Next == IF ~ \E r \in RM: rmState[r].role /= "coordinator"
        THEN
           /\ UpgradeToCoordinator
        ELSE
            \/ \E r \in RM: \/ SendPrepare(r)
                            \/ Prepare(r)
                            \/ StartPre_commit
                            \/ finish
                            \/ BeginTransaction
            \/ DeliverMessage

TypeInv == /\ \A r \in RM: rmState = [rmState EXCEPT ![r].step = "done"]

Spec == Init /\ [][Next]_<<>>

THEOREM Spec => TypeInv

=============================================================================
\* Modification History
\* Last modified Sun Oct 08 19:02:01 WEST 2023 by monkey
\* Created Fri Oct 06 12:09:27 WEST 2023 by monkey

