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

RMState == [ state: { "working"}, step: {"working", "prepare", "pre-commit", "commit", "done", "aborted"} ]
 
Init ==     /\ rmState = [ r \in RM |-> [ state |-> "working", step |-> "working"  ] ]
            /\ msgsInTransit = {}
            /\ msgsReceived = [ r \in RM |-> {} ]
            /\ msgs = {}
            /\ coordinator = RandomElement(RM)
            
TypeOK == /\ msgs \subseteq Message
          /\ msgsInTransit \subseteq Message
          /\ \A r \in RM: rmState[r] \in RMState
          /\ coordinator \in RM
          /\ \A r \in RM: msgsReceived[r] \subseteq Message
          
(***************************************************************************
Auxiliar Functions
 ***************************************************************************)

HasSentEveryMessageRound(type) == IF Cardinality({ msg \in msgs: /\ msg.type /= type /\ msg.src /= coordinator}) = Len(rmState) - 1
                                    THEN
                                        TRUE
                                    ELSE
                                        FALSE
                                                    

ReceivedEveryMessage(type) == IF Cardinality({ msg \in msgsReceived[coordinator]: msg.type /= type }) = Cardinality(RM) -1 
                                THEN
                                    TRUE
                                ELSE
                                    FALSE
            

(***************************************************************************
Message Handling Actions
 ***************************************************************************)

SendMessage(msg) == /\ msg \notin msgs
                    /\ msg \notin msgsInTransit
                    /\ msgs' = msgs \union {msg}
                    /\ msgsInTransit' = msgsInTransit \union {msg}

DeliverMessage == IF Cardinality(msgsInTransit) > 0 
                        THEN
                            LET msg == RandomElement(msgsInTransit) IN
                                /\ msgsInTransit' = msgsInTransit \union {msg}
                                /\ msgsReceived' = [msgsReceived EXCEPT ![msg.dest] = @ \union {msg}]
                                /\ UNCHANGED<<rmState,coordinator, msgs>>
                        ELSE
                            UNCHANGED<<msgsInTransit, msgs, msgsReceived, rmState, coordinator>>


(***************************************************************************
Coordinator Functions
 ***************************************************************************)



(***************************************************************************
Prepare Actions
 ***************************************************************************)

SendPrepare(r) ==   /\ rmState[coordinator].step = "working"
                    /\ rmState' = [rmState EXCEPT ![r].step = "prepare"]
                    /\ r # coordinator
                    /\ ~ HasSentEveryMessageRound("prepare") 
                    /\ SendMessage([ type |-> "prepare", src |-> coordinator, dest |-> r ])
                    /\ UNCHANGED<<msgsReceived, coordinator>>


Prepare(r) == /\ rmState[r].state = "working"
              /\ rmState[r].step = "working"
              /\ {[ type |-> "prepare", src |-> coordinator, dest |-> r]} \subseteq msgsReceived[r]
              /\ rmState' = [rmState EXCEPT ![r].step = "prepare"]
              /\ SendMessage([ type |-> "prepared", src |-> r, dest |-> coordinator ])
              /\ UNCHANGED<<msgsReceived, coordinator>>
              
              
(***************************************************************************
Pre-commit Actions
 ***************************************************************************)

StartPre_commit ==  /\ rmState[coordinator].step /= "prepare"
                    /\ ReceivedEveryMessage("prepared")
                    /\ rmState' = [rmState EXCEPT ![coordinator].step = "pre-commit"]
                    /\ UNCHANGED<<msgs, msgsReceived, msgsInTransit, coordinator>>

SendPre_commit(r) ==    /\ rmState[coordinator].step = "pre-commit"
                        /\ ~ HasSentEveryMessageRound("pre-commit") 
                        /\ r # coordinator
                        /\ SendMessage([ type |-> "pre-commit", src |-> coordinator, dest |-> r ])
                        /\ UNCHANGED<<msgsReceived, coordinator, rmState>>

Pre_commit(r) ==    /\ rmState[r].state /= "working"
                    /\ r # coordinator
                    /\ rmState[r].step /= "prepare"
                    /\ [ type |-> "pre-commit", src |-> coordinator, dest |-> r] \in msgsReceived[r]
                    /\ rmState' = [rmState EXCEPT ![r].step = "pre-commit"]
                    /\ SendMessage([ type |-> "pre-commit", src |-> r, dest |-> coordinator ])
                    /\ UNCHANGED<<coordinator, msgsReceived>>

(***************************************************************************
Commit Actions
 ***************************************************************************)

StartCommit ==  /\ rmState[coordinator].step /= "pre-commit"
                /\ rmState' = [rmState EXCEPT ![coordinator].step = "commit"]
                /\ ReceivedEveryMessage("pre-commit") 
                /\ UNCHANGED<<coordinator, msgs, msgsInTransit, msgsReceived>>

SendCommit(r) ==    /\ rmState[coordinator].step /= "commit"
                    /\ ~ HasSentEveryMessageRound("commit") 
                    /\ r # coordinator
                    /\ SendMessage([ type |-> "commit", src |-> coordinator, dest |-> r ])
                    /\ UNCHANGED<<coordinator, msgsReceived, rmState>>
                    

(***************************************************************************
Spec
 ***************************************************************************)
                    
finish == /\ rmState[coordinator].step = "commit"
          /\ \A a \in RM: rmState' = [rmState EXCEPT ![a].step = "done"]
          /\ UNCHANGED<<msgs, msgsReceived, msgsInTransit, coordinator>>
             
Next == \/ ( \E r \in RM:  \/ SendPrepare(r)
                            \/ Prepare(r)
                            \/ SendPre_commit(r)
                            \/ Pre_commit(r) )
                            \/ finish
                            \/ DeliverMessage
                            \/ StartPre_commit

TypeInv == \A r \in RM: rmState[r].step /= "done"

Spec == Init /\ [][Next]_<<rmState, msgs, msgsInTransit, msgsReceived, coordinator>>

THEOREM Spec => TypeInv

=============================================================================
\* Modification History
\* Last modified Mon Oct 09 12:35:54 WEST 2023 by monkey
\* Created Fri Oct 06 12:09:27 WEST 2023 by monkey

