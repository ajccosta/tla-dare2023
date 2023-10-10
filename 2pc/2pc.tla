-------------------------------- MODULE 2pc --------------------------------

(***************************************************************************)
(* This spec. does not have:                                               *)
(*      abort messages -- DONE: TM can no longer abort if no one aborts    *)
(*      liveness properties                                                *)
(*      message loss                                                       *)
(***************************************************************************)

CONSTANT RM \* The set of resource managers


VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  rmPrevState,   \* The state $rmState[rm]$ was previously in before crashing
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
  msgs           \* messages.

vars == <<rmState, rmPrevState, tmState, tmPrepared, msgs>>

Message ==
  [type : {"Prepared", "Aborted"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
   

TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "crashed"}]
  /\ rmPrevState \in [RM -> {"working", "prepared", "committed", "aborted", "crashed"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message


TPInit ==   
  /\ rmState = [rm \in RM |-> "working"]
  /\ rmPrevState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}

-----------------------------------------------------------------------------

TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs, rmPrevState>>


TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmPrevState>>


TMAbort(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Aborted", rm |-> rm] \in msgs
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmPrevState>>


RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, rmPrevState>>

  
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ msgs' = msgs \cup {[type |-> "Aborted", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, rmPrevState>>


RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmPrevState>>


RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmPrevState>>


RMCrash(rm) == 
  /\ rmState[rm] /= "crashed"
  /\ rmPrevState' = [rmPrevState EXCEPT ![rm] = rmState[rm]]
  /\ rmState' = [rmState EXCEPT ![rm] = "crashed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


RMRecover(rm) == 
  /\ rmState[rm] = "crashed"
  /\ rmState' = [rmState EXCEPT ![rm] = rmPrevState[rm]]
  /\ rmPrevState' = [rmPrevState EXCEPT ![rm] = "crashed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  

TPNext ==
  \/ TMCommit
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm) \/ TMAbort(rm)
         \/ RMCrash(rm) \/ RMRecover(rm)


-----------------------------------------------------------------------------
Fairness == 
            \* For validity 1 and 2:
            /\ WF_vars(TMCommit)
            /\ (\A rm \in RM: WF_vars(TMAbort(rm)))
            /\ (\A rm \in RM: WF_vars(TMRcvPrepared(rm)))
            \* For termination:
            /\ (\A rm \in RM: WF_vars(RMRcvAbortMsg(rm)))
            /\ (\A rm \in RM: WF_vars(RMRcvCommitMsg(rm)))
            /\ (\A rm \in RM: WF_vars(RMPrepare(rm)))
            

TPSpec == TPInit /\ [][TPNext]_vars /\ Fairness


(* AC1 (agreement): Any two processes that decide, decide the same value                                                        *)
TPAgreement ==
    \* No two processes can be in different decision states (i.e., decide different things)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"              


(* AC2 (validity, part 1): If some process starts with the value “no” then “abort” is the only possible decision                *)
TPValidity1 ==
\*  tmState = "aborted" => \E rm \in RM : rmState[rm] = "aborted"
    \* Translation: if any process is in aborted state (decided abort), then TM will eventually decide abort. 
    (\E rm \in RM : rmState[rm] = "aborted") ~> (tmState = "aborted")
  

(* AC3 (validity, part 2): If all processes start with value “yes” and none fails, then “commit” is the only possible decision  *)
TPValidity2 ==
\*  ~ (\E rm \in RM : rmState[rm] = "aborted" \/ rmState[rm] = "working")
\*        => tmState = "committed" \/ tmState = "init"
    \* Translation: if all processes are prepared, then eventually TM will decide commit. 
  ~ (\E rm \in RM : rmState[rm] /= "prepared") ~> (tmState = "committed")
  

(* AC4 (termination): If eventually all processes recover from all faults, then, eventually all processes decide                *)
TPTermination ==
    \* Translation: if eventually no process is crashed, then eventually all will decide (the same thing). 
    <>(~ (\E rm \in RM : rmState[rm] /= "working" /\ rmState[rm] /= "prepared" /\ rmState[rm] /= "aborted")) ~> 
        (~ (\E rm \in RM : rmState[rm] /= "aborted")) \/ (~ (\E rm \in RM : rmState[rm] /= "committed"))

THEOREM TPSpec => []TPTypeOK
THEOREM TPSpec => []TPAgreement
THEOREM TPSpec => TPValidity1
THEOREM TPSpec => TPValidity2
-----------------------------------------------------------------------------
=============================================================================
\* Modification History
\* Last modified Tue Oct 10 16:02:26 WEST 2023 by andre
\* Created Mon Oct 09 17:26:32 WEST 2023 by andre
