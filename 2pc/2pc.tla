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
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
  msgs           \* messages.

vars == <<rmState, tmState, tmPrepared, msgs>>

Message ==
  [type : {"Prepared", "Aborted"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
   

TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message


TPInit ==   
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}

-----------------------------------------------------------------------------

TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>


TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>


TMAbort(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Aborted", rm |-> rm] \in msgs
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>


RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

  
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ msgs' = msgs \cup {[type |-> "Aborted", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>


RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


TPNext ==
  \/ TMCommit
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm) \/ TMAbort(rm)

-----------------------------------------------------------------------------
Fairness == /\ WF_vars(TMCommit) /\ (\A rm \in RM : SF_vars(TMAbort(rm)))

TPSpec == TPInit /\ [][TPNext]_vars /\ Fairness


(* AC1 (agreement): Any two processes that decide, decide the same value                                                        *)
TPAgreement ==  
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"              


(* AC2 (validity, part 1): If some process starts with the value “no” then “abort” is the only possible decision                *)
TPValidity1 ==
\*  tmState = "aborted" => \E rm \in RM : rmState[rm] = "aborted"
    (\E rm \in RM : rmState[rm] = "aborted") ~> (tmState = "aborted")
  

(* AC3 (validity, part 2): If all processes start with value “yes” and none fails, then “commit” is the only possible decision  *)
TPValidity2 ==
\*  ~ (\E rm \in RM : rmState[rm] = "aborted" \/ rmState[rm] = "working")
\*        => tmState = "committed" \/ tmState = "init"
  ~ (\E rm \in RM : rmState[rm] /= "prepared") ~> (tmState = "committed")
  

(* AC4 (termination): If eventually all processes recover from all faults, then, eventually all processes decide                *)


THEOREM TPSpec => []TPTypeOK
THEOREM TPSpec => []TPAgreement
THEOREM TPSpec => TPValidity1
THEOREM TPSpec => TPValidity2
-----------------------------------------------------------------------------
=============================================================================
\* Modification History
\* Last modified Mon Oct 09 21:04:47 WEST 2023 by andre
\* Created Mon Oct 09 17:26:32 WEST 2023 by andre
