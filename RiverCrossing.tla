---------------------- MODULE RiverCrossing ----------------------
EXTENDS Integers, FiniteSets

VARIABLES curr_dock, who_is_on_dock, who_is_on_boat, docking_or_not

TypeOK == /\ curr_dock \in {"E","W"}
          /\ Cardinality(who_is_on_boat) \in {0,1,2}
          /\ who_is_on_boat \in SUBSET ({"Fox", "Chicken", "Corn"})
          /\ who_is_on_dock \in 
                [{"E","W"} -> SUBSET ({"Fox", "Chicken", "Corn"})]
                                          
Termination == Cardinality(who_is_on_dock["W"]) < 3

Init == /\ curr_dock = "E"
        /\ who_is_on_boat = {}
        /\ docking_or_not = 1
        /\ who_is_on_dock = [i \in {"E","W"} |-> 
                               IF i = "E" THEN {"Fox", "Chicken", "Corn"}
                                          ELSE  {} ]

              
IsSafe(S) == \/ S \subseteq {"Fox", "Corn"}
             \/ Cardinality(S) \in {0,1,3}

OtherDock(b) == IF b = "E" THEN "W" ELSE "E"

(* If on the boat (0), dock (1)             *)
(* If on the dock (1), get on the boat (0). *)
SwitchBoatOrDock(d) == 1 - d

Undock(S, b) == /\ LET newOldDock == who_is_on_dock[b] (* Dock where they are not docking *)
                       newNewDock == who_is_on_dock[OtherDock(b)] \cup S (* Dock where they are docking *)
                       newBoat    == who_is_on_boat \ S
                  IN /\ curr_dock' = OtherDock(b)
                     /\ IsSafe(newOldDock)
                     /\ IsSafe(newNewDock)
                     /\ who_is_on_dock' = 
                        [i \in {"E","W"} |->
                            IF i = b
                                THEN newOldDock 
                                ELSE newNewDock]
                     /\ who_is_on_boat' = newBoat

Dock(S, b) == /\ LET newOldDock == who_is_on_dock[b] \ S (* Dock where they are docking *)
                     newNewDock == who_is_on_dock[OtherDock(b)] (* Dock where they are not docking *)
                     newBoat    == who_is_on_boat \cup S
                 IN  /\ curr_dock' = b
                     /\ IsSafe(newOldDock)
                     /\ IsSafe(newNewDock)
                     /\ who_is_on_dock' = 
                        [i \in {"E","W"} |->
                            IF i = b
                                THEN newOldDock 
                                ELSE newNewDock]
                     /\ who_is_on_boat' = newBoat

Next == /\ docking_or_not' = SwitchBoatOrDock(docking_or_not)
        /\ IF docking_or_not = 1 
            THEN \E S \in SUBSET who_is_on_dock[curr_dock] :
                    /\ Cardinality(S) =< 2 - Cardinality(who_is_on_boat)               
                    /\ Dock(S, curr_dock)
            ELSE \E S \in SUBSET who_is_on_boat :
                    /\ Undock(S, curr_dock)
            

=============================================================================
\* Modification History
\* Last modified Sun Oct 08 12:10:40 WEST 2023 by andre
\* Last modified Sat Oct 07 16:46:55 WEST 2023 by andre
