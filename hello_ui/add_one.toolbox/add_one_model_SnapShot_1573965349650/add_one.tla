----MODULE add_one----

EXTENDS Integers
VARIABLES i, program_counter

Init == (program_counter = "start") /\ (i=0)

Pick == /\ program_counter = "start"
        /\ i' \in 0..1000
        /\ program_counter' = "middle"

Add1 == /\ program_counter = "middle"
        /\ i' = i + 1
        /\ program_counter' = "done"

Next == Pick \/ Add1

====
