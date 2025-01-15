---- MODULE VotingMC ----
EXTENDS Voting, TLC
__max_call_depth == 3
__max_int == 5
__max_timestep == 3
__min_int == -5
__max_elapsed_time == 11
__property_0 == []((Winner >= 0) /\ (Winner <= Options))
__constraint_0 == __contractCallDepth <= __max_call_depth
__constraint_1 == __currentTime <= __max_elapsed_time
==========