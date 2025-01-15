---- MODULE TokenMC ----
EXTENDS Token, TLC
__max_call_depth == 3
__max_int == 5
__max_timestep == 3
__min_int == -5
__max_elapsed_time == 11
__property_0 == [](TotalSupply = MapSum(BalanceOf))
__property_1 == [](BalanceOf[NullAddress] = 0)
__property_2 == [](TotalSupply >= 0)
__constraint_0 == __contractCallDepth <= __max_call_depth
__constraint_1 == __currentTime <= __max_elapsed_time
==========