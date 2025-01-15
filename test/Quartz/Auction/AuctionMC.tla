---- MODULE AuctionMC ----
EXTENDS Auction, TLC
__max_call_depth == 3
__max_int == 3
__max_timestep == 3
__min_int == 0
__max_elapsed_time == 5
__property_0 == [](balance >= 0)
__property_1 == [](<>((__currentState = CLOSED)))
__property_2 == [](__max_bid_tokens >= 0)
__property_3 == []((__currentState = OPEN) => (HighestBid >= __max_bid_tokens))
__property_4 == [](MapSum(Balances) >= 0)
__constraint_0 == __contractCallDepth <= __max_call_depth
__constraint_1 == __currentTime <= __max_elapsed_time
==========