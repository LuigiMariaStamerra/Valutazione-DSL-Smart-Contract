-----MODULE Auction-----
EXTENDS Integers, Sequences, TLC
CONSTANTS MAX_INT, MIN_INT, MAX_TIMESTEP, MAX_ELAPSED_TIME, MAX_CALL_DEPTH
CONSTANTS OPEN, CLOSED, ABORTED
STATES == { OPEN, CLOSED, ABORTED }
CONSTANTS ZERO_IDENT, __ident1, __ident2, __ident3
IDENTITIES == { ZERO_IDENT, __ident1, __ident2, __ident3 }


RECURSIVE SeqSum(_)
SeqSum(S) == IF S = <<>> THEN 0 ELSE Head(S) + SeqSum(Tail(S))

RECURSIVE MapSum(_)
MapSum(M) == IF DOMAIN M = {} THEN 0 ELSE
             LET x == CHOOSE x \in DOMAIN M: TRUE
             IN M[x] + MapSum([ y \in  (DOMAIN M \ {x}) |-> M[y] ])

(* --fair algorithm Auction
variables __currentState = OPEN;
    __currentTime = 0;
    __contractCallDepth = 0;
    balance = 0;
    __temporary = 0;
    Auctioneer = ZERO_IDENT;
    Beneficiary = ZERO_IDENT;
    HighestBidder = ZERO_IDENT;
    HighestBid = 0;
    EndTime = 0;
    Balances = [ x \in IDENTITIES \ {ZERO_IDENT} |-> 0 ];
    __max_bid_tokens = MIN_INT;
    __stateStash = [
        Auctioneer |-> Auctioneer,
        Beneficiary |-> Beneficiary,
        HighestBidder |-> HighestBidder,
        HighestBid |-> HighestBid,
        EndTime |-> EndTime,
        Balances |-> Balances,
        balance |-> balance,
        __currentState |-> __currentState
    ];

    procedure initialize(sender, initialize_beneficiary, initialize_duration) begin initialize:
        __currentState := OPEN;
        Beneficiary := initialize_beneficiary ||
        HighestBid := 0 ||
        EndTime := __currentTime + initialize_duration ||
        Auctioneer := sender;
        return;
    end procedure;

    procedure bid(sender, bid_tokens) begin bid:
        if __currentState /= OPEN then
            return;
        end if;
L0:
        if ~(bid_tokens > HighestBid) then
            return;
        end if;
L1:
        balance := balance + bid_tokens;
        if bid_tokens > __max_bid_tokens then
            __max_bid_tokens := bid_tokens
        end if;
        HighestBid := bid_tokens ||
        HighestBidder := sender ||
        Balances[HighestBidder] := Balances[HighestBidder] + HighestBid;
L2:
        return;
    end procedure;

    procedure withdrawOpen(sender) begin withdrawOpen:
        if __currentState /= OPEN then
            return;
        end if;
L3:
        if ~(Balances[sender] > 0) then
            return;
        end if;
L4:
        if (sender = HighestBidder) /\ ((Balances[sender] - HighestBid) > 0) then
            __temporary := Balances[sender] - HighestBid;
            Balances[sender] := Balances[sender] - __temporary;
            call sendTokens(sender, __temporary);
        end if;
L6:
        return;
    end procedure;

    procedure withdrawClosed(sender) begin withdrawClosed:
        if __currentState /= CLOSED then
            return;
        end if;
L7:
        if ~(Balances[sender] > 0) then
            return;
        end if;
L8:
        __temporary := Balances[sender];
        Balances[sender] := Balances[sender] - __temporary;
        call sendTokens(sender, __temporary);
L9:
        return;
    end procedure;

    procedure withdrawAborted(sender) begin withdrawAborted:
        if __currentState /= ABORTED then
            return;
        end if;
L10:
        if ~(Balances[sender] > 0) then
            return;
        end if;
L11:
        __temporary := Balances[sender];
        Balances[sender] := Balances[sender] - __temporary;
        call sendTokens(sender, __temporary);
L12:
        return;
    end procedure;

    procedure accept(sender) begin accept:
        if __currentState /= OPEN then
            return;
        end if;
L13:
        if ~(__currentTime > EndTime) then
            return;
        end if;
L14:
        if sender /= Beneficiary then
            return;
        end if;
L15:
        __currentState := CLOSED;
        __temporary := HighestBid;
        HighestBid := HighestBid - __temporary;
        call sendTokens(sender, __temporary);
        return;
    end procedure;

    procedure reject(sender) begin reject:
        if __currentState /= OPEN then
            return;
        end if;
L16:
        if ~(__currentTime > EndTime) then
            return;
        end if;
L17:
        if sender /= Beneficiary then
            return;
        end if;
L18:
        __currentState := CLOSED;
        __temporary := HighestBid;
        HighestBid := HighestBid - __temporary;
        call sendTokens(HighestBidder, __temporary);
        return;
    end procedure;

    procedure abort(sender) begin abort:
        if __currentState /= OPEN then
            return;
        end if;
L19:
        if sender /= Auctioneer then
            return;
        end if;
L20:
        __currentState := ABORTED;
        return;
    end procedure;

    procedure invokeContract(sender) begin InvokeContract:
        if __contractCallDepth = 0 then
            __stateStash := [
                Auctioneer |-> Auctioneer,
                Beneficiary |-> Beneficiary,
                HighestBidder |-> HighestBidder,
                HighestBid |-> HighestBid,
                EndTime |-> EndTime,
                Balances |-> Balances,
                balance |-> balance,
                __currentState |-> __currentState
            ];
        end if;
        __contractCallDepth := __contractCallDepth + 1;
        if __contractCallDepth < 2 then
            with __timeDelta \in 1..MAX_TIMESTEP do
                __currentTime := __currentTime + __timeDelta;
            end with;
        end if;
MethodCall:
        either
            with bid_tokens_arg \in 0..MAX_INT do
                call bid(sender, bid_tokens_arg);
            end with;
        or
            call withdrawOpen(sender);
        or
            call withdrawClosed(sender);
        or
            call withdrawAborted(sender);
        or
            call accept(sender);
        or
            call reject(sender);
        or
            call abort(sender);
        end either;
L21:
        __contractCallDepth := __contractCallDepth - 1;
        return;
    end procedure;

    procedure sendTokens(recipient, amount) begin SendTokens:
        balance := balance - amount;
SendInvocation:
        either
            call throw();
        or
            skip;
        end either;
L22:
        return;
    end procedure;

    procedure throw() begin Throw:
        Auctioneer := __stateStash["Auctioneer"];
        Beneficiary := __stateStash["Beneficiary"];
        HighestBidder := __stateStash["HighestBidder"];
        HighestBid := __stateStash["HighestBid"];
        EndTime := __stateStash["EndTime"];
        Balances := __stateStash["Balances"];
        balance := __stateStash["balance"];
        __currentState := __stateStash["__currentState"];
        __contractCallDepth := 0;
        return;
    end procedure;

begin Main:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT}, initialize_beneficiary_arg \in IDENTITIES \ {ZERO_IDENT}, initialize_duration_arg \in 0..MAX_INT do
        call initialize(sender_arg, initialize_beneficiary_arg, initialize_duration_arg);
    end with;

Loop:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT} do
        call invokeContract(sender_arg);
    end with;
L23:
    goto Loop;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3e421f8c" /\ chksum(tla) = "ec53c1d1")
\* Label initialize of procedure initialize at line 43 col 9 changed to initialize_
\* Label bid of procedure bid at line 52 col 9 changed to bid_
\* Label withdrawOpen of procedure withdrawOpen at line 72 col 9 changed to withdrawOpen_
\* Label withdrawClosed of procedure withdrawClosed at line 90 col 9 changed to withdrawClosed_
\* Label withdrawAborted of procedure withdrawAborted at line 106 col 9 changed to withdrawAborted_
\* Label accept of procedure accept at line 122 col 9 changed to accept_
\* Label reject of procedure reject at line 142 col 9 changed to reject_
\* Label abort of procedure abort at line 162 col 9 changed to abort_
\* Parameter sender of procedure initialize at line 42 col 26 changed to sender_
\* Parameter sender of procedure bid at line 51 col 19 changed to sender_b
\* Parameter sender of procedure withdrawOpen at line 71 col 28 changed to sender_w
\* Parameter sender of procedure withdrawClosed at line 89 col 30 changed to sender_wi
\* Parameter sender of procedure withdrawAborted at line 105 col 31 changed to sender_wit
\* Parameter sender of procedure accept at line 121 col 22 changed to sender_a
\* Parameter sender of procedure reject at line 141 col 22 changed to sender_r
\* Parameter sender of procedure abort at line 161 col 21 changed to sender_ab
CONSTANT defaultInitValue
VARIABLES __currentState, __currentTime, __contractCallDepth, balance, 
          __temporary, Auctioneer, Beneficiary, HighestBidder, HighestBid, 
          EndTime, Balances, __max_bid_tokens, __stateStash, pc, stack, 
          sender_, initialize_beneficiary, initialize_duration, sender_b, 
          bid_tokens, sender_w, sender_wi, sender_wit, sender_a, sender_r, 
          sender_ab, sender, recipient, amount

vars == << __currentState, __currentTime, __contractCallDepth, balance, 
           __temporary, Auctioneer, Beneficiary, HighestBidder, HighestBid, 
           EndTime, Balances, __max_bid_tokens, __stateStash, pc, stack, 
           sender_, initialize_beneficiary, initialize_duration, sender_b, 
           bid_tokens, sender_w, sender_wi, sender_wit, sender_a, sender_r, 
           sender_ab, sender, recipient, amount >>

Init == (* Global variables *)
        /\ __currentState = OPEN
        /\ __currentTime = 0
        /\ __contractCallDepth = 0
        /\ balance = 0
        /\ __temporary = 0
        /\ Auctioneer = ZERO_IDENT
        /\ Beneficiary = ZERO_IDENT
        /\ HighestBidder = ZERO_IDENT
        /\ HighestBid = 0
        /\ EndTime = 0
        /\ Balances = [ x \in IDENTITIES \ {ZERO_IDENT} |-> 0 ]
        /\ __max_bid_tokens = MIN_INT
        /\ __stateStash =                [
                              Auctioneer |-> Auctioneer,
                              Beneficiary |-> Beneficiary,
                              HighestBidder |-> HighestBidder,
                              HighestBid |-> HighestBid,
                              EndTime |-> EndTime,
                              Balances |-> Balances,
                              balance |-> balance,
                              __currentState |-> __currentState
                          ]
        (* Procedure initialize *)
        /\ sender_ = defaultInitValue
        /\ initialize_beneficiary = defaultInitValue
        /\ initialize_duration = defaultInitValue
        (* Procedure bid *)
        /\ sender_b = defaultInitValue
        /\ bid_tokens = defaultInitValue
        (* Procedure withdrawOpen *)
        /\ sender_w = defaultInitValue
        (* Procedure withdrawClosed *)
        /\ sender_wi = defaultInitValue
        (* Procedure withdrawAborted *)
        /\ sender_wit = defaultInitValue
        (* Procedure accept *)
        /\ sender_a = defaultInitValue
        (* Procedure reject *)
        /\ sender_r = defaultInitValue
        (* Procedure abort *)
        /\ sender_ab = defaultInitValue
        (* Procedure invokeContract *)
        /\ sender = defaultInitValue
        (* Procedure sendTokens *)
        /\ recipient = defaultInitValue
        /\ amount = defaultInitValue
        /\ stack = << >>
        /\ pc = "Main"

initialize_ == /\ pc = "initialize_"
               /\ __currentState' = OPEN
               /\ /\ Auctioneer' = sender_
                  /\ Beneficiary' = initialize_beneficiary
                  /\ EndTime' = __currentTime + initialize_duration
                  /\ HighestBid' = 0
               /\ pc' = Head(stack).pc
               /\ sender_' = Head(stack).sender_
               /\ initialize_beneficiary' = Head(stack).initialize_beneficiary
               /\ initialize_duration' = Head(stack).initialize_duration
               /\ stack' = Tail(stack)
               /\ UNCHANGED << __currentTime, __contractCallDepth, balance, 
                               __temporary, HighestBidder, Balances, 
                               __max_bid_tokens, __stateStash, sender_b, 
                               bid_tokens, sender_w, sender_wi, sender_wit, 
                               sender_a, sender_r, sender_ab, sender, 
                               recipient, amount >>

initialize == initialize_

bid_ == /\ pc = "bid_"
        /\ IF __currentState /= OPEN
              THEN /\ pc' = Head(stack).pc
                   /\ sender_b' = Head(stack).sender_b
                   /\ bid_tokens' = Head(stack).bid_tokens
                   /\ stack' = Tail(stack)
              ELSE /\ pc' = "L0"
                   /\ UNCHANGED << stack, sender_b, bid_tokens >>
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Auctioneer, Beneficiary, 
                        HighestBidder, HighestBid, EndTime, Balances, 
                        __max_bid_tokens, __stateStash, sender_, 
                        initialize_beneficiary, initialize_duration, sender_w, 
                        sender_wi, sender_wit, sender_a, sender_r, sender_ab, 
                        sender, recipient, amount >>

L0 == /\ pc = "L0"
      /\ IF ~(bid_tokens > HighestBid)
            THEN /\ pc' = Head(stack).pc
                 /\ sender_b' = Head(stack).sender_b
                 /\ bid_tokens' = Head(stack).bid_tokens
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L1"
                 /\ UNCHANGED << stack, sender_b, bid_tokens >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Auctioneer, Beneficiary, 
                      HighestBidder, HighestBid, EndTime, Balances, 
                      __max_bid_tokens, __stateStash, sender_, 
                      initialize_beneficiary, initialize_duration, sender_w, 
                      sender_wi, sender_wit, sender_a, sender_r, sender_ab, 
                      sender, recipient, amount >>

L1 == /\ pc = "L1"
      /\ balance' = balance + bid_tokens
      /\ IF bid_tokens > __max_bid_tokens
            THEN /\ __max_bid_tokens' = bid_tokens
            ELSE /\ TRUE
                 /\ UNCHANGED __max_bid_tokens
      /\ /\ Balances' = [Balances EXCEPT ![HighestBidder] = Balances[HighestBidder] + HighestBid]
         /\ HighestBid' = bid_tokens
         /\ HighestBidder' = sender_b
      /\ pc' = "L2"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      __temporary, Auctioneer, Beneficiary, EndTime, 
                      __stateStash, stack, sender_, initialize_beneficiary, 
                      initialize_duration, sender_b, bid_tokens, sender_w, 
                      sender_wi, sender_wit, sender_a, sender_r, sender_ab, 
                      sender, recipient, amount >>

L2 == /\ pc = "L2"
      /\ pc' = Head(stack).pc
      /\ sender_b' = Head(stack).sender_b
      /\ bid_tokens' = Head(stack).bid_tokens
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Auctioneer, Beneficiary, 
                      HighestBidder, HighestBid, EndTime, Balances, 
                      __max_bid_tokens, __stateStash, sender_, 
                      initialize_beneficiary, initialize_duration, sender_w, 
                      sender_wi, sender_wit, sender_a, sender_r, sender_ab, 
                      sender, recipient, amount >>

bid == bid_ \/ L0 \/ L1 \/ L2

withdrawOpen_ == /\ pc = "withdrawOpen_"
                 /\ IF __currentState /= OPEN
                       THEN /\ pc' = Head(stack).pc
                            /\ sender_w' = Head(stack).sender_w
                            /\ stack' = Tail(stack)
                       ELSE /\ pc' = "L3"
                            /\ UNCHANGED << stack, sender_w >>
                 /\ UNCHANGED << __currentState, __currentTime, 
                                 __contractCallDepth, balance, __temporary, 
                                 Auctioneer, Beneficiary, HighestBidder, 
                                 HighestBid, EndTime, Balances, 
                                 __max_bid_tokens, __stateStash, sender_, 
                                 initialize_beneficiary, initialize_duration, 
                                 sender_b, bid_tokens, sender_wi, sender_wit, 
                                 sender_a, sender_r, sender_ab, sender, 
                                 recipient, amount >>

L3 == /\ pc = "L3"
      /\ IF ~(Balances[sender_w] > 0)
            THEN /\ pc' = Head(stack).pc
                 /\ sender_w' = Head(stack).sender_w
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L4"
                 /\ UNCHANGED << stack, sender_w >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Auctioneer, Beneficiary, 
                      HighestBidder, HighestBid, EndTime, Balances, 
                      __max_bid_tokens, __stateStash, sender_, 
                      initialize_beneficiary, initialize_duration, sender_b, 
                      bid_tokens, sender_wi, sender_wit, sender_a, sender_r, 
                      sender_ab, sender, recipient, amount >>

L4 == /\ pc = "L4"
      /\ IF (sender_w = HighestBidder) /\ ((Balances[sender_w] - HighestBid) > 0)
            THEN /\ __temporary' = Balances[sender_w] - HighestBid
                 /\ Balances' = [Balances EXCEPT ![sender_w] = Balances[sender_w] - __temporary']
                 /\ /\ amount' = __temporary'
                    /\ recipient' = sender_w
                    /\ stack' = << [ procedure |->  "sendTokens",
                                     pc        |->  "L6",
                                     recipient |->  recipient,
                                     amount    |->  amount ] >>
                                 \o stack
                 /\ pc' = "SendTokens"
            ELSE /\ pc' = "L6"
                 /\ UNCHANGED << __temporary, Balances, stack, recipient, 
                                 amount >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, Auctioneer, Beneficiary, HighestBidder, 
                      HighestBid, EndTime, __max_bid_tokens, __stateStash, 
                      sender_, initialize_beneficiary, initialize_duration, 
                      sender_b, bid_tokens, sender_w, sender_wi, sender_wit, 
                      sender_a, sender_r, sender_ab, sender >>

L6 == /\ pc = "L6"
      /\ pc' = Head(stack).pc
      /\ sender_w' = Head(stack).sender_w
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Auctioneer, Beneficiary, 
                      HighestBidder, HighestBid, EndTime, Balances, 
                      __max_bid_tokens, __stateStash, sender_, 
                      initialize_beneficiary, initialize_duration, sender_b, 
                      bid_tokens, sender_wi, sender_wit, sender_a, sender_r, 
                      sender_ab, sender, recipient, amount >>

withdrawOpen == withdrawOpen_ \/ L3 \/ L4 \/ L6

withdrawClosed_ == /\ pc = "withdrawClosed_"
                   /\ IF __currentState /= CLOSED
                         THEN /\ pc' = Head(stack).pc
                              /\ sender_wi' = Head(stack).sender_wi
                              /\ stack' = Tail(stack)
                         ELSE /\ pc' = "L7"
                              /\ UNCHANGED << stack, sender_wi >>
                   /\ UNCHANGED << __currentState, __currentTime, 
                                   __contractCallDepth, balance, __temporary, 
                                   Auctioneer, Beneficiary, HighestBidder, 
                                   HighestBid, EndTime, Balances, 
                                   __max_bid_tokens, __stateStash, sender_, 
                                   initialize_beneficiary, initialize_duration, 
                                   sender_b, bid_tokens, sender_w, sender_wit, 
                                   sender_a, sender_r, sender_ab, sender, 
                                   recipient, amount >>

L7 == /\ pc = "L7"
      /\ IF ~(Balances[sender_wi] > 0)
            THEN /\ pc' = Head(stack).pc
                 /\ sender_wi' = Head(stack).sender_wi
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L8"
                 /\ UNCHANGED << stack, sender_wi >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Auctioneer, Beneficiary, 
                      HighestBidder, HighestBid, EndTime, Balances, 
                      __max_bid_tokens, __stateStash, sender_, 
                      initialize_beneficiary, initialize_duration, sender_b, 
                      bid_tokens, sender_w, sender_wit, sender_a, sender_r, 
                      sender_ab, sender, recipient, amount >>

L8 == /\ pc = "L8"
      /\ __temporary' = Balances[sender_wi]
      /\ Balances' = [Balances EXCEPT ![sender_wi] = Balances[sender_wi] - __temporary']
      /\ /\ amount' = __temporary'
         /\ recipient' = sender_wi
         /\ stack' = << [ procedure |->  "sendTokens",
                          pc        |->  "L9",
                          recipient |->  recipient,
                          amount    |->  amount ] >>
                      \o stack
      /\ pc' = "SendTokens"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, Auctioneer, Beneficiary, HighestBidder, 
                      HighestBid, EndTime, __max_bid_tokens, __stateStash, 
                      sender_, initialize_beneficiary, initialize_duration, 
                      sender_b, bid_tokens, sender_w, sender_wi, sender_wit, 
                      sender_a, sender_r, sender_ab, sender >>

L9 == /\ pc = "L9"
      /\ pc' = Head(stack).pc
      /\ sender_wi' = Head(stack).sender_wi
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Auctioneer, Beneficiary, 
                      HighestBidder, HighestBid, EndTime, Balances, 
                      __max_bid_tokens, __stateStash, sender_, 
                      initialize_beneficiary, initialize_duration, sender_b, 
                      bid_tokens, sender_w, sender_wit, sender_a, sender_r, 
                      sender_ab, sender, recipient, amount >>

withdrawClosed == withdrawClosed_ \/ L7 \/ L8 \/ L9

withdrawAborted_ == /\ pc = "withdrawAborted_"
                    /\ IF __currentState /= ABORTED
                          THEN /\ pc' = Head(stack).pc
                               /\ sender_wit' = Head(stack).sender_wit
                               /\ stack' = Tail(stack)
                          ELSE /\ pc' = "L10"
                               /\ UNCHANGED << stack, sender_wit >>
                    /\ UNCHANGED << __currentState, __currentTime, 
                                    __contractCallDepth, balance, __temporary, 
                                    Auctioneer, Beneficiary, HighestBidder, 
                                    HighestBid, EndTime, Balances, 
                                    __max_bid_tokens, __stateStash, sender_, 
                                    initialize_beneficiary, 
                                    initialize_duration, sender_b, bid_tokens, 
                                    sender_w, sender_wi, sender_a, sender_r, 
                                    sender_ab, sender, recipient, amount >>

L10 == /\ pc = "L10"
       /\ IF ~(Balances[sender_wit] > 0)
             THEN /\ pc' = Head(stack).pc
                  /\ sender_wit' = Head(stack).sender_wit
                  /\ stack' = Tail(stack)
             ELSE /\ pc' = "L11"
                  /\ UNCHANGED << stack, sender_wit >>
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_a, sender_r, 
                       sender_ab, sender, recipient, amount >>

L11 == /\ pc = "L11"
       /\ __temporary' = Balances[sender_wit]
       /\ Balances' = [Balances EXCEPT ![sender_wit] = Balances[sender_wit] - __temporary']
       /\ /\ amount' = __temporary'
          /\ recipient' = sender_wit
          /\ stack' = << [ procedure |->  "sendTokens",
                           pc        |->  "L12",
                           recipient |->  recipient,
                           amount    |->  amount ] >>
                       \o stack
       /\ pc' = "SendTokens"
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, Auctioneer, Beneficiary, HighestBidder, 
                       HighestBid, EndTime, __max_bid_tokens, __stateStash, 
                       sender_, initialize_beneficiary, initialize_duration, 
                       sender_b, bid_tokens, sender_w, sender_wi, sender_wit, 
                       sender_a, sender_r, sender_ab, sender >>

L12 == /\ pc = "L12"
       /\ pc' = Head(stack).pc
       /\ sender_wit' = Head(stack).sender_wit
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_a, sender_r, 
                       sender_ab, sender, recipient, amount >>

withdrawAborted == withdrawAborted_ \/ L10 \/ L11 \/ L12

accept_ == /\ pc = "accept_"
           /\ IF __currentState /= OPEN
                 THEN /\ pc' = Head(stack).pc
                      /\ sender_a' = Head(stack).sender_a
                      /\ stack' = Tail(stack)
                 ELSE /\ pc' = "L13"
                      /\ UNCHANGED << stack, sender_a >>
           /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                           balance, __temporary, Auctioneer, Beneficiary, 
                           HighestBidder, HighestBid, EndTime, Balances, 
                           __max_bid_tokens, __stateStash, sender_, 
                           initialize_beneficiary, initialize_duration, 
                           sender_b, bid_tokens, sender_w, sender_wi, 
                           sender_wit, sender_r, sender_ab, sender, recipient, 
                           amount >>

L13 == /\ pc = "L13"
       /\ IF ~(__currentTime > EndTime)
             THEN /\ pc' = Head(stack).pc
                  /\ sender_a' = Head(stack).sender_a
                  /\ stack' = Tail(stack)
             ELSE /\ pc' = "L14"
                  /\ UNCHANGED << stack, sender_a >>
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_r, 
                       sender_ab, sender, recipient, amount >>

L14 == /\ pc = "L14"
       /\ IF sender_a /= Beneficiary
             THEN /\ pc' = Head(stack).pc
                  /\ sender_a' = Head(stack).sender_a
                  /\ stack' = Tail(stack)
             ELSE /\ pc' = "L15"
                  /\ UNCHANGED << stack, sender_a >>
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_r, 
                       sender_ab, sender, recipient, amount >>

L15 == /\ pc = "L15"
       /\ __currentState' = CLOSED
       /\ __temporary' = HighestBid
       /\ HighestBid' = HighestBid - __temporary'
       /\ /\ amount' = __temporary'
          /\ recipient' = sender_a
          /\ stack' = << [ procedure |->  "sendTokens",
                           pc        |->  Head(stack).pc,
                           recipient |->  recipient,
                           amount    |->  amount ] >>
                       \o Tail(stack)
       /\ pc' = "SendTokens"
       /\ UNCHANGED << __currentTime, __contractCallDepth, balance, Auctioneer, 
                       Beneficiary, HighestBidder, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_r, sender_ab, sender >>

accept == accept_ \/ L13 \/ L14 \/ L15

reject_ == /\ pc = "reject_"
           /\ IF __currentState /= OPEN
                 THEN /\ pc' = Head(stack).pc
                      /\ sender_r' = Head(stack).sender_r
                      /\ stack' = Tail(stack)
                 ELSE /\ pc' = "L16"
                      /\ UNCHANGED << stack, sender_r >>
           /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                           balance, __temporary, Auctioneer, Beneficiary, 
                           HighestBidder, HighestBid, EndTime, Balances, 
                           __max_bid_tokens, __stateStash, sender_, 
                           initialize_beneficiary, initialize_duration, 
                           sender_b, bid_tokens, sender_w, sender_wi, 
                           sender_wit, sender_a, sender_ab, sender, recipient, 
                           amount >>

L16 == /\ pc = "L16"
       /\ IF ~(__currentTime > EndTime)
             THEN /\ pc' = Head(stack).pc
                  /\ sender_r' = Head(stack).sender_r
                  /\ stack' = Tail(stack)
             ELSE /\ pc' = "L17"
                  /\ UNCHANGED << stack, sender_r >>
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_ab, sender, recipient, amount >>

L17 == /\ pc = "L17"
       /\ IF sender_r /= Beneficiary
             THEN /\ pc' = Head(stack).pc
                  /\ sender_r' = Head(stack).sender_r
                  /\ stack' = Tail(stack)
             ELSE /\ pc' = "L18"
                  /\ UNCHANGED << stack, sender_r >>
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_ab, sender, recipient, amount >>

L18 == /\ pc = "L18"
       /\ __currentState' = CLOSED
       /\ __temporary' = HighestBid
       /\ HighestBid' = HighestBid - __temporary'
       /\ /\ amount' = __temporary'
          /\ recipient' = HighestBidder
          /\ stack' = << [ procedure |->  "sendTokens",
                           pc        |->  Head(stack).pc,
                           recipient |->  recipient,
                           amount    |->  amount ] >>
                       \o Tail(stack)
       /\ pc' = "SendTokens"
       /\ UNCHANGED << __currentTime, __contractCallDepth, balance, Auctioneer, 
                       Beneficiary, HighestBidder, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_r, sender_ab, sender >>

reject == reject_ \/ L16 \/ L17 \/ L18

abort_ == /\ pc = "abort_"
          /\ IF __currentState /= OPEN
                THEN /\ pc' = Head(stack).pc
                     /\ sender_ab' = Head(stack).sender_ab
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "L19"
                     /\ UNCHANGED << stack, sender_ab >>
          /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                          balance, __temporary, Auctioneer, Beneficiary, 
                          HighestBidder, HighestBid, EndTime, Balances, 
                          __max_bid_tokens, __stateStash, sender_, 
                          initialize_beneficiary, initialize_duration, 
                          sender_b, bid_tokens, sender_w, sender_wi, 
                          sender_wit, sender_a, sender_r, sender, recipient, 
                          amount >>

L19 == /\ pc = "L19"
       /\ IF sender_ab /= Auctioneer
             THEN /\ pc' = Head(stack).pc
                  /\ sender_ab' = Head(stack).sender_ab
                  /\ stack' = Tail(stack)
             ELSE /\ pc' = "L20"
                  /\ UNCHANGED << stack, sender_ab >>
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_r, sender, recipient, amount >>

L20 == /\ pc = "L20"
       /\ __currentState' = ABORTED
       /\ pc' = Head(stack).pc
       /\ sender_ab' = Head(stack).sender_ab
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentTime, __contractCallDepth, balance, 
                       __temporary, Auctioneer, Beneficiary, HighestBidder, 
                       HighestBid, EndTime, Balances, __max_bid_tokens, 
                       __stateStash, sender_, initialize_beneficiary, 
                       initialize_duration, sender_b, bid_tokens, sender_w, 
                       sender_wi, sender_wit, sender_a, sender_r, sender, 
                       recipient, amount >>

abort == abort_ \/ L19 \/ L20

InvokeContract == /\ pc = "InvokeContract"
                  /\ IF __contractCallDepth = 0
                        THEN /\ __stateStash' =                 [
                                                    Auctioneer |-> Auctioneer,
                                                    Beneficiary |-> Beneficiary,
                                                    HighestBidder |-> HighestBidder,
                                                    HighestBid |-> HighestBid,
                                                    EndTime |-> EndTime,
                                                    Balances |-> Balances,
                                                    balance |-> balance,
                                                    __currentState |-> __currentState
                                                ]
                        ELSE /\ TRUE
                             /\ UNCHANGED __stateStash
                  /\ __contractCallDepth' = __contractCallDepth + 1
                  /\ IF __contractCallDepth' < 2
                        THEN /\ \E __timeDelta \in 1..MAX_TIMESTEP:
                                  __currentTime' = __currentTime + __timeDelta
                        ELSE /\ TRUE
                             /\ UNCHANGED __currentTime
                  /\ pc' = "MethodCall"
                  /\ UNCHANGED << __currentState, balance, __temporary, 
                                  Auctioneer, Beneficiary, HighestBidder, 
                                  HighestBid, EndTime, Balances, 
                                  __max_bid_tokens, stack, sender_, 
                                  initialize_beneficiary, initialize_duration, 
                                  sender_b, bid_tokens, sender_w, sender_wi, 
                                  sender_wit, sender_a, sender_r, sender_ab, 
                                  sender, recipient, amount >>

MethodCall == /\ pc = "MethodCall"
              /\ \/ /\ \E bid_tokens_arg \in 0..MAX_INT:
                         /\ /\ bid_tokens' = bid_tokens_arg
                            /\ sender_b' = sender
                            /\ stack' = << [ procedure |->  "bid",
                                             pc        |->  "L21",
                                             sender_b  |->  sender_b,
                                             bid_tokens |->  bid_tokens ] >>
                                         \o stack
                         /\ pc' = "bid_"
                    /\ UNCHANGED <<sender_w, sender_wi, sender_wit, sender_a, sender_r, sender_ab>>
                 \/ /\ /\ sender_w' = sender
                       /\ stack' = << [ procedure |->  "withdrawOpen",
                                        pc        |->  "L21",
                                        sender_w  |->  sender_w ] >>
                                    \o stack
                    /\ pc' = "withdrawOpen_"
                    /\ UNCHANGED <<sender_b, bid_tokens, sender_wi, sender_wit, sender_a, sender_r, sender_ab>>
                 \/ /\ /\ sender_wi' = sender
                       /\ stack' = << [ procedure |->  "withdrawClosed",
                                        pc        |->  "L21",
                                        sender_wi |->  sender_wi ] >>
                                    \o stack
                    /\ pc' = "withdrawClosed_"
                    /\ UNCHANGED <<sender_b, bid_tokens, sender_w, sender_wit, sender_a, sender_r, sender_ab>>
                 \/ /\ /\ sender_wit' = sender
                       /\ stack' = << [ procedure |->  "withdrawAborted",
                                        pc        |->  "L21",
                                        sender_wit |->  sender_wit ] >>
                                    \o stack
                    /\ pc' = "withdrawAborted_"
                    /\ UNCHANGED <<sender_b, bid_tokens, sender_w, sender_wi, sender_a, sender_r, sender_ab>>
                 \/ /\ /\ sender_a' = sender
                       /\ stack' = << [ procedure |->  "accept",
                                        pc        |->  "L21",
                                        sender_a  |->  sender_a ] >>
                                    \o stack
                    /\ pc' = "accept_"
                    /\ UNCHANGED <<sender_b, bid_tokens, sender_w, sender_wi, sender_wit, sender_r, sender_ab>>
                 \/ /\ /\ sender_r' = sender
                       /\ stack' = << [ procedure |->  "reject",
                                        pc        |->  "L21",
                                        sender_r  |->  sender_r ] >>
                                    \o stack
                    /\ pc' = "reject_"
                    /\ UNCHANGED <<sender_b, bid_tokens, sender_w, sender_wi, sender_wit, sender_a, sender_ab>>
                 \/ /\ /\ sender_ab' = sender
                       /\ stack' = << [ procedure |->  "abort",
                                        pc        |->  "L21",
                                        sender_ab |->  sender_ab ] >>
                                    \o stack
                    /\ pc' = "abort_"
                    /\ UNCHANGED <<sender_b, bid_tokens, sender_w, sender_wi, sender_wit, sender_a, sender_r>>
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, balance, __temporary, 
                              Auctioneer, Beneficiary, HighestBidder, 
                              HighestBid, EndTime, Balances, __max_bid_tokens, 
                              __stateStash, sender_, initialize_beneficiary, 
                              initialize_duration, sender, recipient, amount >>

L21 == /\ pc = "L21"
       /\ __contractCallDepth' = __contractCallDepth - 1
       /\ pc' = Head(stack).pc
       /\ sender' = Head(stack).sender
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentState, __currentTime, balance, __temporary, 
                       Auctioneer, Beneficiary, HighestBidder, HighestBid, 
                       EndTime, Balances, __max_bid_tokens, __stateStash, 
                       sender_, initialize_beneficiary, initialize_duration, 
                       sender_b, bid_tokens, sender_w, sender_wi, sender_wit, 
                       sender_a, sender_r, sender_ab, recipient, amount >>

invokeContract == InvokeContract \/ MethodCall \/ L21

SendTokens == /\ pc = "SendTokens"
              /\ balance' = balance - amount
              /\ pc' = "SendInvocation"
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, __temporary, Auctioneer, 
                              Beneficiary, HighestBidder, HighestBid, EndTime, 
                              Balances, __max_bid_tokens, __stateStash, stack, 
                              sender_, initialize_beneficiary, 
                              initialize_duration, sender_b, bid_tokens, 
                              sender_w, sender_wi, sender_wit, sender_a, 
                              sender_r, sender_ab, sender, recipient, amount >>

SendInvocation == /\ pc = "SendInvocation"
                  /\ \/ /\ stack' = << [ procedure |->  "throw",
                                         pc        |->  "L22" ] >>
                                     \o stack
                        /\ pc' = "Throw"
                     \/ /\ TRUE
                        /\ pc' = "L22"
                        /\ stack' = stack
                  /\ UNCHANGED << __currentState, __currentTime, 
                                  __contractCallDepth, balance, __temporary, 
                                  Auctioneer, Beneficiary, HighestBidder, 
                                  HighestBid, EndTime, Balances, 
                                  __max_bid_tokens, __stateStash, sender_, 
                                  initialize_beneficiary, initialize_duration, 
                                  sender_b, bid_tokens, sender_w, sender_wi, 
                                  sender_wit, sender_a, sender_r, sender_ab, 
                                  sender, recipient, amount >>

L22 == /\ pc = "L22"
       /\ pc' = Head(stack).pc
       /\ recipient' = Head(stack).recipient
       /\ amount' = Head(stack).amount
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_r, sender_ab, sender >>

sendTokens == SendTokens \/ SendInvocation \/ L22

Throw == /\ pc = "Throw"
         /\ Auctioneer' = __stateStash["Auctioneer"]
         /\ Beneficiary' = __stateStash["Beneficiary"]
         /\ HighestBidder' = __stateStash["HighestBidder"]
         /\ HighestBid' = __stateStash["HighestBid"]
         /\ EndTime' = __stateStash["EndTime"]
         /\ Balances' = __stateStash["Balances"]
         /\ balance' = __stateStash["balance"]
         /\ __currentState' = __stateStash["__currentState"]
         /\ __contractCallDepth' = 0
         /\ pc' = "Loop"
         /\ stack' = <<>>
         /\ UNCHANGED << __currentTime, __temporary, __max_bid_tokens, 
                         __stateStash, sender_, initialize_beneficiary, 
                         initialize_duration, sender_b, bid_tokens, sender_w, 
                         sender_wi, sender_wit, sender_a, sender_r, sender_ab, 
                         sender, recipient, amount >>

throw == Throw

Main == /\ pc = "Main"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             \E initialize_beneficiary_arg \in IDENTITIES \ {ZERO_IDENT}:
               \E initialize_duration_arg \in 0..MAX_INT:
                 /\ /\ initialize_beneficiary' = initialize_beneficiary_arg
                    /\ initialize_duration' = initialize_duration_arg
                    /\ sender_' = sender_arg
                    /\ stack' = << [ procedure |->  "initialize",
                                     pc        |->  "Loop",
                                     sender_   |->  sender_,
                                     initialize_beneficiary |->  initialize_beneficiary,
                                     initialize_duration |->  initialize_duration ] >>
                                 \o stack
                 /\ pc' = "initialize_"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Auctioneer, Beneficiary, 
                        HighestBidder, HighestBid, EndTime, Balances, 
                        __max_bid_tokens, __stateStash, sender_b, bid_tokens, 
                        sender_w, sender_wi, sender_wit, sender_a, sender_r, 
                        sender_ab, sender, recipient, amount >>

Loop == /\ pc = "Loop"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             /\ /\ sender' = sender_arg
                /\ stack' = << [ procedure |->  "invokeContract",
                                 pc        |->  "L23",
                                 sender    |->  sender ] >>
                             \o stack
             /\ pc' = "InvokeContract"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Auctioneer, Beneficiary, 
                        HighestBidder, HighestBid, EndTime, Balances, 
                        __max_bid_tokens, __stateStash, sender_, 
                        initialize_beneficiary, initialize_duration, sender_b, 
                        bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                        sender_r, sender_ab, recipient, amount >>

L23 == /\ pc = "L23"
       /\ pc' = "Loop"
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Auctioneer, Beneficiary, 
                       HighestBidder, HighestBid, EndTime, Balances, 
                       __max_bid_tokens, __stateStash, stack, sender_, 
                       initialize_beneficiary, initialize_duration, sender_b, 
                       bid_tokens, sender_w, sender_wi, sender_wit, sender_a, 
                       sender_r, sender_ab, sender, recipient, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == initialize \/ bid \/ withdrawOpen \/ withdrawClosed
           \/ withdrawAborted \/ accept \/ reject \/ abort \/ invokeContract
           \/ sendTokens \/ throw \/ Main \/ Loop \/ L23
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
========
