-----MODULE Voting-----
EXTENDS Integers, Sequences, TLC
CONSTANTS MAX_INT, MIN_INT, MAX_TIMESTEP, MAX_ELAPSED_TIME, MAX_CALL_DEPTH
CONSTANTS OPEN, CLOSED
STATES == { OPEN, CLOSED }
CONSTANTS ZERO_IDENT, __ident1, __ident2, __ident3
IDENTITIES == { ZERO_IDENT, __ident1, __ident2, __ident3 }


RECURSIVE SeqSum(_)
SeqSum(S) == IF S = <<>> THEN 0 ELSE Head(S) + SeqSum(Tail(S))

RECURSIVE MapSum(_)
MapSum(M) == IF DOMAIN M = {} THEN 0 ELSE
             LET x == CHOOSE x \in DOMAIN M: TRUE
             IN M[x] + MapSum([ y \in  (DOMAIN M \ {x}) |-> M[y] ])

(* --fair algorithm Voting
variables __currentState = OPEN;
    __currentTime = 0;
    __contractCallDepth = 0;
    balance = 0;
    __temporary = 0;
    Organizer = ZERO_IDENT;
    Options = 0;
    EndTime = 0;
    Voted = <<>>;
    Votes = [ x \in 0..MAX_INT |-> 0 ];
    Winner = 0;
    __stateStash = [
        Organizer |-> Organizer,
        Options |-> Options,
        EndTime |-> EndTime,
        Voted |-> Voted,
        Votes |-> Votes,
        Winner |-> Winner,
        balance |-> balance,
        __currentState |-> __currentState
    ];

    procedure initialize(sender, initialize_options, initialize_duration) begin initialize:
        __currentState := OPEN;
        Organizer := sender ||
        Options := initialize_options ||
        EndTime := __currentTime + initialize_duration;
        return;
    end procedure;

    procedure vote(sender, vote_option) begin vote:
        if __currentState /= OPEN then
            return;
        end if;
L0:
        if ~(((~(\E x \in DOMAIN Voted: Voted[x] = sender)) /\ (vote_option > 0)) /\ (vote_option <= Options)) then
            return;
        end if;
L1:
        Votes[vote_option] := Votes[vote_option] + 1 ||
        Voted := Append(Voted, sender);L2:
        if ((Winner /= 0) /\ (Votes[vote_option] > Votes[Winner])) \/ (Winner = 0) then
            Winner := vote_option;
        end if;
L3:
        return;
    end procedure;

    procedure close(sender) begin close:
        if __currentState /= OPEN then
            return;
        end if;
L4:
        if ~(__currentTime > EndTime) then
            return;
        end if;
L5:
        if sender /= Organizer then
            return;
        end if;
L6:
        __currentState := CLOSED;
        return;
    end procedure;

    procedure invokeContract(sender) begin InvokeContract:
        if __contractCallDepth = 0 then
            __stateStash := [
                Organizer |-> Organizer,
                Options |-> Options,
                EndTime |-> EndTime,
                Voted |-> Voted,
                Votes |-> Votes,
                Winner |-> Winner,
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
            with vote_option_arg \in 0..MAX_INT do
                call vote(sender, vote_option_arg);
            end with;
        or
            call close(sender);
        end either;
L7:
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
L8:
        return;
    end procedure;

    procedure throw() begin Throw:
        Organizer := __stateStash["Organizer"];
        Options := __stateStash["Options"];
        EndTime := __stateStash["EndTime"];
        Voted := __stateStash["Voted"];
        Votes := __stateStash["Votes"];
        Winner := __stateStash["Winner"];
        balance := __stateStash["balance"];
        __currentState := __stateStash["__currentState"];
        __contractCallDepth := 0;
        return;
    end procedure;

begin Main:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT}, initialize_options_arg \in 0..MAX_INT, initialize_duration_arg \in 0..MAX_INT do
        call initialize(sender_arg, initialize_options_arg, initialize_duration_arg);
    end with;

Loop:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT} do
        call invokeContract(sender_arg);
    end with;
L9:
    goto Loop;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c5b262ab" /\ chksum(tla) = "6a494fe5")
\* Label initialize of procedure initialize at line 42 col 9 changed to initialize_
\* Label vote of procedure vote at line 50 col 9 changed to vote_
\* Label close of procedure close at line 68 col 9 changed to close_
\* Parameter sender of procedure initialize at line 41 col 26 changed to sender_
\* Parameter sender of procedure vote at line 49 col 20 changed to sender_v
\* Parameter sender of procedure close at line 67 col 21 changed to sender_c
CONSTANT defaultInitValue
VARIABLES __currentState, __currentTime, __contractCallDepth, balance, 
          __temporary, Organizer, Options, EndTime, Voted, Votes, Winner, 
          __stateStash, pc, stack, sender_, initialize_options, 
          initialize_duration, sender_v, vote_option, sender_c, sender, 
          recipient, amount

vars == << __currentState, __currentTime, __contractCallDepth, balance, 
           __temporary, Organizer, Options, EndTime, Voted, Votes, Winner, 
           __stateStash, pc, stack, sender_, initialize_options, 
           initialize_duration, sender_v, vote_option, sender_c, sender, 
           recipient, amount >>

Init == (* Global variables *)
        /\ __currentState = OPEN
        /\ __currentTime = 0
        /\ __contractCallDepth = 0
        /\ balance = 0
        /\ __temporary = 0
        /\ Organizer = ZERO_IDENT
        /\ Options = 0
        /\ EndTime = 0
        /\ Voted = <<>>
        /\ Votes = [ x \in 0..MAX_INT |-> 0 ]
        /\ Winner = 0
        /\ __stateStash =                [
                              Organizer |-> Organizer,
                              Options |-> Options,
                              EndTime |-> EndTime,
                              Voted |-> Voted,
                              Votes |-> Votes,
                              Winner |-> Winner,
                              balance |-> balance,
                              __currentState |-> __currentState
                          ]
        (* Procedure initialize *)
        /\ sender_ = defaultInitValue
        /\ initialize_options = defaultInitValue
        /\ initialize_duration = defaultInitValue
        (* Procedure vote *)
        /\ sender_v = defaultInitValue
        /\ vote_option = defaultInitValue
        (* Procedure close *)
        /\ sender_c = defaultInitValue
        (* Procedure invokeContract *)
        /\ sender = defaultInitValue
        (* Procedure sendTokens *)
        /\ recipient = defaultInitValue
        /\ amount = defaultInitValue
        /\ stack = << >>
        /\ pc = "Main"

initialize_ == /\ pc = "initialize_"
               /\ __currentState' = OPEN
               /\ /\ EndTime' = __currentTime + initialize_duration
                  /\ Options' = initialize_options
                  /\ Organizer' = sender_
               /\ pc' = Head(stack).pc
               /\ sender_' = Head(stack).sender_
               /\ initialize_options' = Head(stack).initialize_options
               /\ initialize_duration' = Head(stack).initialize_duration
               /\ stack' = Tail(stack)
               /\ UNCHANGED << __currentTime, __contractCallDepth, balance, 
                               __temporary, Voted, Votes, Winner, __stateStash, 
                               sender_v, vote_option, sender_c, sender, 
                               recipient, amount >>

initialize == initialize_

vote_ == /\ pc = "vote_"
         /\ IF __currentState /= OPEN
               THEN /\ pc' = Head(stack).pc
                    /\ sender_v' = Head(stack).sender_v
                    /\ vote_option' = Head(stack).vote_option
                    /\ stack' = Tail(stack)
               ELSE /\ pc' = "L0"
                    /\ UNCHANGED << stack, sender_v, vote_option >>
         /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                         balance, __temporary, Organizer, Options, EndTime, 
                         Voted, Votes, Winner, __stateStash, sender_, 
                         initialize_options, initialize_duration, sender_c, 
                         sender, recipient, amount >>

L0 == /\ pc = "L0"
      /\ IF ~(((~(\E x \in DOMAIN Voted: Voted[x] = sender_v)) /\ (vote_option > 0)) /\ (vote_option <= Options))
            THEN /\ pc' = Head(stack).pc
                 /\ sender_v' = Head(stack).sender_v
                 /\ vote_option' = Head(stack).vote_option
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L1"
                 /\ UNCHANGED << stack, sender_v, vote_option >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, Winner, __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_c, sender, recipient, amount >>

L1 == /\ pc = "L1"
      /\ /\ Voted' = Append(Voted, sender_v)
         /\ Votes' = [Votes EXCEPT ![vote_option] = Votes[vote_option] + 1]
      /\ pc' = "L2"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, 
                      Winner, __stateStash, stack, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender_c, 
                      sender, recipient, amount >>

L2 == /\ pc = "L2"
      /\ IF ((Winner /= 0) /\ (Votes[vote_option] > Votes[Winner])) \/ (Winner = 0)
            THEN /\ Winner' = vote_option
            ELSE /\ TRUE
                 /\ UNCHANGED Winner
      /\ pc' = "L3"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, __stateStash, stack, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender_c, 
                      sender, recipient, amount >>

L3 == /\ pc = "L3"
      /\ pc' = Head(stack).pc
      /\ sender_v' = Head(stack).sender_v
      /\ vote_option' = Head(stack).vote_option
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, Winner, __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_c, sender, recipient, amount >>

vote == vote_ \/ L0 \/ L1 \/ L2 \/ L3

close_ == /\ pc = "close_"
          /\ IF __currentState /= OPEN
                THEN /\ pc' = Head(stack).pc
                     /\ sender_c' = Head(stack).sender_c
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "L4"
                     /\ UNCHANGED << stack, sender_c >>
          /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                          balance, __temporary, Organizer, Options, EndTime, 
                          Voted, Votes, Winner, __stateStash, sender_, 
                          initialize_options, initialize_duration, sender_v, 
                          vote_option, sender, recipient, amount >>

L4 == /\ pc = "L4"
      /\ IF ~(__currentTime > EndTime)
            THEN /\ pc' = Head(stack).pc
                 /\ sender_c' = Head(stack).sender_c
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L5"
                 /\ UNCHANGED << stack, sender_c >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, Winner, __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender, 
                      recipient, amount >>

L5 == /\ pc = "L5"
      /\ IF sender_c /= Organizer
            THEN /\ pc' = Head(stack).pc
                 /\ sender_c' = Head(stack).sender_c
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L6"
                 /\ UNCHANGED << stack, sender_c >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, Winner, __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender, 
                      recipient, amount >>

L6 == /\ pc = "L6"
      /\ __currentState' = CLOSED
      /\ pc' = Head(stack).pc
      /\ sender_c' = Head(stack).sender_c
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentTime, __contractCallDepth, balance, __temporary, 
                      Organizer, Options, EndTime, Voted, Votes, Winner, 
                      __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender, 
                      recipient, amount >>

close == close_ \/ L4 \/ L5 \/ L6

InvokeContract == /\ pc = "InvokeContract"
                  /\ IF __contractCallDepth = 0
                        THEN /\ __stateStash' =                 [
                                                    Organizer |-> Organizer,
                                                    Options |-> Options,
                                                    EndTime |-> EndTime,
                                                    Voted |-> Voted,
                                                    Votes |-> Votes,
                                                    Winner |-> Winner,
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
                                  Organizer, Options, EndTime, Voted, Votes, 
                                  Winner, stack, sender_, initialize_options, 
                                  initialize_duration, sender_v, vote_option, 
                                  sender_c, sender, recipient, amount >>

MethodCall == /\ pc = "MethodCall"
              /\ \/ /\ \E vote_option_arg \in 0..MAX_INT:
                         /\ /\ sender_v' = sender
                            /\ stack' = << [ procedure |->  "vote",
                                             pc        |->  "L7",
                                             sender_v  |->  sender_v,
                                             vote_option |->  vote_option ] >>
                                         \o stack
                            /\ vote_option' = vote_option_arg
                         /\ pc' = "vote_"
                    /\ UNCHANGED sender_c
                 \/ /\ /\ sender_c' = sender
                       /\ stack' = << [ procedure |->  "close",
                                        pc        |->  "L7",
                                        sender_c  |->  sender_c ] >>
                                    \o stack
                    /\ pc' = "close_"
                    /\ UNCHANGED <<sender_v, vote_option>>
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, balance, __temporary, 
                              Organizer, Options, EndTime, Voted, Votes, 
                              Winner, __stateStash, sender_, 
                              initialize_options, initialize_duration, sender, 
                              recipient, amount >>

L7 == /\ pc = "L7"
      /\ __contractCallDepth' = __contractCallDepth - 1
      /\ pc' = Head(stack).pc
      /\ sender' = Head(stack).sender
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, balance, __temporary, 
                      Organizer, Options, EndTime, Voted, Votes, Winner, 
                      __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender_c, 
                      recipient, amount >>

invokeContract == InvokeContract \/ MethodCall \/ L7

SendTokens == /\ pc = "SendTokens"
              /\ balance' = balance - amount
              /\ pc' = "SendInvocation"
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, __temporary, Organizer, 
                              Options, EndTime, Voted, Votes, Winner, 
                              __stateStash, stack, sender_, initialize_options, 
                              initialize_duration, sender_v, vote_option, 
                              sender_c, sender, recipient, amount >>

SendInvocation == /\ pc = "SendInvocation"
                  /\ \/ /\ stack' = << [ procedure |->  "throw",
                                         pc        |->  "L8" ] >>
                                     \o stack
                        /\ pc' = "Throw"
                     \/ /\ TRUE
                        /\ pc' = "L8"
                        /\ stack' = stack
                  /\ UNCHANGED << __currentState, __currentTime, 
                                  __contractCallDepth, balance, __temporary, 
                                  Organizer, Options, EndTime, Voted, Votes, 
                                  Winner, __stateStash, sender_, 
                                  initialize_options, initialize_duration, 
                                  sender_v, vote_option, sender_c, sender, 
                                  recipient, amount >>

L8 == /\ pc = "L8"
      /\ pc' = Head(stack).pc
      /\ recipient' = Head(stack).recipient
      /\ amount' = Head(stack).amount
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, Winner, __stateStash, sender_, initialize_options, 
                      initialize_duration, sender_v, vote_option, sender_c, 
                      sender >>

sendTokens == SendTokens \/ SendInvocation \/ L8

Throw == /\ pc = "Throw"
         /\ Organizer' = __stateStash["Organizer"]
         /\ Options' = __stateStash["Options"]
         /\ EndTime' = __stateStash["EndTime"]
         /\ Voted' = __stateStash["Voted"]
         /\ Votes' = __stateStash["Votes"]
         /\ Winner' = __stateStash["Winner"]
         /\ balance' = __stateStash["balance"]
         /\ __currentState' = __stateStash["__currentState"]
         /\ __contractCallDepth' = 0
         /\ pc' = "Loop"
         /\ stack' = <<>>
         /\ UNCHANGED << __currentTime, __temporary, __stateStash, sender_, 
                         initialize_options, initialize_duration, sender_v, 
                         vote_option, sender_c, sender, recipient, amount >>

throw == Throw

Main == /\ pc = "Main"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             \E initialize_options_arg \in 0..MAX_INT:
               \E initialize_duration_arg \in 0..MAX_INT:
                 /\ /\ initialize_duration' = initialize_duration_arg
                    /\ initialize_options' = initialize_options_arg
                    /\ sender_' = sender_arg
                    /\ stack' = << [ procedure |->  "initialize",
                                     pc        |->  "Loop",
                                     sender_   |->  sender_,
                                     initialize_options |->  initialize_options,
                                     initialize_duration |->  initialize_duration ] >>
                                 \o stack
                 /\ pc' = "initialize_"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Organizer, Options, EndTime, 
                        Voted, Votes, Winner, __stateStash, sender_v, 
                        vote_option, sender_c, sender, recipient, amount >>

Loop == /\ pc = "Loop"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             /\ /\ sender' = sender_arg
                /\ stack' = << [ procedure |->  "invokeContract",
                                 pc        |->  "L9",
                                 sender    |->  sender ] >>
                             \o stack
             /\ pc' = "InvokeContract"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Organizer, Options, EndTime, 
                        Voted, Votes, Winner, __stateStash, sender_, 
                        initialize_options, initialize_duration, sender_v, 
                        vote_option, sender_c, recipient, amount >>

L9 == /\ pc = "L9"
      /\ pc' = "Loop"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Organizer, Options, EndTime, Voted, 
                      Votes, Winner, __stateStash, stack, sender_, 
                      initialize_options, initialize_duration, sender_v, 
                      vote_option, sender_c, sender, recipient, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == initialize \/ vote \/ close \/ invokeContract \/ sendTokens
           \/ throw \/ Main \/ Loop \/ L9
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
========
