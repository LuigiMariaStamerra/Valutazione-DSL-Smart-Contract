-----MODULE EtherExchange-----
EXTENDS Integers, Sequences, TLC
CONSTANTS MAX_INT, MIN_INT, MAX_TIMESTEP, MAX_ELAPSED_TIME, MAX_CALL_DEPTH
CONSTANTS OPEN
STATES == { OPEN }
CONSTANTS ZERO_IDENT, __ident1, __ident2, __ident3
IDENTITIES == { ZERO_IDENT, __ident1, __ident2, __ident3 }


RECURSIVE SeqSum(_)
SeqSum(S) == IF S = <<>> THEN 0 ELSE Head(S) + SeqSum(Tail(S))

RECURSIVE MapSum(_)
MapSum(M) == IF DOMAIN M = {} THEN 0 ELSE
             LET x == CHOOSE x \in DOMAIN M: TRUE
             IN M[x] + MapSum([ y \in  (DOMAIN M \ {x}) |-> M[y] ])

(* --fair algorithm EtherExchange
variables __currentState = OPEN;
    __currentTime = 0;
    __contractCallDepth = 0;
    balance = 0;
    __temporary = 0;
    __stateStash = [
        balance |-> balance,
        __currentState |-> __currentState
    ];

    procedure initialize(sender) begin initialize:
        __currentState := OPEN;
        return;
    end procedure;

    procedure deposit(sender, deposit_tokens) begin deposit:
        if __currentState /= OPEN then
            return;
        end if;
L0:
        balance := balance + deposit_tokens;
        return;
    end procedure;

    procedure send(sender, send_to, send_amount) begin send:
        if __currentState /= OPEN then
            return;
        end if;
L1:
        if ~(send_amount <= balance) then
            return;
        end if;
L2:
        __temporary := send_amount;
        send_amount := send_amount - __temporary;
        call sendTokens(send_to, __temporary);
L3:
        return;
    end procedure;

    procedure invokeContract(sender) begin InvokeContract:
        if __contractCallDepth = 0 then
            __stateStash := [
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
            with deposit_tokens_arg \in 0..MAX_INT do
                call deposit(sender, deposit_tokens_arg);
            end with;
        or
            with send_to_arg \in IDENTITIES \ {ZERO_IDENT}, send_amount_arg \in 0..MAX_INT do
                call send(sender, send_to_arg, send_amount_arg);
            end with;
        end either;
L4:
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
L5:
        return;
    end procedure;

    procedure throw() begin Throw:
        balance := __stateStash["balance"];
        __currentState := __stateStash["__currentState"];
        __contractCallDepth := 0;
        return;
    end procedure;

begin Main:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT} do
        call initialize(sender_arg);
    end with;

Loop:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT} do
        call invokeContract(sender_arg);
    end with;
L6:
    goto Loop;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f4526036" /\ chksum(tla) = "66afe1b7")
\* Label initialize of procedure initialize at line 30 col 9 changed to initialize_
\* Label deposit of procedure deposit at line 35 col 9 changed to deposit_
\* Label send of procedure send at line 44 col 9 changed to send_
\* Parameter sender of procedure initialize at line 29 col 26 changed to sender_
\* Parameter sender of procedure deposit at line 34 col 23 changed to sender_d
\* Parameter sender of procedure send at line 43 col 20 changed to sender_s
CONSTANT defaultInitValue
VARIABLES __currentState, __currentTime, __contractCallDepth, balance, 
          __temporary, __stateStash, pc, stack, sender_, sender_d, 
          deposit_tokens, sender_s, send_to, send_amount, sender, recipient, 
          amount

vars == << __currentState, __currentTime, __contractCallDepth, balance, 
           __temporary, __stateStash, pc, stack, sender_, sender_d, 
           deposit_tokens, sender_s, send_to, send_amount, sender, recipient, 
           amount >>

Init == (* Global variables *)
        /\ __currentState = OPEN
        /\ __currentTime = 0
        /\ __contractCallDepth = 0
        /\ balance = 0
        /\ __temporary = 0
        /\ __stateStash =                [
                              balance |-> balance,
                              __currentState |-> __currentState
                          ]
        (* Procedure initialize *)
        /\ sender_ = defaultInitValue
        (* Procedure deposit *)
        /\ sender_d = defaultInitValue
        /\ deposit_tokens = defaultInitValue
        (* Procedure send *)
        /\ sender_s = defaultInitValue
        /\ send_to = defaultInitValue
        /\ send_amount = defaultInitValue
        (* Procedure invokeContract *)
        /\ sender = defaultInitValue
        (* Procedure sendTokens *)
        /\ recipient = defaultInitValue
        /\ amount = defaultInitValue
        /\ stack = << >>
        /\ pc = "Main"

initialize_ == /\ pc = "initialize_"
               /\ __currentState' = OPEN
               /\ pc' = Head(stack).pc
               /\ sender_' = Head(stack).sender_
               /\ stack' = Tail(stack)
               /\ UNCHANGED << __currentTime, __contractCallDepth, balance, 
                               __temporary, __stateStash, sender_d, 
                               deposit_tokens, sender_s, send_to, send_amount, 
                               sender, recipient, amount >>

initialize == initialize_

deposit_ == /\ pc = "deposit_"
            /\ IF __currentState /= OPEN
                  THEN /\ pc' = Head(stack).pc
                       /\ sender_d' = Head(stack).sender_d
                       /\ deposit_tokens' = Head(stack).deposit_tokens
                       /\ stack' = Tail(stack)
                  ELSE /\ pc' = "L0"
                       /\ UNCHANGED << stack, sender_d, deposit_tokens >>
            /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                            balance, __temporary, __stateStash, sender_, 
                            sender_s, send_to, send_amount, sender, recipient, 
                            amount >>

L0 == /\ pc = "L0"
      /\ balance' = balance + deposit_tokens
      /\ pc' = Head(stack).pc
      /\ sender_d' = Head(stack).sender_d
      /\ deposit_tokens' = Head(stack).deposit_tokens
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      __temporary, __stateStash, sender_, sender_s, send_to, 
                      send_amount, sender, recipient, amount >>

deposit == deposit_ \/ L0

send_ == /\ pc = "send_"
         /\ IF __currentState /= OPEN
               THEN /\ pc' = Head(stack).pc
                    /\ sender_s' = Head(stack).sender_s
                    /\ send_to' = Head(stack).send_to
                    /\ send_amount' = Head(stack).send_amount
                    /\ stack' = Tail(stack)
               ELSE /\ pc' = "L1"
                    /\ UNCHANGED << stack, sender_s, send_to, send_amount >>
         /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                         balance, __temporary, __stateStash, sender_, sender_d, 
                         deposit_tokens, sender, recipient, amount >>

L1 == /\ pc = "L1"
      /\ IF ~(send_amount <= balance)
            THEN /\ pc' = Head(stack).pc
                 /\ sender_s' = Head(stack).sender_s
                 /\ send_to' = Head(stack).send_to
                 /\ send_amount' = Head(stack).send_amount
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L2"
                 /\ UNCHANGED << stack, sender_s, send_to, send_amount >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, __stateStash, sender_, sender_d, 
                      deposit_tokens, sender, recipient, amount >>

L2 == /\ pc = "L2"
      /\ __temporary' = send_amount
      /\ send_amount' = send_amount - __temporary'
      /\ /\ amount' = __temporary'
         /\ recipient' = send_to
         /\ stack' = << [ procedure |->  "sendTokens",
                          pc        |->  "L3",
                          recipient |->  recipient,
                          amount    |->  amount ] >>
                      \o stack
      /\ pc' = "SendTokens"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __stateStash, sender_, sender_d, deposit_tokens, 
                      sender_s, send_to, sender >>

L3 == /\ pc = "L3"
      /\ pc' = Head(stack).pc
      /\ sender_s' = Head(stack).sender_s
      /\ send_to' = Head(stack).send_to
      /\ send_amount' = Head(stack).send_amount
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, __stateStash, sender_, sender_d, 
                      deposit_tokens, sender, recipient, amount >>

send == send_ \/ L1 \/ L2 \/ L3

InvokeContract == /\ pc = "InvokeContract"
                  /\ IF __contractCallDepth = 0
                        THEN /\ __stateStash' =                 [
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
                  /\ UNCHANGED << __currentState, balance, __temporary, stack, 
                                  sender_, sender_d, deposit_tokens, sender_s, 
                                  send_to, send_amount, sender, recipient, 
                                  amount >>

MethodCall == /\ pc = "MethodCall"
              /\ \/ /\ \E deposit_tokens_arg \in 0..MAX_INT:
                         /\ /\ deposit_tokens' = deposit_tokens_arg
                            /\ sender_d' = sender
                            /\ stack' = << [ procedure |->  "deposit",
                                             pc        |->  "L4",
                                             sender_d  |->  sender_d,
                                             deposit_tokens |->  deposit_tokens ] >>
                                         \o stack
                         /\ pc' = "deposit_"
                    /\ UNCHANGED <<sender_s, send_to, send_amount>>
                 \/ /\ \E send_to_arg \in IDENTITIES \ {ZERO_IDENT}:
                         \E send_amount_arg \in 0..MAX_INT:
                           /\ /\ send_amount' = send_amount_arg
                              /\ send_to' = send_to_arg
                              /\ sender_s' = sender
                              /\ stack' = << [ procedure |->  "send",
                                               pc        |->  "L4",
                                               sender_s  |->  sender_s,
                                               send_to   |->  send_to,
                                               send_amount |->  send_amount ] >>
                                           \o stack
                           /\ pc' = "send_"
                    /\ UNCHANGED <<sender_d, deposit_tokens>>
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, balance, __temporary, 
                              __stateStash, sender_, sender, recipient, amount >>

L4 == /\ pc = "L4"
      /\ __contractCallDepth' = __contractCallDepth - 1
      /\ pc' = Head(stack).pc
      /\ sender' = Head(stack).sender
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, balance, __temporary, 
                      __stateStash, sender_, sender_d, deposit_tokens, 
                      sender_s, send_to, send_amount, recipient, amount >>

invokeContract == InvokeContract \/ MethodCall \/ L4

SendTokens == /\ pc = "SendTokens"
              /\ balance' = balance - amount
              /\ pc' = "SendInvocation"
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, __temporary, __stateStash, 
                              stack, sender_, sender_d, deposit_tokens, 
                              sender_s, send_to, send_amount, sender, 
                              recipient, amount >>

SendInvocation == /\ pc = "SendInvocation"
                  /\ \/ /\ stack' = << [ procedure |->  "throw",
                                         pc        |->  "L5" ] >>
                                     \o stack
                        /\ pc' = "Throw"
                     \/ /\ TRUE
                        /\ pc' = "L5"
                        /\ stack' = stack
                  /\ UNCHANGED << __currentState, __currentTime, 
                                  __contractCallDepth, balance, __temporary, 
                                  __stateStash, sender_, sender_d, 
                                  deposit_tokens, sender_s, send_to, 
                                  send_amount, sender, recipient, amount >>

L5 == /\ pc = "L5"
      /\ pc' = Head(stack).pc
      /\ recipient' = Head(stack).recipient
      /\ amount' = Head(stack).amount
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, __stateStash, sender_, sender_d, 
                      deposit_tokens, sender_s, send_to, send_amount, sender >>

sendTokens == SendTokens \/ SendInvocation \/ L5

Throw == /\ pc = "Throw"
         /\ balance' = __stateStash["balance"]
         /\ __currentState' = __stateStash["__currentState"]
         /\ __contractCallDepth' = 0
         /\ pc' = "Loop"
         /\ stack' = <<>>
         /\ UNCHANGED << __currentTime, __temporary, __stateStash, sender_, 
                         sender_d, deposit_tokens, sender_s, send_to, 
                         send_amount, sender, recipient, amount >>

throw == Throw

Main == /\ pc = "Main"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             /\ /\ sender_' = sender_arg
                /\ stack' = << [ procedure |->  "initialize",
                                 pc        |->  "Loop",
                                 sender_   |->  sender_ ] >>
                             \o stack
             /\ pc' = "initialize_"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, __stateStash, sender_d, 
                        deposit_tokens, sender_s, send_to, send_amount, sender, 
                        recipient, amount >>

Loop == /\ pc = "Loop"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             /\ /\ sender' = sender_arg
                /\ stack' = << [ procedure |->  "invokeContract",
                                 pc        |->  "L6",
                                 sender    |->  sender ] >>
                             \o stack
             /\ pc' = "InvokeContract"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, __stateStash, sender_, sender_d, 
                        deposit_tokens, sender_s, send_to, send_amount, 
                        recipient, amount >>

L6 == /\ pc = "L6"
      /\ pc' = "Loop"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, __stateStash, stack, sender_, 
                      sender_d, deposit_tokens, sender_s, send_to, send_amount, 
                      sender, recipient, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == initialize \/ deposit \/ send \/ invokeContract \/ sendTokens
           \/ throw \/ Main \/ Loop \/ L6
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
========
