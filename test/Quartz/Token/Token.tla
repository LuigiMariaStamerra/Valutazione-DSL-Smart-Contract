-----MODULE Token-----
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

(* --fair algorithm Token
variables __currentState = OPEN;
    __currentTime = 0;
    __contractCallDepth = 0;
    balance = 0;
    __temporary = 0;
    Name = "";
    Symbol = "";
    BalanceOf = [ x \in IDENTITIES \ {ZERO_IDENT} |-> 0 ];
    Owner = ZERO_IDENT;
    Decimals = 0;
    TotalSupply = 0;
    Allowance = [ x \in IDENTITIES \ {ZERO_IDENT} |-> [ x \in IDENTITIES \ {ZERO_IDENT} |-> 0 ] ];
    NullAddress = ZERO_IDENT;
    __stateStash = [
        Name |-> Name,
        Symbol |-> Symbol,
        BalanceOf |-> BalanceOf,
        Owner |-> Owner,
        Decimals |-> Decimals,
        TotalSupply |-> TotalSupply,
        Allowance |-> Allowance,
        NullAddress |-> NullAddress,
        balance |-> balance,
        __currentState |-> __currentState
    ];

    procedure initialize(sender, initialize_name, initialize_symbol) begin initialize:
        __currentState := OPEN;
        Name := initialize_name ||
        Symbol := initialize_symbol ||
        Decimals := 18 ||
        Owner := sender;
        return;
    end procedure;

    procedure mint(sender, mint_to, mint_amount) begin mint:
        if __currentState /= OPEN then
            return;
        end if;
L0:
        if ~((mint_to /= NullAddress) /\ (mint_amount > 0)) then
            return;
        end if;
L1:
        if sender /= Owner then
            return;
        end if;
L2:
        TotalSupply := TotalSupply + mint_amount ||
        BalanceOf[mint_to] := BalanceOf[mint_to] + mint_amount;
L3:
        return;
    end procedure;

    procedure transfer(sender, transfer_to, transfer_amount) begin transfer:
        if __currentState /= OPEN then
            return;
        end if;
L4:
        if ~((BalanceOf[sender] >= transfer_amount) /\ (transfer_to /= NullAddress)) then
            return;
        end if;
L5:
        BalanceOf[sender] := BalanceOf[sender] - transfer_amount ||
        BalanceOf[transfer_to] := BalanceOf[transfer_to] + transfer_amount;
L6:
        return;
    end procedure;

    procedure approve(sender, approve_spender, approve_amount) begin approve:
        if __currentState /= OPEN then
            return;
        end if;
L7:
        Allowance[sender][approve_spender] := approve_amount;
L8:
        return;
    end procedure;

    procedure transferFrom(sender, transferFrom_from, transferFrom_to, transferFrom_amount) begin transferFrom:
        if __currentState /= OPEN then
            return;
        end if;
L9:
        if ~(((Allowance[transferFrom_from][sender] >= transferFrom_amount) /\ (BalanceOf[transferFrom_from] >= transferFrom_amount)) /\ (transferFrom_to /= NullAddress)) then
            return;
        end if;
L10:
        Allowance[transferFrom_from][sender] := Allowance[transferFrom_from][sender] - transferFrom_amount ||
        BalanceOf[transferFrom_from] := BalanceOf[transferFrom_from] - transferFrom_amount ||
        BalanceOf[transferFrom_to] := BalanceOf[transferFrom_to] + transferFrom_amount;
L11:
        return;
    end procedure;

    procedure invokeContract(sender) begin InvokeContract:
        if __contractCallDepth = 0 then
            __stateStash := [
                Name |-> Name,
                Symbol |-> Symbol,
                BalanceOf |-> BalanceOf,
                Owner |-> Owner,
                Decimals |-> Decimals,
                TotalSupply |-> TotalSupply,
                Allowance |-> Allowance,
                NullAddress |-> NullAddress,
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
            with mint_to_arg \in IDENTITIES \ {ZERO_IDENT}, mint_amount_arg \in 0..MAX_INT do
                call mint(sender, mint_to_arg, mint_amount_arg);
            end with;
        or
            with transfer_to_arg \in IDENTITIES \ {ZERO_IDENT}, transfer_amount_arg \in 0..MAX_INT do
                call transfer(sender, transfer_to_arg, transfer_amount_arg);
            end with;
        or
            with approve_spender_arg \in IDENTITIES \ {ZERO_IDENT}, approve_amount_arg \in 0..MAX_INT do
                call approve(sender, approve_spender_arg, approve_amount_arg);
            end with;
        or
            with transferFrom_from_arg \in IDENTITIES \ {ZERO_IDENT}, transferFrom_to_arg \in IDENTITIES \ {ZERO_IDENT}, transferFrom_amount_arg \in 0..MAX_INT do
                call transferFrom(sender, transferFrom_from_arg, transferFrom_to_arg, transferFrom_amount_arg);
            end with;
        end either;
L12:
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
L13:
        return;
    end procedure;

    procedure throw() begin Throw:
        Name := __stateStash["Name"];
        Symbol := __stateStash["Symbol"];
        BalanceOf := __stateStash["BalanceOf"];
        Owner := __stateStash["Owner"];
        Decimals := __stateStash["Decimals"];
        TotalSupply := __stateStash["TotalSupply"];
        Allowance := __stateStash["Allowance"];
        NullAddress := __stateStash["NullAddress"];
        balance := __stateStash["balance"];
        __currentState := __stateStash["__currentState"];
        __contractCallDepth := 0;
        return;
    end procedure;

begin Main:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT}, initialize_name_arg \in {"str_1"}, initialize_symbol_arg \in {"str_1"} do
        call initialize(sender_arg, initialize_name_arg, initialize_symbol_arg);
    end with;

Loop:
    with sender_arg \in IDENTITIES \ {ZERO_IDENT} do
        call invokeContract(sender_arg);
    end with;
L14:
    goto Loop;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f4110fb7" /\ chksum(tla) = "4ac98f7c")
\* Label initialize of procedure initialize at line 46 col 9 changed to initialize_
\* Label mint of procedure mint at line 55 col 9 changed to mint_
\* Label transfer of procedure transfer at line 74 col 9 changed to transfer_
\* Label approve of procedure approve at line 89 col 9 changed to approve_
\* Label transferFrom of procedure transferFrom at line 99 col 9 changed to transferFrom_
\* Parameter sender of procedure initialize at line 45 col 26 changed to sender_
\* Parameter sender of procedure mint at line 54 col 20 changed to sender_m
\* Parameter sender of procedure transfer at line 73 col 24 changed to sender_t
\* Parameter sender of procedure approve at line 88 col 23 changed to sender_a
\* Parameter sender of procedure transferFrom at line 98 col 28 changed to sender_tr
CONSTANT defaultInitValue
VARIABLES __currentState, __currentTime, __contractCallDepth, balance, 
          __temporary, Name, Symbol, BalanceOf, Owner, Decimals, TotalSupply, 
          Allowance, NullAddress, __stateStash, pc, stack, sender_, 
          initialize_name, initialize_symbol, sender_m, mint_to, mint_amount, 
          sender_t, transfer_to, transfer_amount, sender_a, approve_spender, 
          approve_amount, sender_tr, transferFrom_from, transferFrom_to, 
          transferFrom_amount, sender, recipient, amount

vars == << __currentState, __currentTime, __contractCallDepth, balance, 
           __temporary, Name, Symbol, BalanceOf, Owner, Decimals, TotalSupply, 
           Allowance, NullAddress, __stateStash, pc, stack, sender_, 
           initialize_name, initialize_symbol, sender_m, mint_to, mint_amount, 
           sender_t, transfer_to, transfer_amount, sender_a, approve_spender, 
           approve_amount, sender_tr, transferFrom_from, transferFrom_to, 
           transferFrom_amount, sender, recipient, amount >>

Init == (* Global variables *)
        /\ __currentState = OPEN
        /\ __currentTime = 0
        /\ __contractCallDepth = 0
        /\ balance = 0
        /\ __temporary = 0
        /\ Name = ""
        /\ Symbol = ""
        /\ BalanceOf = [ x \in IDENTITIES \ {ZERO_IDENT} |-> 0 ]
        /\ Owner = ZERO_IDENT
        /\ Decimals = 0
        /\ TotalSupply = 0
        /\ Allowance = [ x \in IDENTITIES \ {ZERO_IDENT} |-> [ y \in IDENTITIES \ {ZERO_IDENT} |-> 0 ] ]
        /\ NullAddress = ZERO_IDENT
        /\ __stateStash =                [
                              Name |-> Name,
                              Symbol |-> Symbol,
                              BalanceOf |-> BalanceOf,
                              Owner |-> Owner,
                              Decimals |-> Decimals,
                              TotalSupply |-> TotalSupply,
                              Allowance |-> Allowance,
                              NullAddress |-> NullAddress,
                              balance |-> balance,
                              __currentState |-> __currentState
                          ]
        (* Procedure initialize *)
        /\ sender_ = defaultInitValue
        /\ initialize_name = defaultInitValue
        /\ initialize_symbol = defaultInitValue
        (* Procedure mint *)
        /\ sender_m = defaultInitValue
        /\ mint_to = defaultInitValue
        /\ mint_amount = defaultInitValue
        (* Procedure transfer *)
        /\ sender_t = defaultInitValue
        /\ transfer_to = defaultInitValue
        /\ transfer_amount = defaultInitValue
        (* Procedure approve *)
        /\ sender_a = defaultInitValue
        /\ approve_spender = defaultInitValue
        /\ approve_amount = defaultInitValue
        (* Procedure transferFrom *)
        /\ sender_tr = defaultInitValue
        /\ transferFrom_from = defaultInitValue
        /\ transferFrom_to = defaultInitValue
        /\ transferFrom_amount = defaultInitValue
        (* Procedure invokeContract *)
        /\ sender = defaultInitValue
        (* Procedure sendTokens *)
        /\ recipient = defaultInitValue
        /\ amount = defaultInitValue
        /\ stack = << >>
        /\ pc = "Main"

initialize_ == /\ pc = "initialize_"
               /\ __currentState' = OPEN
               /\ /\ Decimals' = 18
                  /\ Name' = initialize_name
                  /\ Owner' = sender_
                  /\ Symbol' = initialize_symbol
               /\ pc' = Head(stack).pc
               /\ sender_' = Head(stack).sender_
               /\ initialize_name' = Head(stack).initialize_name
               /\ initialize_symbol' = Head(stack).initialize_symbol
               /\ stack' = Tail(stack)
               /\ UNCHANGED << __currentTime, __contractCallDepth, balance, 
                               __temporary, BalanceOf, TotalSupply, Allowance, 
                               NullAddress, __stateStash, sender_m, mint_to, 
                               mint_amount, sender_t, transfer_to, 
                               transfer_amount, sender_a, approve_spender, 
                               approve_amount, sender_tr, transferFrom_from, 
                               transferFrom_to, transferFrom_amount, sender, 
                               recipient, amount >>

initialize == initialize_

mint_ == /\ pc = "mint_"
         /\ IF __currentState /= OPEN
               THEN /\ pc' = Head(stack).pc
                    /\ sender_m' = Head(stack).sender_m
                    /\ mint_to' = Head(stack).mint_to
                    /\ mint_amount' = Head(stack).mint_amount
                    /\ stack' = Tail(stack)
               ELSE /\ pc' = "L0"
                    /\ UNCHANGED << stack, sender_m, mint_to, mint_amount >>
         /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                         balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                         Decimals, TotalSupply, Allowance, NullAddress, 
                         __stateStash, sender_, initialize_name, 
                         initialize_symbol, sender_t, transfer_to, 
                         transfer_amount, sender_a, approve_spender, 
                         approve_amount, sender_tr, transferFrom_from, 
                         transferFrom_to, transferFrom_amount, sender, 
                         recipient, amount >>

L0 == /\ pc = "L0"
      /\ IF ~((mint_to /= NullAddress) /\ (mint_amount > 0))
            THEN /\ pc' = Head(stack).pc
                 /\ sender_m' = Head(stack).sender_m
                 /\ mint_to' = Head(stack).mint_to
                 /\ mint_amount' = Head(stack).mint_amount
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L1"
                 /\ UNCHANGED << stack, sender_m, mint_to, mint_amount >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_t, transfer_to, 
                      transfer_amount, sender_a, approve_spender, 
                      approve_amount, sender_tr, transferFrom_from, 
                      transferFrom_to, transferFrom_amount, sender, recipient, 
                      amount >>

L1 == /\ pc = "L1"
      /\ IF sender_m /= Owner
            THEN /\ pc' = Head(stack).pc
                 /\ sender_m' = Head(stack).sender_m
                 /\ mint_to' = Head(stack).mint_to
                 /\ mint_amount' = Head(stack).mint_amount
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L2"
                 /\ UNCHANGED << stack, sender_m, mint_to, mint_amount >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_t, transfer_to, 
                      transfer_amount, sender_a, approve_spender, 
                      approve_amount, sender_tr, transferFrom_from, 
                      transferFrom_to, transferFrom_amount, sender, recipient, 
                      amount >>

L2 == /\ pc = "L2"
      /\ /\ BalanceOf' = [BalanceOf EXCEPT ![mint_to] = BalanceOf[mint_to] + mint_amount]
         /\ TotalSupply' = TotalSupply + mint_amount
      /\ pc' = "L3"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, Owner, Decimals, 
                      Allowance, NullAddress, __stateStash, stack, sender_, 
                      initialize_name, initialize_symbol, sender_m, mint_to, 
                      mint_amount, sender_t, transfer_to, transfer_amount, 
                      sender_a, approve_spender, approve_amount, sender_tr, 
                      transferFrom_from, transferFrom_to, transferFrom_amount, 
                      sender, recipient, amount >>

L3 == /\ pc = "L3"
      /\ pc' = Head(stack).pc
      /\ sender_m' = Head(stack).sender_m
      /\ mint_to' = Head(stack).mint_to
      /\ mint_amount' = Head(stack).mint_amount
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_t, transfer_to, 
                      transfer_amount, sender_a, approve_spender, 
                      approve_amount, sender_tr, transferFrom_from, 
                      transferFrom_to, transferFrom_amount, sender, recipient, 
                      amount >>

mint == mint_ \/ L0 \/ L1 \/ L2 \/ L3

transfer_ == /\ pc = "transfer_"
             /\ IF __currentState /= OPEN
                   THEN /\ pc' = Head(stack).pc
                        /\ sender_t' = Head(stack).sender_t
                        /\ transfer_to' = Head(stack).transfer_to
                        /\ transfer_amount' = Head(stack).transfer_amount
                        /\ stack' = Tail(stack)
                   ELSE /\ pc' = "L4"
                        /\ UNCHANGED << stack, sender_t, transfer_to, 
                                        transfer_amount >>
             /\ UNCHANGED << __currentState, __currentTime, 
                             __contractCallDepth, balance, __temporary, Name, 
                             Symbol, BalanceOf, Owner, Decimals, TotalSupply, 
                             Allowance, NullAddress, __stateStash, sender_, 
                             initialize_name, initialize_symbol, sender_m, 
                             mint_to, mint_amount, sender_a, approve_spender, 
                             approve_amount, sender_tr, transferFrom_from, 
                             transferFrom_to, transferFrom_amount, sender, 
                             recipient, amount >>

L4 == /\ pc = "L4"
      /\ IF ~((BalanceOf[sender_t] >= transfer_amount) /\ (transfer_to /= NullAddress))
            THEN /\ pc' = Head(stack).pc
                 /\ sender_t' = Head(stack).sender_t
                 /\ transfer_to' = Head(stack).transfer_to
                 /\ transfer_amount' = Head(stack).transfer_amount
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L5"
                 /\ UNCHANGED << stack, sender_t, transfer_to, transfer_amount >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_m, mint_to, mint_amount, 
                      sender_a, approve_spender, approve_amount, sender_tr, 
                      transferFrom_from, transferFrom_to, transferFrom_amount, 
                      sender, recipient, amount >>

L5 == /\ pc = "L5"
      /\ BalanceOf' = [BalanceOf EXCEPT ![sender_t] = BalanceOf[sender_t] - transfer_amount,
                                        ![transfer_to] = BalanceOf[transfer_to] + transfer_amount]
      /\ pc' = "L6"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, Owner, Decimals, 
                      TotalSupply, Allowance, NullAddress, __stateStash, stack, 
                      sender_, initialize_name, initialize_symbol, sender_m, 
                      mint_to, mint_amount, sender_t, transfer_to, 
                      transfer_amount, sender_a, approve_spender, 
                      approve_amount, sender_tr, transferFrom_from, 
                      transferFrom_to, transferFrom_amount, sender, recipient, 
                      amount >>

L6 == /\ pc = "L6"
      /\ pc' = Head(stack).pc
      /\ sender_t' = Head(stack).sender_t
      /\ transfer_to' = Head(stack).transfer_to
      /\ transfer_amount' = Head(stack).transfer_amount
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_m, mint_to, mint_amount, 
                      sender_a, approve_spender, approve_amount, sender_tr, 
                      transferFrom_from, transferFrom_to, transferFrom_amount, 
                      sender, recipient, amount >>

transfer == transfer_ \/ L4 \/ L5 \/ L6

approve_ == /\ pc = "approve_"
            /\ IF __currentState /= OPEN
                  THEN /\ pc' = Head(stack).pc
                       /\ sender_a' = Head(stack).sender_a
                       /\ approve_spender' = Head(stack).approve_spender
                       /\ approve_amount' = Head(stack).approve_amount
                       /\ stack' = Tail(stack)
                  ELSE /\ pc' = "L7"
                       /\ UNCHANGED << stack, sender_a, approve_spender, 
                                       approve_amount >>
            /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                            balance, __temporary, Name, Symbol, BalanceOf, 
                            Owner, Decimals, TotalSupply, Allowance, 
                            NullAddress, __stateStash, sender_, 
                            initialize_name, initialize_symbol, sender_m, 
                            mint_to, mint_amount, sender_t, transfer_to, 
                            transfer_amount, sender_tr, transferFrom_from, 
                            transferFrom_to, transferFrom_amount, sender, 
                            recipient, amount >>

L7 == /\ pc = "L7"
      /\ Allowance' = [Allowance EXCEPT ![sender_a][approve_spender] = approve_amount]
      /\ pc' = "L8"
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, NullAddress, __stateStash, stack, 
                      sender_, initialize_name, initialize_symbol, sender_m, 
                      mint_to, mint_amount, sender_t, transfer_to, 
                      transfer_amount, sender_a, approve_spender, 
                      approve_amount, sender_tr, transferFrom_from, 
                      transferFrom_to, transferFrom_amount, sender, recipient, 
                      amount >>

L8 == /\ pc = "L8"
      /\ pc' = Head(stack).pc
      /\ sender_a' = Head(stack).sender_a
      /\ approve_spender' = Head(stack).approve_spender
      /\ approve_amount' = Head(stack).approve_amount
      /\ stack' = Tail(stack)
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_m, mint_to, mint_amount, 
                      sender_t, transfer_to, transfer_amount, sender_tr, 
                      transferFrom_from, transferFrom_to, transferFrom_amount, 
                      sender, recipient, amount >>

approve == approve_ \/ L7 \/ L8

transferFrom_ == /\ pc = "transferFrom_"
                 /\ IF __currentState /= OPEN
                       THEN /\ pc' = Head(stack).pc
                            /\ sender_tr' = Head(stack).sender_tr
                            /\ transferFrom_from' = Head(stack).transferFrom_from
                            /\ transferFrom_to' = Head(stack).transferFrom_to
                            /\ transferFrom_amount' = Head(stack).transferFrom_amount
                            /\ stack' = Tail(stack)
                       ELSE /\ pc' = "L9"
                            /\ UNCHANGED << stack, sender_tr, 
                                            transferFrom_from, transferFrom_to, 
                                            transferFrom_amount >>
                 /\ UNCHANGED << __currentState, __currentTime, 
                                 __contractCallDepth, balance, __temporary, 
                                 Name, Symbol, BalanceOf, Owner, Decimals, 
                                 TotalSupply, Allowance, NullAddress, 
                                 __stateStash, sender_, initialize_name, 
                                 initialize_symbol, sender_m, mint_to, 
                                 mint_amount, sender_t, transfer_to, 
                                 transfer_amount, sender_a, approve_spender, 
                                 approve_amount, sender, recipient, amount >>

L9 == /\ pc = "L9"
      /\ IF ~(((Allowance[transferFrom_from][sender_tr] >= transferFrom_amount) /\ (BalanceOf[transferFrom_from] >= transferFrom_amount)) /\ (transferFrom_to /= NullAddress))
            THEN /\ pc' = Head(stack).pc
                 /\ sender_tr' = Head(stack).sender_tr
                 /\ transferFrom_from' = Head(stack).transferFrom_from
                 /\ transferFrom_to' = Head(stack).transferFrom_to
                 /\ transferFrom_amount' = Head(stack).transferFrom_amount
                 /\ stack' = Tail(stack)
            ELSE /\ pc' = "L10"
                 /\ UNCHANGED << stack, sender_tr, transferFrom_from, 
                                 transferFrom_to, transferFrom_amount >>
      /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                      balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                      Decimals, TotalSupply, Allowance, NullAddress, 
                      __stateStash, sender_, initialize_name, 
                      initialize_symbol, sender_m, mint_to, mint_amount, 
                      sender_t, transfer_to, transfer_amount, sender_a, 
                      approve_spender, approve_amount, sender, recipient, 
                      amount >>

L10 == /\ pc = "L10"
       /\ /\ Allowance' = [Allowance EXCEPT ![transferFrom_from][sender_tr] = Allowance[transferFrom_from][sender_tr] - transferFrom_amount]
          /\ BalanceOf' = [BalanceOf EXCEPT ![transferFrom_from] = BalanceOf[transferFrom_from] - transferFrom_amount,
                                            ![transferFrom_to] = BalanceOf[transferFrom_to] + transferFrom_amount]
       /\ pc' = "L11"
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Name, Symbol, Owner, Decimals, 
                       TotalSupply, NullAddress, __stateStash, stack, sender_, 
                       initialize_name, initialize_symbol, sender_m, mint_to, 
                       mint_amount, sender_t, transfer_to, transfer_amount, 
                       sender_a, approve_spender, approve_amount, sender_tr, 
                       transferFrom_from, transferFrom_to, transferFrom_amount, 
                       sender, recipient, amount >>

L11 == /\ pc = "L11"
       /\ pc' = Head(stack).pc
       /\ sender_tr' = Head(stack).sender_tr
       /\ transferFrom_from' = Head(stack).transferFrom_from
       /\ transferFrom_to' = Head(stack).transferFrom_to
       /\ transferFrom_amount' = Head(stack).transferFrom_amount
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                       Decimals, TotalSupply, Allowance, NullAddress, 
                       __stateStash, sender_, initialize_name, 
                       initialize_symbol, sender_m, mint_to, mint_amount, 
                       sender_t, transfer_to, transfer_amount, sender_a, 
                       approve_spender, approve_amount, sender, recipient, 
                       amount >>

transferFrom == transferFrom_ \/ L9 \/ L10 \/ L11

InvokeContract == /\ pc = "InvokeContract"
                  /\ IF __contractCallDepth = 0
                        THEN /\ __stateStash' =                 [
                                                    Name |-> Name,
                                                    Symbol |-> Symbol,
                                                    BalanceOf |-> BalanceOf,
                                                    Owner |-> Owner,
                                                    Decimals |-> Decimals,
                                                    TotalSupply |-> TotalSupply,
                                                    Allowance |-> Allowance,
                                                    NullAddress |-> NullAddress,
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
                  /\ UNCHANGED << __currentState, balance, __temporary, Name, 
                                  Symbol, BalanceOf, Owner, Decimals, 
                                  TotalSupply, Allowance, NullAddress, stack, 
                                  sender_, initialize_name, initialize_symbol, 
                                  sender_m, mint_to, mint_amount, sender_t, 
                                  transfer_to, transfer_amount, sender_a, 
                                  approve_spender, approve_amount, sender_tr, 
                                  transferFrom_from, transferFrom_to, 
                                  transferFrom_amount, sender, recipient, 
                                  amount >>

MethodCall == /\ pc = "MethodCall"
              /\ \/ /\ \E mint_to_arg \in IDENTITIES \ {ZERO_IDENT}:
                         \E mint_amount_arg \in 0..MAX_INT:
                           /\ /\ mint_amount' = mint_amount_arg
                              /\ mint_to' = mint_to_arg
                              /\ sender_m' = sender
                              /\ stack' = << [ procedure |->  "mint",
                                               pc        |->  "L12",
                                               sender_m  |->  sender_m,
                                               mint_to   |->  mint_to,
                                               mint_amount |->  mint_amount ] >>
                                           \o stack
                           /\ pc' = "mint_"
                    /\ UNCHANGED <<sender_t, transfer_to, transfer_amount, sender_a, approve_spender, approve_amount, sender_tr, transferFrom_from, transferFrom_to, transferFrom_amount>>
                 \/ /\ \E transfer_to_arg \in IDENTITIES \ {ZERO_IDENT}:
                         \E transfer_amount_arg \in 0..MAX_INT:
                           /\ /\ sender_t' = sender
                              /\ stack' = << [ procedure |->  "transfer",
                                               pc        |->  "L12",
                                               sender_t  |->  sender_t,
                                               transfer_to |->  transfer_to,
                                               transfer_amount |->  transfer_amount ] >>
                                           \o stack
                              /\ transfer_amount' = transfer_amount_arg
                              /\ transfer_to' = transfer_to_arg
                           /\ pc' = "transfer_"
                    /\ UNCHANGED <<sender_m, mint_to, mint_amount, sender_a, approve_spender, approve_amount, sender_tr, transferFrom_from, transferFrom_to, transferFrom_amount>>
                 \/ /\ \E approve_spender_arg \in IDENTITIES \ {ZERO_IDENT}:
                         \E approve_amount_arg \in 0..MAX_INT:
                           /\ /\ approve_amount' = approve_amount_arg
                              /\ approve_spender' = approve_spender_arg
                              /\ sender_a' = sender
                              /\ stack' = << [ procedure |->  "approve",
                                               pc        |->  "L12",
                                               sender_a  |->  sender_a,
                                               approve_spender |->  approve_spender,
                                               approve_amount |->  approve_amount ] >>
                                           \o stack
                           /\ pc' = "approve_"
                    /\ UNCHANGED <<sender_m, mint_to, mint_amount, sender_t, transfer_to, transfer_amount, sender_tr, transferFrom_from, transferFrom_to, transferFrom_amount>>
                 \/ /\ \E transferFrom_from_arg \in IDENTITIES \ {ZERO_IDENT}:
                         \E transferFrom_to_arg \in IDENTITIES \ {ZERO_IDENT}:
                           \E transferFrom_amount_arg \in 0..MAX_INT:
                             /\ /\ sender_tr' = sender
                                /\ stack' = << [ procedure |->  "transferFrom",
                                                 pc        |->  "L12",
                                                 sender_tr |->  sender_tr,
                                                 transferFrom_from |->  transferFrom_from,
                                                 transferFrom_to |->  transferFrom_to,
                                                 transferFrom_amount |->  transferFrom_amount ] >>
                                             \o stack
                                /\ transferFrom_amount' = transferFrom_amount_arg
                                /\ transferFrom_from' = transferFrom_from_arg
                                /\ transferFrom_to' = transferFrom_to_arg
                             /\ pc' = "transferFrom_"
                    /\ UNCHANGED <<sender_m, mint_to, mint_amount, sender_t, transfer_to, transfer_amount, sender_a, approve_spender, approve_amount>>
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, balance, __temporary, Name, 
                              Symbol, BalanceOf, Owner, Decimals, TotalSupply, 
                              Allowance, NullAddress, __stateStash, sender_, 
                              initialize_name, initialize_symbol, sender, 
                              recipient, amount >>

L12 == /\ pc = "L12"
       /\ __contractCallDepth' = __contractCallDepth - 1
       /\ pc' = Head(stack).pc
       /\ sender' = Head(stack).sender
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentState, __currentTime, balance, __temporary, 
                       Name, Symbol, BalanceOf, Owner, Decimals, TotalSupply, 
                       Allowance, NullAddress, __stateStash, sender_, 
                       initialize_name, initialize_symbol, sender_m, mint_to, 
                       mint_amount, sender_t, transfer_to, transfer_amount, 
                       sender_a, approve_spender, approve_amount, sender_tr, 
                       transferFrom_from, transferFrom_to, transferFrom_amount, 
                       recipient, amount >>

invokeContract == InvokeContract \/ MethodCall \/ L12

SendTokens == /\ pc = "SendTokens"
              /\ balance' = balance - amount
              /\ pc' = "SendInvocation"
              /\ UNCHANGED << __currentState, __currentTime, 
                              __contractCallDepth, __temporary, Name, Symbol, 
                              BalanceOf, Owner, Decimals, TotalSupply, 
                              Allowance, NullAddress, __stateStash, stack, 
                              sender_, initialize_name, initialize_symbol, 
                              sender_m, mint_to, mint_amount, sender_t, 
                              transfer_to, transfer_amount, sender_a, 
                              approve_spender, approve_amount, sender_tr, 
                              transferFrom_from, transferFrom_to, 
                              transferFrom_amount, sender, recipient, amount >>

SendInvocation == /\ pc = "SendInvocation"
                  /\ \/ /\ stack' = << [ procedure |->  "throw",
                                         pc        |->  "L13" ] >>
                                     \o stack
                        /\ pc' = "Throw"
                     \/ /\ TRUE
                        /\ pc' = "L13"
                        /\ stack' = stack
                  /\ UNCHANGED << __currentState, __currentTime, 
                                  __contractCallDepth, balance, __temporary, 
                                  Name, Symbol, BalanceOf, Owner, Decimals, 
                                  TotalSupply, Allowance, NullAddress, 
                                  __stateStash, sender_, initialize_name, 
                                  initialize_symbol, sender_m, mint_to, 
                                  mint_amount, sender_t, transfer_to, 
                                  transfer_amount, sender_a, approve_spender, 
                                  approve_amount, sender_tr, transferFrom_from, 
                                  transferFrom_to, transferFrom_amount, sender, 
                                  recipient, amount >>

L13 == /\ pc = "L13"
       /\ pc' = Head(stack).pc
       /\ recipient' = Head(stack).recipient
       /\ amount' = Head(stack).amount
       /\ stack' = Tail(stack)
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                       Decimals, TotalSupply, Allowance, NullAddress, 
                       __stateStash, sender_, initialize_name, 
                       initialize_symbol, sender_m, mint_to, mint_amount, 
                       sender_t, transfer_to, transfer_amount, sender_a, 
                       approve_spender, approve_amount, sender_tr, 
                       transferFrom_from, transferFrom_to, transferFrom_amount, 
                       sender >>

sendTokens == SendTokens \/ SendInvocation \/ L13

Throw == /\ pc = "Throw"
         /\ Name' = __stateStash["Name"]
         /\ Symbol' = __stateStash["Symbol"]
         /\ BalanceOf' = __stateStash["BalanceOf"]
         /\ Owner' = __stateStash["Owner"]
         /\ Decimals' = __stateStash["Decimals"]
         /\ TotalSupply' = __stateStash["TotalSupply"]
         /\ Allowance' = __stateStash["Allowance"]
         /\ NullAddress' = __stateStash["NullAddress"]
         /\ balance' = __stateStash["balance"]
         /\ __currentState' = __stateStash["__currentState"]
         /\ __contractCallDepth' = 0
         /\ pc' = "Loop"
         /\ stack' = <<>>
         /\ UNCHANGED << __currentTime, __temporary, __stateStash, sender_, 
                         initialize_name, initialize_symbol, sender_m, mint_to, 
                         mint_amount, sender_t, transfer_to, transfer_amount, 
                         sender_a, approve_spender, approve_amount, sender_tr, 
                         transferFrom_from, transferFrom_to, 
                         transferFrom_amount, sender, recipient, amount >>

throw == Throw

Main == /\ pc = "Main"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             \E initialize_name_arg \in {"str_1"}:
               \E initialize_symbol_arg \in {"str_1"}:
                 /\ /\ initialize_name' = initialize_name_arg
                    /\ initialize_symbol' = initialize_symbol_arg
                    /\ sender_' = sender_arg
                    /\ stack' = << [ procedure |->  "initialize",
                                     pc        |->  "Loop",
                                     sender_   |->  sender_,
                                     initialize_name |->  initialize_name,
                                     initialize_symbol |->  initialize_symbol ] >>
                                 \o stack
                 /\ pc' = "initialize_"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                        Decimals, TotalSupply, Allowance, NullAddress, 
                        __stateStash, sender_m, mint_to, mint_amount, sender_t, 
                        transfer_to, transfer_amount, sender_a, 
                        approve_spender, approve_amount, sender_tr, 
                        transferFrom_from, transferFrom_to, 
                        transferFrom_amount, sender, recipient, amount >>

Loop == /\ pc = "Loop"
        /\ \E sender_arg \in IDENTITIES \ {ZERO_IDENT}:
             /\ /\ sender' = sender_arg
                /\ stack' = << [ procedure |->  "invokeContract",
                                 pc        |->  "L14",
                                 sender    |->  sender ] >>
                             \o stack
             /\ pc' = "InvokeContract"
        /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                        balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                        Decimals, TotalSupply, Allowance, NullAddress, 
                        __stateStash, sender_, initialize_name, 
                        initialize_symbol, sender_m, mint_to, mint_amount, 
                        sender_t, transfer_to, transfer_amount, sender_a, 
                        approve_spender, approve_amount, sender_tr, 
                        transferFrom_from, transferFrom_to, 
                        transferFrom_amount, recipient, amount >>

L14 == /\ pc = "L14"
       /\ pc' = "Loop"
       /\ UNCHANGED << __currentState, __currentTime, __contractCallDepth, 
                       balance, __temporary, Name, Symbol, BalanceOf, Owner, 
                       Decimals, TotalSupply, Allowance, NullAddress, 
                       __stateStash, stack, sender_, initialize_name, 
                       initialize_symbol, sender_m, mint_to, mint_amount, 
                       sender_t, transfer_to, transfer_amount, sender_a, 
                       approve_spender, approve_amount, sender_tr, 
                       transferFrom_from, transferFrom_to, transferFrom_amount, 
                       sender, recipient, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == initialize \/ mint \/ transfer \/ approve \/ transferFrom
           \/ invokeContract \/ sendTokens \/ throw \/ Main \/ Loop \/ L14
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
========
