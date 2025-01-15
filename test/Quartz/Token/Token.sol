pragma solidity >=0.5.7;

contract Token {
    enum State {
        open
    }
    bytes32 public Name;
    bytes32 public Symbol;
    mapping(address => uint) public BalanceOf;
    address public Owner;
    uint public Decimals;
    uint public TotalSupply;
    mapping(address => mapping(address => uint)) public Allowance;
    address public NullAddress;
    State public __currentState;

    constructor(bytes32 name, bytes32 symbol) {
        __currentState = State.open;
        Name = name;
        Symbol = symbol;
        Decimals = 18;
        Owner = msg.sender;
    }

    function mint(address to, uint amount) public {
        require(__currentState == State.open);
        require((to != NullAddress) && (amount > 0));
        if (msg.sender != Owner) {
            return;
        }
        TotalSupply = TotalSupply + amount;
        BalanceOf[to] = BalanceOf[to] + amount;
    }

    function transfer(address to, uint amount) public {
        require(__currentState == State.open);
        require((BalanceOf[msg.sender] >= amount) && (to != NullAddress));
        BalanceOf[msg.sender] = BalanceOf[msg.sender] - amount;
        BalanceOf[to] = BalanceOf[to] + amount;
    }

    function approve(address spender, uint amount) public {
        require(__currentState == State.open);
        Allowance[msg.sender][spender] = amount;
    }

    function transferFrom(address from, address to, uint amount) public {
        require(__currentState == State.open);
        require(((Allowance[from][msg.sender] >= amount) && (BalanceOf[from] >= amount)) && (to != NullAddress));
        Allowance[from][msg.sender] = Allowance[from][msg.sender] - amount;
        BalanceOf[from] = BalanceOf[from] - amount;
        BalanceOf[to] = BalanceOf[to] + amount;
    }


}
