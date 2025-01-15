pragma solidity >=0.5.7;

contract TheDAO {
    enum State {
        open
    }
    mapping(address => uint) public Balances;
    State public __currentState;

    constructor() {
        __currentState = State.open;
    }

    function deposit() public payable {
        require(__currentState == State.open);
        require(msg.value >= 1);
        Balances[msg.sender] = Balances[msg.sender] + msg.value;
    }

    function withdraw() public {
        require(__currentState == State.open);
        require(Balances[msg.sender] >= 1);
        msg.sender.call{value: Balances[msg.sender]}("");
        Balances[msg.sender] = 0;
    }


}
