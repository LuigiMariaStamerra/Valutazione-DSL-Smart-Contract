pragma solidity >=0.5.7;

contract EtherExchange {
    enum State {
        open
    }
    State public __currentState;

    constructor() {
        __currentState = State.open;
    }

    function deposit() public payable {
        require(__currentState == State.open);
    }

    function send(address payable to, uint amount) public {
        require(__currentState == State.open);
        require(amount <= address(this).balance);
        uint __temporary = amount;
        amount = amount - __temporary;
        to.transfer(__temporary);
    }

    receive() external payable { }


}
