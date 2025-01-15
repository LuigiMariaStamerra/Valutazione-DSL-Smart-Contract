pragma solidity >=0.5.7;

contract Auction {
    enum State {
        open,
        closed,
        aborted
    }
    address public Auctioneer;
    address public Beneficiary;
    address payable public HighestBidder;
    uint public HighestBid;
    uint public EndTime;
    mapping(address => uint) public Balances;
    State public __currentState;

    constructor(address beneficiary, uint duration) {
        __currentState = State.open;
        Beneficiary = beneficiary;
        HighestBid = 0;
        EndTime = block.timestamp + duration;
        Auctioneer = msg.sender;
    }

    function bid() public payable {
        require(__currentState == State.open);
        require(msg.value > HighestBid);
        HighestBid = msg.value;
        HighestBidder = payable(msg.sender);
        Balances[HighestBidder] = Balances[HighestBidder] + HighestBid;
    }

    function withdrawOpen() public {
        require(__currentState == State.open);
        require(Balances[msg.sender] > 0);
        if (msg.sender != HighestBidder) {
            uint __temporary = Balances[msg.sender];
            Balances[msg.sender] = Balances[msg.sender] - __temporary;
            payable(msg.sender).transfer(__temporary);
        }
        if ((msg.sender == HighestBidder) && ((Balances[msg.sender] - HighestBid) > 0)) {
            uint __temporary = Balances[msg.sender] - HighestBid;
            Balances[msg.sender] = Balances[msg.sender] - __temporary;
            payable(msg.sender).transfer(__temporary);
        }
    }

    function withdrawClosed() public {
        require(__currentState == State.closed);
        require(Balances[msg.sender] > 0);
        uint __temporary = Balances[msg.sender];
        Balances[msg.sender] = Balances[msg.sender] - __temporary;
        payable(msg.sender).transfer(__temporary);
    }

    function withdrawAborted() public {
        require(__currentState == State.aborted);
        require(Balances[msg.sender] > 0);
        uint __temporary = Balances[msg.sender];
        Balances[msg.sender] = Balances[msg.sender] - __temporary;
        payable(msg.sender).transfer(__temporary);
    }

    function accept() public {
        require(__currentState == State.open);
        require(block.timestamp > EndTime);
        if (msg.sender != Beneficiary) {
            return;
        }
        __currentState = State.closed;
        uint __temporary = HighestBid;
        HighestBid = HighestBid - __temporary;
        payable(msg.sender).transfer(__temporary);
    }

    function reject() public {
        require(__currentState == State.open);
        require(block.timestamp > EndTime);
        if (msg.sender != Beneficiary) {
            return;
        }
        __currentState = State.closed;
        uint __temporary = HighestBid;
        HighestBid = HighestBid - __temporary;
        HighestBidder.transfer(__temporary);
    }

    function abort() public {
        require(__currentState == State.open);
        if (msg.sender != Auctioneer) {
            return;
        }
        __currentState = State.aborted;
    }


}
