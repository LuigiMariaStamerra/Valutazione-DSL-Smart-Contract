pragma solidity >=0.5.7;

contract Voting {
    enum State {
        open,
        closed
    }
    address public Organizer;
    uint public Options;
    uint public EndTime;
    address[] public Voted;
    mapping(uint => uint) public Votes;
    uint public Winner;
    State public __currentState;

    constructor(uint options, uint duration) {
        __currentState = State.open;
        Organizer = msg.sender;
        Options = options;
        EndTime = block.timestamp + duration;
    }

    function vote(uint option) public {
        require(__currentState == State.open);
        require(((!(sequenceContains(Voted, msg.sender))) && (option > 0)) && (option <= Options));
        Votes[option] = Votes[option] + 1;
        Voted.push(msg.sender);
        if (((Winner != 0) && (Votes[option] > Votes[Winner])) || (Winner == 0)) {
            Winner = option;
        }
    }

    function close() public {
        require(__currentState == State.open);
        require(block.timestamp > EndTime);
        if (msg.sender != Organizer) {
            return;
        }
        __currentState = State.closed;
    }

    function sequenceContains(address[] storage sequence, address element) private view returns (bool) {
        for (uint i = 0; i < sequence.length; i++) {
            if (sequence[i] == element) {
                return true;
            }
        }
        return false;
    }

}
