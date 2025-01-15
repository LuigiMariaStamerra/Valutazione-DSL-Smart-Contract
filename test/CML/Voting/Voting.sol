pragma solidity >=0.4.22 <0.7.0;
pragma experimental ABIEncoderV2;
import "./lib/cml/ConditionalContract.sol";
import "./lib/cml/DateTime.sol";
import "./lib/cml/IntLib.sol";
import "./lib/cml/RealLib.sol";
import "./lib/cml/Model.sol";
import "./lib/cml/MapPartyVoted.sol";
import "./lib/cml/MapUintVotes.sol";

contract Voting is ConditionalContract {

	/*
	 * State variables
	 */
	Model.Party organizer;
	uint options;
	uint votingTime;
	using MapPartyVoted for MapPartyVoted.Data;
	MapPartyVoted.Data internal voted;
	using MapUintVotes for MapUintVotes.Data;
	MapUintVotes.Data internal votes;
	bool ended;
	uint public winner;
	uint _contractStart;
	
	/*
	 * Constructor
	 */
	constructor(uint _options, uint _votingTime) public {
		options = _options;
		votingTime = _votingTime;
		organizer = Model.Party(msg.sender);
		_contractStart = now;
	}
	
	/*
	 * Functions
	 */
	// @notice function for clause Vote
	function vote(uint option) public
		checkAllowed("Vote")
	{
		require(option > 0 && option <= options, "Option not valid.");
		votes.get(option).count += 1;
		voted.get(msg.sender).voted = true;
		if (votes.get(option).count > votes.get(winner).count)
		{	
			winner = option;
		}
	}
	
	// @notice function for clause Close
	function close() public
		checkAllowed("Close")
	{
		ended = true;
	}
	
	// Fallback function
	function() external payable {}
	
	function clauseAllowed(bytes32 _clauseId) internal returns (bool) {
		if (_clauseId == "Vote") {
			require( !ended && voted.get(msg.sender).voted == false, "Given condition(s) not met");
			return true;
		}
		if (_clauseId == "Close") {
			require(onlyBy(organizer.id), "Caller not authorized");
			require(onlyAfter(DateTime.addDuration(_contractStart, votingTime), 0, false), "Function called too early");
			require( !ended, "Given condition(s) not met");
			return true;
		}
		return false;
	}
	
	function clauseFulfilledTime(bytes32 _clauseId) internal returns (uint) {
		uint max = 0;
		if (_clauseId == "Vote" && (callSuccess(this.vote.selector))) {
			if (max < callTime(this.vote.selector)) {
				max =  callTime(this.vote.selector);
			}
			return max;
		}
		if (_clauseId == "Close" && (callSuccess(this.close.selector))) {
			if (max < callTime(this.close.selector)) {
				max =  callTime(this.close.selector);
			}
			return max;
		}
		return max;
	}
	
	function contractObeyed() internal returns (bool) {
		return true;
	}
	
}
