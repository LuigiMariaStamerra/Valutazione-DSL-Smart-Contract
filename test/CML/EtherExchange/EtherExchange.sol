pragma solidity >=0.4.22 <0.7.0;
pragma experimental ABIEncoderV2;
import "./lib/cml/ConditionalContract.sol";
import "./lib/cml/DateTime.sol";
import "./lib/cml/IntLib.sol";
import "./lib/cml/RealLib.sol";
import "./lib/openzeppelin/PullPayment.sol";
import "./lib/cml/Model.sol";

contract EtherExchange is ConditionalContract, PullPayment {

	/*
	 * State variables
	 */
	uint _contractStart;
	
	/*
	 * Constructor
	 */
	constructor() public {
		_contractStart = now;
	}
	
	/*
	 * Functions
	 */
	// @notice function for clause Deposit
	function deposit() public payable
		checkAllowed("Deposit")
	{
	}
	
	// @notice function for clause Send
	function send(Model.Party memory to, uint amount) public
		checkAllowed("Send")
	{
		require(amount <= address(this).balance, "Insufficient contract balance.");
		_asyncTransfer(to.id , amount);
	}
	
	// Fallback function
	function() external payable {}
	
	function clauseAllowed(bytes32 _clauseId) internal returns (bool) {
		if (_clauseId == "Deposit") {
			return true;
		}
		if (_clauseId == "Send") {
			return true;
		}
		return false;
	}
	
	function clauseFulfilledTime(bytes32 _clauseId) internal returns (uint) {
		uint max = 0;
		if (_clauseId == "Deposit" && (callSuccess(this.deposit.selector))) {
			if (max < callTime(this.deposit.selector)) {
				max =  callTime(this.deposit.selector);
			}
			return max;
		}
		if (_clauseId == "Send" && (callSuccess(this.send.selector))) {
			if (max < callTime(this.send.selector)) {
				max =  callTime(this.send.selector);
			}
			return max;
		}
		return max;
	}
	
	function contractObeyed() internal returns (bool) {
		return true;
	}
	
}
