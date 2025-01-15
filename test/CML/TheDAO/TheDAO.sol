pragma solidity >=0.4.22 <0.7.0;
pragma experimental ABIEncoderV2;
import "./lib/cml/ConditionalContract.sol";
import "./lib/cml/DateTime.sol";
import "./lib/cml/IntLib.sol";
import "./lib/cml/RealLib.sol";
import "./lib/openzeppelin/PullPayment.sol";
import "./lib/cml/Model.sol";
import "./lib/cml/MapPartyBalance.sol";

contract TheDAO is ConditionalContract, PullPayment {

	/*
	 * State variables
	 */
	using MapPartyBalance for MapPartyBalance.Data;
	MapPartyBalance.Data internal balances;
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
		balances.get(msg.sender).balance += msg.value;
	}
	
	// @notice function for clause Withdraw
	function withdraw() public
		checkAllowed("Withdraw")
	{
		require(balances.get(msg.sender).balance > 0, "Insufficient balance.");
		_asyncTransfer(Model.Party(msg.sender).id , balances.get(msg.sender).balance);
		balances.get(msg.sender).balance = 0;
	}
	
	// Fallback function
	function() external payable {}
	
	function clauseAllowed(bytes32 _clauseId) internal returns (bool) {
		if (_clauseId == "Deposit") {
			return true;
		}
		if (_clauseId == "Withdraw") {
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
		if (_clauseId == "Withdraw" && (callSuccess(this.withdraw.selector))) {
			if (max < callTime(this.withdraw.selector)) {
				max =  callTime(this.withdraw.selector);
			}
			return max;
		}
		return max;
	}
	
	function contractObeyed() internal returns (bool) {
		return true;
	}
	
}
