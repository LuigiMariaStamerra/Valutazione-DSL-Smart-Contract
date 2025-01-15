pragma solidity >=0.4.22 <0.7.0;
pragma experimental ABIEncoderV2;
import "./lib/cml/ConditionalContract.sol";
import "./lib/cml/DateTime.sol";
import "./lib/cml/IntLib.sol";
import "./lib/cml/RealLib.sol";
import "./lib/openzeppelin/PullPayment.sol";
import "./lib/cml/Model.sol";
import "./lib/cml/MapPartyBalance.sol";

contract Auction is ConditionalContract, PullPayment {

	/*
	 * State variables
	 */
	uint public highestBid;
	Model.Party highestBidder;
	Model.Party beneficiary;
	Model.Party auctioneer;
	uint biddingTime;
	bool aborted;
	bool ended;
	using MapPartyBalance for MapPartyBalance.Data;
	MapPartyBalance.Data internal balances;
	uint _contractStart;
	
	/*
	 * Constructor
	 */
	constructor(Model.Party memory _beneficiary, uint _biddingTime) public {
		auctioneer = Model.Party(msg.sender);
		biddingTime = _biddingTime;
		beneficiary = _beneficiary;
		_contractStart = now;
	}
	
	/*
	 * Functions
	 */
	// @notice function for clause Bid
	function bid() public payable
		checkAllowed("Bid")
	{
		require(msg.value > highestBid, "There is already a higher bid.");
		highestBidder = Model.Party(msg.sender);
		highestBid = msg.value;
		balances.get(msg.sender).bid += msg.value;
	}
	
	// @notice function for clause Withdraw
	function withdraw() public
		checkAllowed("Withdraw")
	{
		require(balances.get(msg.sender).bid > 0, "Bidder balance is 0");
		if ( !aborted &&  !ended)
		{	
			if (msg.sender != highestBidder.id)
			{	
				_asyncTransfer(msg.sender , balances.get(msg.sender).bid);
				balances.get(msg.sender).bid = 0;
			}
			if (msg.sender == highestBidder.id && balances.get(msg.sender).bid - highestBid > 0)
			{	
				_asyncTransfer(msg.sender , balances.get(msg.sender).bid - highestBid);
				balances.get(msg.sender).bid -= highestBid;
			}
		}
		else
		{	
			_asyncTransfer(msg.sender , balances.get(msg.sender).bid);
			balances.get(msg.sender).bid = 0;
		}
	}
	
	// @notice function for clause Accept
	function accept() public
		checkAllowed("Accept")
	{
		ended = true;
		_asyncTransfer(beneficiary.id , highestBid);
		highestBid = 0;
	}
	
	// @notice function for clause Reject
	function reject() public
		checkAllowed("Reject")
	{
		ended = true;
		_asyncTransfer(highestBidder.id , highestBid);
		highestBid = 0;
	}
	
	// @notice function for clause Abort
	function abort() public
		checkAllowed("Abort")
	{
		aborted = true;
	}
	
	// Fallback function
	function() external payable {}
	
	function clauseAllowed(bytes32 _clauseId) internal returns (bool) {
		if (_clauseId == "Bid") {
			require( !aborted &&  !ended, "Given condition(s) not met");
			return true;
		}
		if (_clauseId == "Withdraw") {
			return true;
		}
		if (_clauseId == "Accept") {
			require(onlyBy(beneficiary.id), "Caller not authorized");
			require(onlyAfter(DateTime.addDuration(_contractStart, biddingTime), 0, false), "Function called too early");
			require( !aborted &&  !ended, "Given condition(s) not met");
			return true;
		}
		if (_clauseId == "Reject") {
			require(onlyBy(beneficiary.id), "Caller not authorized");
			require(onlyAfter(DateTime.addDuration(_contractStart, biddingTime), 0, false), "Function called too early");
			require( !aborted &&  !ended, "Given condition(s) not met");
			return true;
		}
		if (_clauseId == "Abort") {
			require(onlyBy(auctioneer.id), "Caller not authorized");
			require( !aborted &&  !ended, "Given condition(s) not met");
			return true;
		}
		return false;
	}
	
	function clauseFulfilledTime(bytes32 _clauseId) internal returns (uint) {
		uint max = 0;
		if (_clauseId == "Bid" && (callSuccess(this.bid.selector))) {
			if (max < callTime(this.bid.selector)) {
				max =  callTime(this.bid.selector);
			}
			return max;
		}
		if (_clauseId == "Withdraw" && (callSuccess(this.withdraw.selector))) {
			if (max < callTime(this.withdraw.selector)) {
				max =  callTime(this.withdraw.selector);
			}
			return max;
		}
		if (_clauseId == "Accept" && (callSuccess(this.accept.selector))) {
			if (max < callTime(this.accept.selector)) {
				max =  callTime(this.accept.selector);
			}
			return max;
		}
		if (_clauseId == "Reject" && (callSuccess(this.reject.selector))) {
			if (max < callTime(this.reject.selector)) {
				max =  callTime(this.reject.selector);
			}
			return max;
		}
		if (_clauseId == "Abort" && (callSuccess(this.abort.selector))) {
			if (max < callTime(this.abort.selector)) {
				max =  callTime(this.abort.selector);
			}
			return max;
		}
		return max;
	}
	
	function contractObeyed() internal returns (bool) {
		return true;
	}
	
}
