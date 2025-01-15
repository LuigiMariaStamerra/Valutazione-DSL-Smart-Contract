contract Auction {
  struct EndTimeTuple {
    uint _endTime;
    bool _valid;
  }
  struct HighestBidTuple {
    address _bidder;
    uint _bid;
    bool _valid;
  }
  struct EndedTuple {
    bool _ended;
    bool _valid;
  }
  struct BalanceTuple {
    uint _amount;
    bool _valid;
  }
  struct AbortedTuple {
    bool _aborted;
    bool _valid;
  }
  struct BeneficiaryTuple {
    address _beneficiary;
    bool _valid;
  }
  struct WithdrawWinnerCountTuple {
    uint _count;
    bool _valid;
  }
  struct OwnerTuple {
    address _owner;
    bool _valid;
  }
  EndTimeTuple endTime;
  HighestBidTuple public highestBid;
  EndedTuple ended;
  OwnerTuple owner;
  mapping(address=>BalanceTuple) balance;
  BeneficiaryTuple beneficiary;
  WithdrawWinnerCountTuple withdrawWinnerCount;
  AbortedTuple aborted;
  event WithdrawWinner(address _recipient,uint _amount);
  event Bid(address _bidder,uint _amount);
  event Withdraw(address _bidder,uint _amount);
  event Aborted(bool _aborted);
  constructor(address _beneficiary,uint _biddingTime) public {
    updateBeneficiaryOnInsertConstructor_r8(_beneficiary);
    updateOwnerOnInsertConstructor_r15();
    updateEndTimeOnInsertConstructor_r13(_biddingTime);
  }
  function withdraw() public    {
      bool r16 = updateWithdrawOnInsertRecv_withdraw_r16();
      bool r17 = updateWithdrawOnInsertRecv_withdraw_r17();
      bool r14 = updateWithdrawOnInsertRecv_withdraw_r14();
      if(r16==false && r17==false && r14==false) {
        revert("Rule condition failed");
      }
  }
  function reject() public    {
      bool r6 = updateWithdrawWinnerOnInsertRecv_reject_r6();
      if(r6==false) {
        revert("Rule condition failed");
      }
  }
  function abort() public    {
      bool r0 = updateAbortedOnInsertRecv_abort_r0();
      if(r0==false) {
        revert("Rule condition failed");
      }
  }
  function bid() public  payable  {
      bool r3 = updateBidOnInsertRecv_bid_r3();
      if(r3==false) {
        revert("Rule condition failed");
      }
  }
  function accept() public    {
      bool r11 = updateWithdrawWinnerOnInsertRecv_accept_r11();
      if(r11==false) {
        revert("Rule condition failed");
      }
  }
  function updateWithdrawOnInsertRecv_withdraw_r17() private   returns (bool) {
      address _highestBidder = highestBid._bidder;
      address _bidder = msg.sender;
      uint _amount = balance[_bidder]._amount;
      if(_bidder!=_highestBidder && _amount>0) {
        updateSendOnInsertWithdraw_r7(_bidder,_amount);
        updateWithdrawTotalOnInsertWithdraw_r9(_bidder,_amount);
        emit Withdraw(_bidder,_amount);
        return true;
      }
      return false;
  }
  function updateWithdrawWinnerOnInsertRecv_reject_r6() private   returns (bool) {
      uint _nowTime = block.timestamp;
      if(false==aborted._aborted) {
        address _sender = beneficiary._beneficiary;
        uint _endTime = endTime._endTime;
        if(_sender==msg.sender) {
          if(false==ended._ended) {
            address _recipient = highestBid._bidder;
            uint _amount = highestBid._bid;
            if(_nowTime>=_endTime) {
              updateWithdrawWinnerCountOnInsertWithdrawWinner_r4(_recipient,_amount);
              updateSendOnInsertWithdrawWinner_r10(_recipient,_amount);
              emit WithdrawWinner(_recipient,_amount);
              return true;
            }
          }
        }
      }
      return false;
  }
  function updateAbortedOnInsertRecv_abort_r0() private   returns (bool) {
      address _sender = msg.sender;
      if(_sender==owner._owner) {
        if(false==ended._ended) {
          if(false==aborted._aborted) {
            aborted = AbortedTuple(true,true);
            emit Aborted(true);
            return true;
          }
        }
      }
      return false;
  }
  function updateWithdrawWinnerOnInsertRecv_accept_r11() private   returns (bool) {
      uint _amount = highestBid._bid;
      uint _endTime = endTime._endTime;
      uint _nowTime = block.timestamp;
      if(false==aborted._aborted) {
        address _sender = beneficiary._beneficiary;
        if(_sender==msg.sender) {
          if(false==ended._ended) {
            if(_nowTime>=_endTime) {
              updateSendOnInsertWithdrawWinner_r10(_sender,_amount);
              updateWithdrawWinnerCountOnInsertWithdrawWinner_r4(_sender,_amount);
              emit WithdrawWinner(_sender,_amount);
              return true;
            }
          }
        }
      }
      return false;
  }
  function updateWithdrawTotalOnInsertWithdraw_r9(address _bidder,uint _amount) private    {
      int delta0 = int(_amount);
      updateBalanceOnIncrementWithdrawTotal_r5(_bidder,delta0);
  }
  function updateuintByint(uint x,int delta) private   returns (uint) {
      int convertedX = int(x);
      int value = convertedX+delta;
      uint convertedValue = uint(value);
      return convertedValue;
  }
  function updateSendOnInsertWithdrawWinner_r10(address _recipient,uint _amount) private    {
      payable(_recipient).send(_amount);
  }
  function updateBeneficiaryOnInsertConstructor_r8(address _beneficiary) private    {
      beneficiary = BeneficiaryTuple(_beneficiary,true);
  }
  function updateEndedOnInsertWithdrawWinnerCount_r1(uint _count) private    {
      if(_count>=1) {
        ended = EndedTuple(true,true);
      }
  }
  function updateWithdrawOnInsertRecv_withdraw_r16() private   returns (bool) {
      if(true==aborted._aborted) {
        address _bidder = msg.sender;
        uint _amount = balance[_bidder]._amount;
        updateSendOnInsertWithdraw_r7(_bidder,_amount);
        updateWithdrawTotalOnInsertWithdraw_r9(_bidder,_amount);
        emit Withdraw(_bidder,_amount);
        return true;
      }
      return false;
  }
  function updateBalanceOnIncrementWithdrawTotal_r5(address _bidder,int _withdrawTotal) private    {
      int _delta = int(-_withdrawTotal);
      uint newValue = updateuintByint(balance[_bidder]._amount,_delta);
      balance[_bidder]._amount = newValue;
  }
  function updateBidOnInsertRecv_bid_r3() private   returns (bool) {
      address _bidder = msg.sender;
      uint _amount = msg.value;
      if(false==ended._ended) {
        uint _bid = highestBid._bid;
        if(false==aborted._aborted) {
          if(_amount>_bid) {
            updateBidTotalOnInsertBid_r2(_bidder,_amount);
            updateHighestBidOnInsertBid_r12(_bidder,_amount);
            emit Bid(_bidder,_amount);
            return true;
          }
        }
      }
      return false;
  }
  function updateOwnerOnInsertConstructor_r15() private    {
      address _sender = msg.sender;
      owner = OwnerTuple(_sender,true);
  }
  function updateEndedOnIncrementWithdrawWinnerCount_r1(int _count) private    {
      int _delta = int(_count);
      uint newValue = updateuintByint(withdrawWinnerCount._count,_delta);
      updateEndedOnInsertWithdrawWinnerCount_r1(newValue);
  }
  function updateBalanceOnIncrementBidTotal_r5(address _bidder,int _bidTotal) private    {
      int _delta = int(_bidTotal);
      uint newValue = updateuintByint(balance[_bidder]._amount,_delta);
      balance[_bidder]._amount = newValue;
  }
  function updateHighestBidOnInsertBid_r12(address _bidder,uint _bid) private    {
      uint _max = highestBid._bid;
      if(_bid>_max) {
        highestBid = HighestBidTuple(_bidder,_bid,true);
      }
  }
  function updateSendOnInsertWithdraw_r7(address _bidder,uint _amount) private    {
      payable(_bidder).send(_amount);
  }
  function updateEndTimeOnInsertConstructor_r13(uint _biddingTime) private    {
      uint _nowTime = block.timestamp;
      uint _endTime = _nowTime+_biddingTime;
      endTime = EndTimeTuple(_endTime,true);
  }
  function updateWithdrawOnInsertRecv_withdraw_r14() private   returns (bool) {
      address _bidder = highestBid._bidder;
      uint _bid = highestBid._bid;
      if(_bidder==msg.sender) {
        uint _balance = balance[_bidder]._amount;
        if(_balance>_bid) {
          uint _amount = _balance-_bid;
          updateSendOnInsertWithdraw_r7(_bidder,_amount);
          updateWithdrawTotalOnInsertWithdraw_r9(_bidder,_amount);
          emit Withdraw(_bidder,_amount);
          return true;
        }
      }
      return false;
  }
  function updateWithdrawWinnerCountOnInsertWithdrawWinner_r4(address __recipient0,uint __amount1) private    {
      int delta1 = int(1);
      updateEndedOnIncrementWithdrawWinnerCount_r1(delta1);
      withdrawWinnerCount._count += 1;
  }
  function updateBidTotalOnInsertBid_r2(address _bidder,uint _amount) private    {
      int delta0 = int(_amount);
      updateBalanceOnIncrementBidTotal_r5(_bidder,delta0);
  }
}