contract EtherExchange {
  event Deposit(address _from,uint _amount);
  event Send(address p,uint amount);
  function deposit() public  payable  {
      bool r0 = updateDepositOnInsertRecv_deposit_r0();
      if(r0==false) {
        revert("Rule condition failed");
      }
  }
  function send(address _to,uint _amount) public    {
      bool r1 = updateSendOnInsertRecv_send_r1(_to,_amount);
      if(r1==false) {
        revert("Rule condition failed");
      }
  }
  function updateSendOnInsertRecv_send_r1(address _to,uint _amount) private   returns (bool) {
      uint _balance = address(this).balance;
      if(_amount<=_balance) {
        payable(_to).send(_amount);
        emit Send(_to,_amount);
        return true;
      }
      return false;
  }
  function updateDepositOnInsertRecv_deposit_r0() private   returns (bool) {
      uint _amount = msg.value;
      address _from = msg.sender;
      emit Deposit(_from,_amount);
      return true;
      return false;
  }
  function updateuintByint(uint x,int delta) private   returns (uint) {
      int convertedX = int(x);
      int value = convertedX+delta;
      uint convertedValue = uint(value);
      return convertedValue;
  }
}