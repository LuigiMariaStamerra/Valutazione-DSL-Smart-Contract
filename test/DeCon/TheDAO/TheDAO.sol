contract TheDAO {
  struct BalancesTuple {
    uint _balance;
    bool _valid;
  }
  mapping(address=>BalancesTuple) balances;
  event Withdraw(address _to,uint _amount);
  event Deposit(address _from,uint _amount);
  function getBalances(address _account) public view  returns (uint) {
      uint _balance = balances[_account]._balance;
      return _balance;
  }
  function deposit() public  payable  {
      bool r0 = updateDepositOnInsertRecv_deposit_r0();
      if(r0==false) {
        revert("Rule condition failed");
      }
  }
  function withdraw() public    {
      bool r3 = updateWithdrawOnInsertRecv_withdraw_r3();
      if(r3==false) {
        revert("Rule condition failed");
      }
  }
  function updateTotalDepositOnInsertDeposit_r2(address _account,uint _deposit) private    {
      int delta0 = int(_deposit);
      updateBalancesOnIncrementTotalDeposit_r4(_account,delta0);
  }
  function updateBalancesOnIncrementTotalWithdraw_r4(address _account,int _totalWithdraw) private    {
      int _delta = int(-_totalWithdraw);
      uint newValue = updateuintByint(balances[_account]._balance,_delta);
      balances[_account]._balance = newValue;
  }
  function updateDepositOnInsertRecv_deposit_r0() private   returns (bool) {
      uint _amount = msg.value;
      address _from = msg.sender;
      updateTotalDepositOnInsertDeposit_r2(_from,_amount);
      emit Deposit(_from,_amount);
      return true;
      return false;
  }
  function updateTotalWithdrawOnInsertWithdraw_r1(address _account,uint _withdraw) private    {
      int delta0 = int(_withdraw);
      updateBalancesOnIncrementTotalWithdraw_r4(_account,delta0);
  }
  function updateuintByint(uint x,int delta) private   returns (uint) {
      int convertedX = int(x);
      int value = convertedX+delta;
      uint convertedValue = uint(value);
      return convertedValue;
  }
  function updateWithdrawOnInsertRecv_withdraw_r3() private   returns (bool) {
      address _to = msg.sender;
      uint _amount = balances[_to]._balance;
      updateTotalWithdrawOnInsertWithdraw_r1(_to,_amount);
      updateSendOnInsertWithdraw_r5(_to,_amount);
      emit Withdraw(_to,_amount);
      return true;
      return false;
  }
  function updateSendOnInsertWithdraw_r5(address _to,uint _amount) private    {
      payable(_to).send(_amount);
  }
  function updateBalancesOnIncrementTotalDeposit_r4(address _account,int _totalDeposit) private    {
      int _delta = int(_totalDeposit);
      uint newValue = updateuintByint(balances[_account]._balance,_delta);
      balances[_account]._balance = newValue;
  }
}