contract Token {
  struct BalanceOfTuple {
    uint _balance;
    bool _valid;
  }
  struct TotalSupplyTuple {
    uint _totalSupply;
    bool _valid;
  }
  struct OwnerTuple {
    address _owner;
    bool _valid;
  }
  struct AllowanceTuple {
    uint _amount;
    bool _valid;
  }
  mapping(address=>BalanceOfTuple) balanceOf;
  TotalSupplyTuple totalSupply;
  OwnerTuple owner;
  mapping(address=>mapping(address=>AllowanceTuple)) allowance;
  event Mint(address _to,uint _amount);
  event Transfer(address _from,address _to,uint _amount);
  event TransferFrom(address _from,address _to,address _spender,uint _amount);
  event IncreaseAllowance(address _account,address _spender,uint _increase);
  constructor(string memory _name,string memory _symbol) public {
    updateTotalBalancesOnInsertConstructor_r3();
    updateSymbolOnInsertConstructor_r12(_symbol);
    updateTotalSupplyOnInsertConstructor_r16();
    updateOwnerOnInsertConstructor_r13();
    updateNameOnInsertConstructor_r19(_name);
    updateDecimalsOnInsertConstructor_r10();
  }
  function transferFrom(address _from,address _to,uint _amount) public    {
      bool r18 = updateTransferFromOnInsertRecv_transferFrom_r18(_from,_to,_amount);
      if(r18==false) {
        revert("Rule condition failed");
      }
  }
  function getAllowance(address _account,address _spender) public view  returns (uint) {
      uint _amount = allowance[_account][_spender]._amount;
      return _amount;
  }
  function approve(address _spender,uint _amount) public    {
      bool r11 = updateIncreaseAllowanceOnInsertRecv_approve_r11(_spender,_amount);
      if(r11==false) {
        revert("Rule condition failed");
      }
  }
  function transfer(address _to,uint _amount) public    {
      bool r4 = updateTransferOnInsertRecv_transfer_r4(_to,_amount);
      if(r4==false) {
        revert("Rule condition failed");
      }
  }
  function getTotalSupply() public view  returns (uint) {
      uint _totalSupply = totalSupply._totalSupply;
      return _totalSupply;
  }
  function getBalanceOf(address _account) public view  returns (uint) {
      uint _balance = balanceOf[_account]._balance;
      return _balance;
  }
  function mint(address _to,uint _amount) public    {
      bool r0 = updateMintOnInsertRecv_mint_r0(_to,_amount);
      if(r0==false) {
        revert("Rule condition failed");
      }
  }
  function updateTotalBalancesOnInsertConstructor_r3() private    {
      // Empty()
  }
  function updateTransferFromOnInsertRecv_transferFrom_r18(address _from,address _to,uint _amount) private   returns (bool) {
      address _spender = msg.sender;
      uint _allowance = allowance[_from][_spender]._amount;
      uint _balance = balanceOf[_from]._balance;
      if(_amount<=_balance && _amount<=_allowance) {
        updateSpentTotalOnInsertTransferFrom_r20(_from,_spender,_amount);
        updateTransferOnInsertTransferFrom_r7(_from,_to,_amount);
        emit TransferFrom(_from,_to,_spender,_amount);
        return true;
      }
      return false;
  }
  function updateTransferOnInsertRecv_transfer_r4(address _to,uint _amount) private   returns (bool) {
      address _from = msg.sender;
      uint _balance = balanceOf[_from]._balance;
      if(_amount<=_balance) {
        updateTotalInOnInsertTransfer_r17(_to,_amount);
        updateTotalOutOnInsertTransfer_r9(_from,_amount);
        emit Transfer(_from,_to,_amount);
        return true;
      }
      return false;
  }
  function updateAllowanceOnIncrementAllowanceTotal_r2(address _account,address _spender,int _allowanceTotal) private    {
      int _delta = int(_allowanceTotal);
      uint newValue = updateuintByint(allowance[_account][_spender]._amount,_delta);
      allowance[_account][_spender]._amount = newValue;
  }
  function updateBalanceOfOnIncrementTotalIn_r14(address _account,int _inAmount) private    {
      int _delta = int(_inAmount);
      uint newValue = updateuintByint(balanceOf[_account]._balance,_delta);
      balanceOf[_account]._balance = newValue;
  }
  function updateuintByint(uint x,int delta) private   returns (uint) {
      int convertedX = int(x);
      int value = convertedX+delta;
      uint convertedValue = uint(value);
      return convertedValue;
  }
  function updateTotalOutOnInsertTransfer_r9(address _account,uint _amount) private    {
      int delta0 = int(_amount);
      updateBalanceOfOnIncrementTotalOut_r14(_account,delta0);
  }
  function updateNameOnInsertConstructor_r19(string memory _name) private    {
      // Empty()
  }
  function updateSpentTotalOnInsertTransferFrom_r20(address _account,address _spender,uint _amount) private    {
      int delta0 = int(_amount);
      updateAllowanceOnIncrementSpentTotal_r2(_account,_spender,delta0);
  }
  function updateIncreaseAllowanceOnInsertRecv_approve_r11(address _spender,uint _amount) private   returns (bool) {
      address _account = msg.sender;
      uint _allowance = allowance[_account][_spender]._amount;
      uint _increase = _amount-_allowance;
      updateAllowanceTotalOnInsertIncreaseAllowance_r5(_account,_spender,_increase);
      emit IncreaseAllowance(_account,_spender,_increase);
      return true;
      return false;
  }
  function updateBalanceOfOnIncrementTotalMint_r14(address _account,int _mintAmount) private    {
      int _delta = int(_mintAmount);
      uint newValue = updateuintByint(balanceOf[_account]._balance,_delta);
      balanceOf[_account]._balance = newValue;
  }
  function updateBalanceOfOnIncrementTotalOut_r14(address _account,int _outAmount) private    {
      int _delta = int(-_outAmount);
      uint newValue = updateuintByint(balanceOf[_account]._balance,_delta);
      balanceOf[_account]._balance = newValue;
  }
  function updateAllowanceTotalOnInsertIncreaseAllowance_r5(address _account,address _spender,uint _increase) private    {
      int delta0 = int(_increase);
      updateAllowanceOnIncrementAllowanceTotal_r2(_account,_spender,delta0);
  }
  function updateTransferOnInsertTransferFrom_r7(address _from,address _to,uint _amount) private    {
      updateTotalInOnInsertTransfer_r17(_to,_amount);
      updateTotalOutOnInsertTransfer_r9(_from,_amount);
      emit Transfer(_from,_to,_amount);
  }
  function updateAllowanceOnIncrementSpentTotal_r2(address _account,address _spender,int _spentTotal) private    {
      int _delta = int(-_spentTotal);
      uint newValue = updateuintByint(allowance[_account][_spender]._amount,_delta);
      allowance[_account][_spender]._amount = newValue;
  }
  function updateTotalInOnInsertTransfer_r17(address _account,uint _amount) private    {
      int delta0 = int(_amount);
      updateBalanceOfOnIncrementTotalIn_r14(_account,delta0);
  }
  function updateTotalMintOnInsertMint_r6(address _account,uint _amount) private    {
      int delta0 = int(_amount);
      updateBalanceOfOnIncrementTotalMint_r14(_account,delta0);
  }
  function updateSymbolOnInsertConstructor_r12(string memory _symbol) private    {
      // Empty()
  }
  function updateDecimalsOnInsertConstructor_r10() private    {
      // Empty()
  }
  function updateMintOnInsertRecv_mint_r0(address _to,uint _amount) private   returns (bool) {
      address _owner = owner._owner;
      if(_owner==msg.sender) {
        if(_to!=address(0) && _amount>0) {
          updateTotalMintOnInsertMint_r6(_to,_amount);
          updateTotalSupplyOnInsertMint_r1(_amount);
          emit Mint(_to,_amount);
          return true;
        }
      }
      return false;
  }
  function updateTotalSupplyOnInsertConstructor_r16() private    {
      totalSupply = TotalSupplyTuple(0,true);
  }
  function updateOwnerOnInsertConstructor_r13() private    {
      address _sender = msg.sender;
      owner = OwnerTuple(_sender,true);
  }
  function updateTotalSupplyOnInsertMint_r1(uint _amount) private    {
      totalSupply._totalSupply += _amount;
  }
}