pragma solidity >=0.4.22 <0.7.0;

library Model {
	/*
	 * Structs
	 */
	struct Party {
		address payable id;
	}
	
	struct Balance {
		Model.Party user;
		uint balance;
	}
	
}
