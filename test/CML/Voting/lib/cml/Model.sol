pragma solidity >=0.4.22 <0.7.0;

library Model {
	/*
	 * Structs
	 */
	struct Party {
		address payable id;
	}
	
	struct Voted {
		Model.Party voter;
		bool voted;
	}
	
	struct Votes {
		uint option;
		uint count;
	}
	
}
