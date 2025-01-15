pragma solidity >=0.4.22 <0.7.0;
pragma experimental ABIEncoderV2;

import "./CLLAddress.sol";
import "./Model.sol";

library MapPartyVoted {

	struct Data {
		mapping(address => Model.Voted) map;
		CLLAddress.CLL mapIdList;
	}
	
	using CLLAddress for CLLAddress.CLL;
    
	function size(Data storage self) public view returns (uint) {
		return self.mapIdList.sizeOf();
	}
	
	function add(Data storage self, address _key, Model.Voted memory _value) public {
		self.map[_key] = _value;
		self.mapIdList.push(_key, true);
	}
	
	function remove(Data storage self, address _key) public {
		if(self.mapIdList.nodeExists(_key)) {
			delete self.map[_key];
			self.mapIdList.remove(_key);
		}
	}
	
	function contains(Data storage self, address _key) public view returns (bool) {
		return self.mapIdList.nodeExists(_key);
	}
	
	function get(Data storage self, address _key) public view returns (Model.Voted storage) {
		return self.map[_key];
	}
	
	function getEntry(Data storage self, uint _index) public view returns (Model.Voted storage) {
		return self.map[self.mapIdList.nodeAt(_index)];
	}
    
	function isEmpty(Data storage self) public view returns (bool) {
		return !self.mapIdList.exists();
	}
	
	function getKeys(Data storage self) public view returns (address[] memory) {
		return self.mapIdList.keys();
	}
    
	function clear(Data storage self) public {
		address[] memory arr = getKeys(self);
		for (uint i = 0; i < arr.length; i++) {
			delete self.map[arr[i]];
			remove(self, arr[i]);
		}
	}
}
