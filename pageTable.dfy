newtype int32 = x: int | 0 <= x < 0x1_0000_0000
newtype addr = int32
type addrArray = array<addr>
datatype secondLevelPtr = Some(arr: addrArray) | Nil

class PageTable{

var root: array<secondLevelPtr>
const levelSizes := [10, 10]
const offset := 12
const pageSize: addr := 0x0FFF
var currPfn: addr

predicate pageTableInvariant()
reads this
{0 <= currPfn < 0x100000 &&
root.Length == 0x10_0000

}

constructor() ensures pageTableInvariant(){
  root := new secondLevelPtr[0x10_0000];
  currPfn := 1;
  // completely null

}
method getVpn(vaddr: addr) returns(vpn: addr)
ensures vpn < 0x10_0000{
  var mask := 0xFFC0_0000;
  var bv := (vaddr as bv32 & mask as bv32);
  bv := bv >> 22;
  vpn := bv as addr;
}

method maskVpn(vpn: addr, level: nat) returns(part: addr)
requires 0 <= level <= 1
ensures 0 <= part < 0x10_0000{
  var bv: bv32;
  if(level == 1) {
    var mask := 0x03FF;
    bv := (vpn as bv32 & mask as bv32);
  }
  else {
    var mask := 0xF_FC00;
    bv := (vpn as bv32 & mask as bv32);
    bv := bv >> 10;
  }
  part := bv as addr;
}

// internal functions
method tryInsertMapping(vpn: addr, pfn: addr) returns (err: nat)
requires pageTableInvariant()
modifies root{
  var part1 := maskVpn(vpn, 0);

  var entry1 := root[part1];

  if (entry1 == Nil){
    var a := new addr[levelSizes[0]];
    entry1 := Some(a);
    root[part1] := entry1;
  }


  var part2 := maskVpn(vpn, 1);

  assert entry1.Some?;
  var entry2 := entry1.arr[part2];
  
  if (entry2 == 0){
    entry2 := pfn;
    return 0;
  } else if (entry2 == pfn){
    return 0;
  } else{
    // vaddr is alr in use
    return 1;
  }
}

method tryGetMapping(vpn: addr) returns (pfn: addr){
  var part1 := maskVpn(vpn, 0);

  var entry1 := root[part1];

  if (entry1 == Nil){
    return 0;
  }

  var part2 := maskVpn(vpn, 1);

  assert entry1.Some?;
  var entry2 := entry1.arr[part2];
  
  return entry2;
}

method getPfn(vpn: addr) returns (pfn: addr){
  pfn := tryGetMapping(vpn);
}


method allocate(vaddr: addr, size: addr) returns (err: nat) 
requires pageTableInvariant(){
  var vpn := getVpn(vaddr);

  var pagesNeeded := 1;

  var freePages := 0xF_FFFF - currPfn by {
    assert(currPfn <= 0xF_FFFF);
  }
  if (currPfn == 0 || freePages < pagesNeeded){
    // out of free pages
    return 1;
  }
  
  err := tryInsertMapping(vpn, currPfn);
}

method translate(vaddr: addr) requires false{
  // easy to implement, do later
}

}
