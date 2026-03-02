newtype int32 = x: int | 0 <= x < 0x1_0000_0000
newtype addr = int32
type addrArray = array<addr>

datatype secondLevelPtr = Nil | Some(arr: addrArray) 

class PageTable{

var root: array<secondLevelPtr>
const levelSizes := [10, 10]
const offset := 12
const pageSize: addr := 0x0FFF
const numVpns: addr := 0x0010_0000
const numOffsets := 0x1000
const numVpnParts: addr := 0x0400
var currPfn: addr

predicate pageTableInvariant()
reads this
reads root
{0 <= currPfn < numVpns &&
root.Length == numVpns as int &&
forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int))
}

constructor() 
ensures pageTableInvariant()
ensures fresh(root)
{

  root := new secondLevelPtr[numVpns];

  new;

  assert(root.Length == numVpns as int);
  for i := 0 to numVpns as int
    invariant root.Length == numVpns as int
    invariant 0 <= i <= root.Length
    invariant forall j: nat :: 0 <= j < i ==> root[j] == Nil
    invariant fresh(root){
    root[i] := Nil by {
      assert(root.Length == numVpns as int);

    }
  }
  currPfn := 1;
  assert(currPfn == 1 as addr);
  assert(!root[0].Some?);
  //assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil)));
  // completely null

}
method getVpn(vaddr: addr) returns(vpn: addr)
ensures 0 <= vpn < numVpns{
  var mask := 0xFFC0_0000;
  var bv := (vaddr as bv32 & mask as bv32);
  bv := bv >> 22;
  vpn := bv as addr;
}

method maskVpn(vpn: addr, level: nat) returns(part: addr)
requires 0 <= level <= 1
ensures 0 <= part < numVpnParts
{
  var bv: bv32;
  if(level == 1) {
    var mask: bv32 := 0x03FF;
    bv := (vpn as bv32 & mask);
    assert(bv <= mask);
    assert(bv as nat <= mask as nat);
  }
  else {
    var mask := 0xF_FC00;
    bv := (vpn as bv32 & mask as bv32);
    assert(bv <= mask);
    bv := bv >> 10;
    assert(bv <= mask >> 10);
    assert(mask >> 10 == 0x03FF as bv32);
    assert(bv <= 0x03FF as bv32);
  }
  part := bv as addr;    
  assert(bv <= 0x03FF);
}

// internal functions
method tryInsertMapping(vpn: addr, pfn: addr) returns (err: nat)
requires pageTableInvariant()
ensures 0 <= err <= 1
modifies root{
  assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));

  var part1 := maskVpn(vpn, 0);

  var entry1 := root[part1];

  if (entry1 == Nil){
    var a := new addr[numVpnParts];
    entry1 := Some(a);
    root[part1] := entry1;
    assert(entry1.arr.Length == numVpnParts as int);
  }


  var part2 := maskVpn(vpn, 1);

  assert entry1.Some?;

  var entry2 := entry1.arr[part2] by {
    assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));
    assert(0 <= part2 < numVpnParts);
  }
  
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

method tryGetMapping(vpn: addr) returns (pfn: addr)
  requires 0 <= vpn < numVpns
  requires pageTableInvariant(){
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

method getPfn(vpn: addr) returns (pfn: addr)
requires false{
  //pfn := tryGetMapping(vpn);
}


method allocate(vaddr: addr, size: addr) returns (err: nat) 
requires pageTableInvariant()
modifies root
modifies this{
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
