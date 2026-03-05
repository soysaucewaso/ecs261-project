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
// all pageTables have exactly `numVpns` entries
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
/*lemma insertThenGet(vpnPart1: addr, vpnPart2: addr, pfn: addr)
requires 0 <= vpnPart1 < numVpnParts
requires 0 <= vpnPart2 < numVpnParts{
  var err := tryInsertMapping(vpnPart1, vpnPart2, pfn);

}*/

method getVpn(vaddr: addr) returns(vpn: addr)
ensures 0 <= vpn < numVpns{
  var mask := 0xFFC0_0000;
  var bv := (vaddr as bv32 & mask as bv32);
  bv := bv >> 22;
  vpn := bv as addr;
}

method maskVpn(vpn: addr) returns(part1: addr, part2: addr)
requires 0 <= vpn < numVpns
ensures 0 <= part1 < numVpnParts
ensures 0 <= part2 < numVpnParts
{
  // splitting a page number into two indexes.
  var mask1: bv32 := 0x03FF;
  var b1 := (vpn as bv32 & mask1);
  assert(b1 <= mask1);
  assert(b1 as nat <= mask1 as nat);


  var mask2 := 0xF_FC00;
  var b2 := (vpn as bv32 & mask2 as bv32);
  assert(b2 <= mask2);
  b2 := b2 >> 10;
  assert(b2 <= mask2 >> 10);
  assert(mask2 >> 10 == 0x03FF as bv32);
  assert(b2 <= 0x03FF as bv32);
  part1 := b1 as addr;    
  part2 := b2 as addr;    
}

// internal functions
method tryInsertMapping(vpnPart1: addr, vpnPart2: addr, pfn: addr) returns (err: nat)
requires pageTableInvariant()
requires 0 <= vpnPart1 < numVpnParts
requires 0 <= vpnPart2 < numVpnParts
ensures 0 <= err <= 1
ensures pageTableInvariant()
ensures err == 0 ==> root[vpnPart1].Some? && root[vpnPart1].arr[vpnPart2] == pfn
modifies root
modifies if root[vpnPart1].Some? then {root[vpnPart1].arr} else {}
{
assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));

  var entry1 := root[vpnPart1];

  if (entry1 == Nil){
    var a := new addr[numVpnParts];
    entry1 := Some(a);
    root[vpnPart1] := entry1;
    assert(entry1.arr.Length == numVpnParts as int);
    entry1.arr[0] := 1;
  }


  assert entry1.Some?;

  var entry2: addr := entry1.arr[vpnPart2] by {
    assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));
    assert(0 <= vpnPart2 < numVpnParts);
  }
  
  if (entry2 == 0){
    entry2 := pfn;
    entry1.arr[vpnPart2] := entry2;
  }
  

  if (entry2 == pfn){
    // important assertions
    var getPfn := tryGetMapping(vpnPart1, vpnPart2);
    assert(pfn == getPfn);
    return 0;
  } else{
    // vaddr is alr in use
    // TODO use a free entry
    return 1;
  }
}

method tryGetMapping(vpnPart1: addr, vpnPart2: addr) returns (pfn: addr)
  requires 0 <= vpnPart1 < numVpnParts
  requires 0 <= vpnPart2 < numVpnParts
  requires pageTableInvariant()
ensures pageTableInvariant()
ensures root[vpnPart1].Some? ==> pfn == root[vpnPart1].arr[vpnPart2]
{

  var entry1 := root[vpnPart1];

  if (entry1 == Nil){
    return 0;
  }

  assert entry1.Some?;
  var entry2 := entry1.arr[vpnPart2];
  
  return entry2;
}

method getPfn(vpn: addr) returns (pfn: addr)
requires false{
  //pfn := tryGetMapping(vpn);
}


method allocate(vaddr: addr, size: addr) returns (err: nat) 
requires pageTableInvariant()
ensures pageTableInvariant()
modifies root
modifies set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr
modifies this{
  var pagesNeeded := 1;

  var freePages := 0xF_FFFF - currPfn by {
    assert(currPfn <= 0xF_FFFF);
  }
  if (currPfn == 0 || freePages < pagesNeeded){
    // out of free pages
    return 1;
  }
  
  var vpn := getVpn(vaddr);

  var part1, part2 := maskVpn(vpn);
  err := tryInsertMapping(part1, part2, currPfn);
}

method translate(vaddr: addr) requires false{
  // easy to implement, do later
}

}

/*method main(){
  var pt := new PageTable();
}*/
