newtype int32 = x: int | 0 <= x < 0x1_0000_0000
newtype addr = int32
type addrArray = array<addr>

datatype secondLevelPtr = Nil | Some(arr: addrArray)

class PageTable{

  var root: array<secondLevelPtr>
  // TLB cache: small hardware-style cache for VPN -> PFN mappings
  const tlbSize: int := 16
  var tlbKeys: array<addr>
  var tlbVals: array<addr>
  var tlbValid: array<bool>
  var tlbNext: nat
  const levelSizes := [10, 10]
  const offset := 12
  const pageSize: addr := 0x0FFF
  const numVpns: addr := 0x0010_0000
  const numOffsets: addr := 0x1000
  const numVpnParts: addr := 0x0400
  var currPfn: addr

  predicate tlbInvariant()
    reads this
    reads tlbValid, tlbKeys, tlbVals
    {
   tlbKeys.Length == tlbSize &&
   tlbVals.Length == tlbSize &&
   tlbValid.Length == tlbSize &&
   0 <= tlbNext < tlbSize
    }
  
  predicate pageInvariant()
    reads this 
    reads root
    reads tlbValid, tlbKeys, tlbVals
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
    {
    0 < currPfn < numVpns &&
   root.Length == numVpnParts as int &&
   // all pageTables have exactly `numVpns` entries
   (forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int))) &&
   (forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j : nat :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < currPfn)))


    }

  predicate pageTableInvariant()
    reads this
    reads root
    reads tlbValid, tlbKeys, tlbVals
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
   tlbInvariant() && pageInvariant() &&
   // when valid, TLB entries carry valid vpn/pfn ranges
   (forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && tlbVals[i] < currPfn))) 
  }

  constructor()
    ensures pageTableInvariant()
    ensures fresh(root)
    ensures forall j: nat :: 0 <= j < tlbSize ==> tlbValid[j] == false
  {

    root := new secondLevelPtr[numVpnParts];

    new;

    assert(root.Length == numVpnParts as int);
    for i := 0 to numVpnParts as int
      invariant root.Length == numVpnParts as int
      invariant 0 <= i <= root.Length
      invariant forall j: nat :: 0 <= j < i ==> root[j] == Nil
      invariant fresh(root)
      {
      root[i] := Nil by {
        assert(root.Length == numVpnParts as int);

      }
    }
    assert(!root[0].Some?);
    // initialize TLB
    tlbKeys := new addr[tlbSize];
    tlbVals := new addr[tlbSize];
    tlbValid := new bool[tlbSize];
    tlbNext := 0;
    currPfn := 1;
    assert(currPfn == 1 as addr);
    //assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil)));
    // completely null
    for i := 0 to tlbSize as int
      invariant 0 <= i <= tlbSize as int
      invariant root.Length == numVpnParts as int
      invariant fresh(tlbKeys) && fresh(tlbVals) && fresh(tlbValid)
      invariant fresh(root)
      invariant forall j: nat :: 0 <= j < i ==> j < tlbValid.Length && !tlbValid[j]
      invariant currPfn == 1 as addr
      // can prove everything except properties about tlbValid
      invariant pageInvariant() && tlbInvariant()
    {
      tlbValid[i] := false;
    }
    assert forall j: nat :: 0 <= j < tlbSize ==> !tlbValid[j];
    assert(currPfn == 1 as addr);

  }
  /*lemma insertThenGet(vpnPart1: addr, vpnPart2: addr, pfn: addr)
    requires 0 <= vpnPart1 < numVpnParts
    requires 0 <= vpnPart2 < numVpnParts{
    var err := tryInsertMapping(vpnPart1, vpnPart2, pfn);
  }
  */
  lemma bvLess(a: nat, b: nat)
    requires 0 <= a <= 0xFFFF_FFFF
    requires 0 <= b <= 0xFFFF_FFFF
    requires a < b
    //ensures a as bv32 < b as bv32
  {
  }

  lemma bvLessAddr(a: addr, b: addr)
    requires 0 <= a <= 0xFFFF_FFFF
    requires 0 <= b <= 0xFFFF_FFFF
    requires a < b
    //ensures a as bv32 < b as bv32
  {
    var aNat := a as nat;
    var bNat := b as nat;
    //assert(aNat as bv32 < bNat as bv32) by {
    //bvLess(aNat, bNat);
    //}
  }

  method buildAddr(pfn: addr, offset: addr)
    returns (a: addr)
    requires 0 <= pfn < numVpns
    requires 0 <= offset < numOffsets
    //ensures (a as bv32 & 0xFFF) == offset as bv32
    //ensures (a as bv32 >> 12) == pfn as bv32
  {
    var mask1: bv32 := 0xF_FFFF;
    var b1 := (pfn as bv32 & mask1);
    //assert(b1 == pfn as bv32);
    assert(b1 <= mask1);
    //assert(b1 < 0x1 as bv32 << 20);
    //assert(b1 <= 0xF_FFFF as bv32);

    //assert(pfnBv < numVpns as bv32);
    //assert(0x10_0000 == 1 as bv32 << 20 as bv6);
    //assert(pfnBv < numVpns as bv21);
    var shifted := (b1 << 12);
    //assert(shifted >> 12 == b1);
    //assert(shifted >> 32 == 0);
    //assert(shifted >> 12 == pfnBv) by {
    //}
    //assert(shifted & 0xFFF == 0);
    var b := (shifted | offset as bv32);

    //assert(b >> 12 == pfnBv) by {
    //assert(offset as bv32 >> 12 == 0) by {
    //assert(0 <= offset < 0xFFF);
    //assert(0xFFF as bv32 == )
    //}
    //assert(b & 0x0FFF == offset as bv32);
    return (b as addr);
  }
  function getOffset(a: addr): addr {
    (a as bv32 & 0x0FFF as bv32) as addr
  }

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
    requires pfn < currPfn
    ensures 0 <= err <= 1
    ensures pageTableInvariant()
    ensures err == 0 ==> root[vpnPart1].Some? && root[vpnPart1].arr[vpnPart2] == pfn
    ensures (err != 0 && old(root[vpnPart1].Some?)) ==> root[vpnPart1].Some?    && root[vpnPart1].arr == old(root[vpnPart1].arr)
    modifies root
    modifies if root[vpnPart1].Some? then {root[vpnPart1].arr} else {}
  {
    assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));
    assert(forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < currPfn)));

    var entry1 := root[vpnPart1];

    if (entry1 == Nil){
      assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));
      var a := new addr[numVpnParts];
      for i := 0 to numVpnParts as int
        invariant a.Length == numVpnParts as int
        invariant 0 <= i <= a.Length
        invariant forall j: nat :: 0 <= j < i ==> a[j] == 0 as addr
        // these invariants are irrelevant to this loop but are necessary to prove later assertions
        invariant forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int))
        invariant forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < currPfn))
      {
        a[i] := 0 as addr by {
          assert(a.Length == numVpnParts as int);

        }
      }
      assert(forall i :: 0 <= i < a.Length ==> a[i] == 0 as addr);

      entry1 := Some(a);
      root[vpnPart1] := entry1;
      assert(entry1.arr.Length == numVpnParts as int);
    }


    assert entry1.Some?;

    var entry2: addr := entry1.arr[vpnPart2] by {
      assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)));
      assert(0 <= vpnPart2 < numVpnParts);
    }

    if (entry2 == 0){
      entry2 := pfn;
      entry1.arr[vpnPart2] := entry2;
      assert(entry2 < currPfn);
    }


    if (entry2 == pfn){
      // important assertions
      var getPfn := tryGetMapping(vpnPart1, vpnPart2) by {
        assert(forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int))) ;
        assert(forall j :: 0 <= j < numVpnParts ==> root[vpnPart1].arr[j] < currPfn) by {
          assert(root[vpnPart1].Some? && root[vpnPart1].arr[vpnPart2] == pfn);
          assert(old(root[vpnPart1].Some?) ==> forall j :: 0 <= j < numVpnParts && j != vpnPart2 ==> root[vpnPart1].arr[j] == old(root[vpnPart1].arr[j]));
          assert(old(root[vpnPart1].Some?) ==> forall j :: 0 <= j < numVpnParts && j != vpnPart2 ==> root[vpnPart1].arr[j] < currPfn);
          assert(!old(root[vpnPart1].Some?) ==> forall j :: 0 <= j < numVpnParts && j != vpnPart2 ==> root[vpnPart1].arr[j] == 0);
        }
        assert(forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < currPfn)));
      }
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
    ensures currPfn != 0 ==> 0 <= pfn < currPfn
  {

    var entry1 := root[vpnPart1];

    if (entry1 == Nil){
      return 0;
    }

    assert entry1.Some?;
    var entry2 := entry1.arr[vpnPart2];

    return entry2;
  }


  method allocate(vaddr: addr, size: addr) returns (err: nat)
    requires pageTableInvariant()
    ensures pageTableInvariant()
    ensures tlbKeys == old(tlbKeys)
    ensures tlbVals == old(tlbVals)
    ensures tlbValid == old(tlbValid)
    modifies this
    modifies root
    modifies set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr
    modifies tlbKeys, tlbVals, tlbValid, this
    // modifies this
  {
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
    currPfn := currPfn + 1;

    err := tryInsertMapping(part1, part2, currPfn - 1);
    if (err == 0) {
      // warm the TLB with the new mapping
      // assumes err code 0 means no error
      tlbInsert(vpn, currPfn - 1);
    }
  }

  method tlbLookup(vpn: addr) returns (pfn: addr, hit: bool)
    requires pageTableInvariant()
    requires vpn < numVpns
    ensures pageTableInvariant()
    ensures pfn < currPfn
  {
    var i := 0;
    while i < tlbSize
      invariant 0 <= i <= tlbSize
      invariant pageTableInvariant()
    {
      if (tlbValid[i] && tlbKeys[i] == vpn) {
        pfn := tlbVals[i];
        hit := true;
        return;
      }
      i := i + 1;
    }
    pfn := 0;
    hit := false;
  }

  method tlbInsert(vpn: addr, pfn: addr)
    requires pageTableInvariant()
    requires vpn < numVpns
    requires pfn < currPfn
    ensures pageTableInvariant()
    ensures tlbKeys == old(tlbKeys)
    ensures tlbVals == old(tlbVals)
    ensures tlbValid == old(tlbValid)
    modifies tlbKeys, tlbVals, tlbValid, this
  {
    var idx := tlbNext as int;
    tlbKeys[idx] := vpn;
    tlbVals[idx] := pfn;
    tlbValid[idx] := true;

    if tlbNext + 1 < tlbSize as nat {
      tlbNext := tlbNext + 1;
    } else {
      tlbNext := 0;
    }
  }

  method flushTLB()
    requires pageTableInvariant()
    ensures pageTableInvariant()
    modifies tlbValid, this
  {
    for i := 0 to tlbSize as int
      invariant 0 <= i <= tlbSize as int
      invariant forall j :: 0 <= j < i ==> !tlbValid[j]
      invariant forall j :: 0 <= j < tlbSize ==> tlbValid[j] ==> (tlbKeys[j] < numVpns && tlbVals[j] < numVpns)
      invariant pageTableInvariant()
      modifies tlbValid
    {
      tlbValid[i] := false;
    }
    tlbNext := 0;
  }

  method translate(vaddr: addr) returns (paddr: addr, ok: bool)
    requires pageTableInvariant()
    //ensures pageTableInvariant()
    modifies root
    modifies set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr
    modifies tlbKeys, tlbVals, tlbValid, this
  {
    var vpn := getVpn(vaddr);
    var pfn, hit := tlbLookup(vpn);
    
    if (hit) {
      var offset := getOffset(vaddr);
      var phys := buildAddr(pfn, offset);
      paddr := phys as addr;
      ok := true;
      return;
    } 
    

    var part1, part2 := maskVpn(vpn);
    pfn := tryGetMapping(part1, part2);

    if (pfn == 0){
      
      var err := allocate(vaddr, 1);
      if (err != 0) {
        paddr := 0;
        ok := false;
        return;
      }

    }
    // insert into TLB on a miss
    assert(tlbKeys == old(tlbKeys));
    assert(tlbVals == old(tlbVals));
    assert(tlbValid == old(tlbValid));
    tlbInsert(vpn, pfn);
    var offset := getOffset(vaddr);

    paddr := buildAddr(pfn, offset);
    ok := true;
  }
}


/*method main(){
  var pt := new PageTable();
}*/
