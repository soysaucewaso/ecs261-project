newtype int32 = x: int | 0 <= x < 0x1_0000_0000
newtype addr = int32
type addrArray = array<addr>

datatype secondLevelPtr = Nil | Some(arr: addrArray)

class PageTable{

  var root: array<secondLevelPtr>
  // TLB cache: small hardware-style cache for VPN -> PFN mappings
  const tlbSize: nat := 16
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
    tlbKeys != tlbVals &&
    0 <= tlbNext < tlbSize
  }

  predicate pageTableUnique()
    reads this
    reads root
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
    root.Length == numVpnParts as int &&
    // every nonzero page frame in the pageTable is unique
    //    equivalent to the following pseudocode assertion
    //      forall (vpn1, vpn2) in page table,
    //        pfn1 := pageTable[vpn1]
    //        pfn2 := pageTable[vpn2]
    //        assert((vpn1 != vpn2 && pfn1 != 0) ==> pfn1 != pfn2);
    (forall i, j : nat :: (0 <= i < root.Length && 0 <= j < root.Length && root[i].Some? && root[j].Some? && i != j) ==> root[i] != root[j]) &&
    forall i : nat, j, k, l ::
      (0 <= i < root.Length && root[i].Some? &&
       0 <= j < root[i].arr.Length && root[i].arr[j] != 0 &&
       0 <= k < root.Length && root[k].Some? &&
       0 <= l < root[k].arr.Length &&
       (i != k || j != l)) ==> root[i].arr[j] != root[k].arr[l]
  }

  predicate tableArraySize()
    reads this
    reads root
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
    (forall i : nat :: ((0 <= i < root.Length) ==> (root[i] == Nil || root[i].arr.Length == numVpnParts as int)))
  }

  predicate pageInvariant()
    reads this
    reads root
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
    0 < currPfn < numVpns &&
    root.Length == numVpnParts as int &&
    tableArraySize() &&
    // all pfns in the page table have a lower index than the current free pfn
    (forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j : nat :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < currPfn))) &&
    pageTableUnique()

  }

  predicate tlbUnique()
    reads this
    reads tlbValid, tlbKeys, tlbVals
  {
    tlbInvariant() &&
    //(forall i, j: nat :: 0 <= i < tlbSize as int && 0 <= j < tlbSize as int && i != j && tlbValid[i] && tlbValid[j] ==> (tlbKeys[i] != tlbKeys[j])) &&
    (forall i, j: nat :: 0 <= i < tlbSize as int && 0 <= j < tlbSize as int && i != j && tlbValid[i] && tlbValid[j] ==> (tlbVals[i] != tlbVals[j]))
  }
  predicate valExists(val: addr)
  requires false
    reads this
    reads root
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
     (exists j, k: nat :: 0 <= j < numVpnParts && 0 <= k < numVpnParts as int && root[j].Some? && root[j].arr[k] == val)
  }


  predicate tlbGrounded()
  requires false
    reads this
    reads tlbValid, tlbKeys, tlbVals
    reads root
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
    tlbInvariant() &&
    pageInvariant() &&
    (forall i: nat :: 0 <= i < tlbSize as int && tlbValid[i] ==> valExists(tlbVals[i]))
  }


  predicate pageTableInvariant()
    reads this
    reads root
    reads tlbValid, tlbKeys, tlbVals
    reads if (root.Length == numVpnParts as int) then set i | 0 <= i < numVpnParts && root[i].Some? :: root[i].arr else {}
  {
    tlbInvariant() && pageInvariant() &&
    // when valid, TLB entries carry valid vpn/pfn ranges
    (forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && 0 < tlbVals[i] < currPfn))) &&
    tlbUnique() 
    //tlbGrounded()
  }

  constructor()
  {


  }
  method init()
    ensures pageTableInvariant()
    ensures fresh(root)
    ensures forall j: nat :: 0 <= j < tlbSize ==> tlbValid[j] == false
    modifies this
  {
    root := new secondLevelPtr[numVpnParts];

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
    var keys := new addr[tlbSize];
    var vals := new addr[tlbSize];
    var valid := new bool[tlbSize];
    tlbKeys := keys;
    tlbVals := vals;
    tlbValid := valid;
    tlbNext := 0;
    currPfn := 1;
    assert(currPfn == 1 as addr);
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
    var mask1: bv32 := 0x03FF;
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
    var mask := 0xFFFF_F000;
    var bv := (vaddr as bv32 & mask as bv32);
    bv := bv >> 12;
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
    requires 0 < pfn < currPfn
    requires forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < pfn))
    ensures 0 <= err <= 1
    //ensures pageTableInvariant()
    ensures tlbInvariant() && pageInvariant() &&
    // when valid, TLB entries carry valid vpn/pfn ranges
    (forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && 0 < tlbVals[i] < currPfn))) &&
    tlbUnique()

    ensures err == 0 ==> root[vpnPart1].Some? && root[vpnPart1].arr.Length == numVpnParts as nat && root[vpnPart1].arr[vpnPart2] == pfn
    // everything except the vpn is unmodified
    ensures err == 0 ==> forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != vpnPart1 as nat || j != vpnPart2 as nat) ==> root[i].arr[j] == old(root[i].arr[j])
    ensures (err != 0 && old(root[vpnPart1].Some?)) ==> root[vpnPart1].Some?    && root[vpnPart1].arr == old(root[vpnPart1].arr)
    modifies root
    modifies if root[vpnPart1].Some? then {root[vpnPart1].arr} else {}
  {
    assert(tableArraySize());
    assert(forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < pfn)));

    var entry1 := root[vpnPart1];
    assert(pageTableUnique());

    if (entry1 == Nil){
      assert(tableArraySize());
      var a := new addr[numVpnParts];
      for i := 0 to numVpnParts as int
        invariant a.Length == numVpnParts as int
        invariant 0 <= i <= a.Length
        invariant forall j: nat :: 0 <= j < i ==> a[j] == 0 as addr
        // these invariants are irrelevant to this loop but are necessary to prove later assertions
        invariant tableArraySize()
        invariant forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < pfn))
        invariant forall i : nat :: (0 <= i < root.Length) ==> root[i] == old(root[i])
        invariant forall i : nat :: (0 <= i < root.Length && root[i].Some?) ==> root[i].arr != a
        invariant forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && 0 <= j < root[i].arr.Length) ==> (root[i].arr.Length == numVpnParts as nat) ==> root[i].arr[j] == old(root[i].arr[j])
        invariant pageTableUnique()
        invariant tlbUnique()
        //invariant tlbGrounded()
      {
        a[i] := 0 as addr by {
          assert(a.Length == numVpnParts as int);
        }
      }

      entry1 := Some(a);
      root[vpnPart1] := entry1;
      assert(forall j :: (0 <= j < root[vpnPart1].arr.Length) ==> root[vpnPart1].arr[j] < pfn) by {
        assert(forall i :: 0 <= i < a.Length ==> a[i] == 0 as addr);
        assert(entry1.arr.Length == numVpnParts as int);
        assert(forall i :: 0 <= i < entry1.arr.Length ==> entry1.arr[i] == 0 as addr);
      }
      
      
    }


    assert entry1.Some?;
    assert(pageTableUnique()) by {
      assert(forall i : nat :: (0 <= i < root.Length && root[i].Some?) ==> (i != vpnPart1 as nat) ==> root[i] != entry1);
    }
        //assert(forall i : nat :: (0 <= i < root.Length && i != vpnPart1 as nat) ==> root[i] == old(root[i]));
      //}
      //assert(!old(root[vpnPart1].Some?));

    var entry2: addr := entry1.arr[vpnPart2] by {
      assert(tableArraySize());
      assert(0 <= vpnPart2 < numVpnParts);
    }

    if (entry2 == 0){
      //assert(forall i : nat :: ((0 <= i < root.Length && root[i].Some?) ==> (forall j :: (0 <= j < root[i].arr.Length) ==> root[i].arr[j] < pfn)));
      entry2 := pfn;
      assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && 0 <= j < root[i].arr.Length) ==> (i == vpnPart1 as nat && j == vpnPart2 as nat) || root[i].arr[j] != pfn);
      root[vpnPart1].arr[vpnPart2] := entry2;
      assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != vpnPart1 as nat || j != vpnPart2 as nat) ==> root[i].arr[j] == old(root[i].arr[j])) by {
        assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != vpnPart1 as nat) ==> root[i].arr[j] == old(root[i].arr[j])) by {
          assert(root[vpnPart1].arr[vpnPart2] == pfn);
          assert(forall i : nat :: (0 <= i < root.Length && root[i].Some?) ==> (i != vpnPart1 as nat) ==> root[i] == old(root[i]));
          assert(forall i, j : nat :: (0 <= i < root.Length && 0 <= j < root.Length && root[i].Some? && root[j].Some? && i != j) ==> root[i] != root[j]);

        }
        assert(forall j : nat :: (0 <= j < root[vpnPart1].arr.Length && old(root[vpnPart1].Some?)) ==> (j != vpnPart2 as nat) ==> root[vpnPart1].arr[j] == old(root[vpnPart1].arr[j]));
      }
      assert(pageTableUnique()) by {
        assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && 0 <= j < root[i].arr.Length) ==> (i == vpnPart1 as nat && j == vpnPart2 as nat) || root[i].arr[j] != root[vpnPart1].arr[vpnPart2]) by {
          assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != vpnPart1 as nat || j != vpnPart2 as nat) ==> root[i].arr[j] == old(root[i].arr[j]));
        }
      }
      /*
      assert(tlbGrounded()) by {
          assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != vpnPart1 as nat || j != vpnPart2 as nat) ==> root[i].arr[j] == old(root[i].arr[j]));
          assert(forall i : nat :: (0 <= i < tlbSize as nat && tlbValid[i]) ==> tlbVals[i] > 0);
          assert(old(root[vpnPart1].arr[vpnPart2]) == 0);
      }
      */
    }


    if (entry2 == pfn){
      // important assertions
      var getPfn := tryGetMapping(vpnPart1, vpnPart2) by {
        assert(tableArraySize()) ;
        assert(forall j :: 0 <= j < numVpnParts ==> root[vpnPart1].arr[j] < currPfn) by {
          assert(root[vpnPart1].Some? && root[vpnPart1].arr[vpnPart2] == pfn);
          assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != vpnPart1 as nat || j != vpnPart2 as nat) ==> root[i].arr[j] == old(root[i].arr[j]));
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
    assert(forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && 0 < tlbVals[i] < currPfn)));
    var pfn := currPfn;
    currPfn := currPfn + 1;

    err := tryInsertMapping(part1, part2, pfn);
    if (err == 0) {
      // warm the TLB with the new mapping
      // assumes err code 0 means no error
      var tlbI := tlbNext;
      assert(forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && 0 < tlbVals[i] < pfn)));
      tlbInsert(vpn, pfn) by {
        assert(forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && 0 < tlbVals[i] < pfn)));
        assert(forall i, j : nat :: (0 <= i < root.Length && root[i].Some? && old(root[i].Some?) && 0 <= j < root[i].arr.Length) ==> (i != part1 as nat || j != part2 as nat) ==> root[i].arr[j] == old(root[i].arr[j]));

      }
      assert(root[part1].Some? && root[part1].arr.Length == numVpnParts as nat && root[part1].arr[part2] == pfn) by {
        assert(err == 0);
        assert(err == 0 ==> root[part1].Some? && root[part1].arr.Length == numVpnParts as nat && root[part1].arr[part2] == pfn);
      }
      assert(tlbKeys[tlbI] == vpn);
      assert(tlbVals[tlbI] == pfn);
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
    requires 0 < pfn < currPfn
    requires forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] ==> (tlbKeys[i] < numVpns && 0 < tlbVals[i] < pfn))
    requires exists j, k: nat :: 0 <= j < numVpnParts && 0 <= k < numVpnParts as int && root[j].Some? && root[j].arr[k] == pfn
    ensures pageTableInvariant()
    ensures tlbKeys == old(tlbKeys)
    ensures tlbVals == old(tlbVals)
    ensures tlbValid == old(tlbValid)
    ensures tlbValid[old(tlbNext)] == true
    ensures tlbKeys[old(tlbNext)] == vpn
    ensures tlbVals[old(tlbNext)] == pfn
    ensures root == old(root)
    modifies tlbKeys, tlbVals, tlbValid, this
  {
    var idx := tlbNext as int;
    tlbKeys[idx] := vpn;
    assert(tlbKeys[idx] == vpn);
    tlbVals[idx] := pfn;
    tlbValid[idx] := true;

    assert(old(tlbNext) == idx);
    assert(tlbValid[old(tlbNext)] == true);
    assert(tlbKeys[old(tlbNext)] == vpn);
    assert(tlbVals[old(tlbNext)] == pfn);
    assert(tlbUnique()) by {
      assert(forall i: nat :: 0 <= i < tlbSize as int ==> (tlbValid[i] && i != idx ==> (0 < tlbVals[i] < pfn)));
    }
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
    ensures pageTableInvariant()
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
    pfn := tryGetMapping(part1, part2);
    var offset := getOffset(vaddr);

    paddr := buildAddr(pfn, offset);
    ok := true;
  }
}


/*method main(){
  var pt := new PageTable();
}*/
