import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_


class int32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class addr:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class secondLevelPtr:
    @classmethod
    def default(cls, ):
        return lambda: secondLevelPtr_Nil()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Nil(self) -> bool:
        return isinstance(self, secondLevelPtr_Nil)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, secondLevelPtr_Some)

class secondLevelPtr_Nil(secondLevelPtr, NamedTuple('Nil', [])):
    def __dafnystr__(self) -> str:
        return f'secondLevelPtr.Nil'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, secondLevelPtr_Nil)
    def __hash__(self) -> int:
        return super().__hash__()

class secondLevelPtr_Some(secondLevelPtr, NamedTuple('Some', [('arr', Any)])):
    def __dafnystr__(self) -> str:
        return f'secondLevelPtr.Some({_dafny.string_of(self.arr)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, secondLevelPtr_Some) and self.arr == __o.arr
    def __hash__(self) -> int:
        return super().__hash__()


class PageTable:
    def  __init__(self):
        self.root: _dafny.Array = _dafny.Array(None, 0)
        self.tlbKeys: _dafny.Array = _dafny.Array(None, 0)
        self.tlbVals: _dafny.Array = _dafny.Array(None, 0)
        self.tlbValid: _dafny.Array = _dafny.Array(None, 0)
        self.tlbNext: int = int(0)
        self.currPfn: int = int(0)
        pass

    def __dafnystr__(self) -> str:
        return "_module.PageTable"
    def tlbInvariant(self):
        return (((((self.tlbKeys).length(0)) == ((self).tlbSize)) and (((self.tlbVals).length(0)) == ((self).tlbSize))) and (((self.tlbValid).length(0)) == ((self).tlbSize))) and (((0) <= (self.tlbNext)) and ((self.tlbNext) < ((self).tlbSize)))

    def pageTableUnique(self):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                def lambda2_(forall_var_2_):
                    def lambda3_(forall_var_3_):
                        d_3_l_: int = forall_var_3_
                        return not ((((((((((0) <= (d_0_i_)) and ((d_0_i_) < ((self.root).length(0)))) and (((self.root)[d_0_i_]).is_Some)) and (((0) <= (d_1_j_)) and ((d_1_j_) < ((((self.root)[d_0_i_]).arr).length(0))))) and (((((self.root)[d_0_i_]).arr)[d_1_j_]) != (0))) and (((0) <= (d_2_k_)) and ((d_2_k_) < ((self.root).length(0))))) and (((self.root)[d_2_k_]).is_Some)) and (((0) <= (d_3_l_)) and ((d_3_l_) < ((((self.root)[d_2_k_]).arr).length(0))))) and (((d_0_i_) != (d_2_k_)) or ((d_1_j_) != (d_3_l_)))) or (((((self.root)[d_0_i_]).arr)[d_1_j_]) != ((((self.root)[d_2_k_]).arr)[d_3_l_]))

                    d_2_k_: int = forall_var_2_
                    return _dafny.quantifier(_dafny.IntegerRange(0, (((self.root)[d_2_k_]).arr).length(0)), True, lambda3_)

                d_1_j_: int = forall_var_1_
                return _dafny.quantifier(_dafny.IntegerRange(0, (self.root).length(0)), True, lambda2_)

            d_0_i_: int = forall_var_0_
            if System_.nat._Is(d_0_i_):
                return _dafny.quantifier(_dafny.IntegerRange(0, (((self.root)[d_0_i_]).arr).length(0)), True, lambda1_)
            elif True:
                return True

        return (((self.root).length(0)) == ((self).numVpnParts)) and (_dafny.quantifier(_dafny.IntegerRange(0, (self.root).length(0)), True, lambda0_))

    def pageInvariant(self):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            if System_.nat._Is(d_0_i_):
                return not (((0) <= (d_0_i_)) and ((d_0_i_) < ((self.root).length(0)))) or ((((self.root)[d_0_i_]) == (secondLevelPtr_Nil())) or (((((self.root)[d_0_i_]).arr).length(0)) == ((self).numVpnParts)))
            elif True:
                return True

        def lambda1_(forall_var_1_):
            def lambda2_(forall_var_2_):
                d_2_j_: int = forall_var_2_
                if System_.nat._Is(d_2_j_):
                    return not (((0) <= (d_2_j_)) and ((d_2_j_) < ((((self.root)[d_1_i_]).arr).length(0)))) or (((((self.root)[d_1_i_]).arr)[d_2_j_]) < (self.currPfn))
                elif True:
                    return True

            d_1_i_: int = forall_var_1_
            if System_.nat._Is(d_1_i_):
                return not ((((0) <= (d_1_i_)) and ((d_1_i_) < ((self.root).length(0)))) and (((self.root)[d_1_i_]).is_Some)) or (_dafny.quantifier(_dafny.IntegerRange(0, (((self.root)[d_1_i_]).arr).length(0)), True, lambda2_))
            elif True:
                return True

        return ((((((0) < (self.currPfn)) and ((self.currPfn) < ((self).numVpns))) and (((self.root).length(0)) == ((self).numVpnParts))) and (_dafny.quantifier(_dafny.IntegerRange(0, (self.root).length(0)), True, lambda0_))) and (_dafny.quantifier(_dafny.IntegerRange(0, (self.root).length(0)), True, lambda1_))) and ((self).pageTableUnique())

    def pageTableInvariant(self):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            if System_.nat._Is(d_0_i_):
                return not (((0) <= (d_0_i_)) and ((d_0_i_) < ((self).tlbSize))) or (not ((self.tlbValid)[d_0_i_]) or ((((self.tlbKeys)[d_0_i_]) < ((self).numVpns)) and (((self.tlbVals)[d_0_i_]) < (self.currPfn))))
            elif True:
                return True

        return (((self).tlbInvariant()) and ((self).pageInvariant())) and (_dafny.quantifier(_dafny.IntegerRange(0, (self).tlbSize), True, lambda0_))

    def ctor__(self):
        pass
        pass

    def init(self):
        nw0_ = _dafny.Array(secondLevelPtr.default()(), (self).numVpnParts)
        (self).root = nw0_
        hi0_ = (self).numVpnParts
        for d_0_i_ in range(0, hi0_):
            arr0_ = self.root
            arr0_[(d_0_i_)] = secondLevelPtr_Nil()
        d_1_keys_: _dafny.Array
        nw1_ = _dafny.Array(int(0), (self).tlbSize)
        d_1_keys_ = nw1_
        d_2_vals_: _dafny.Array
        nw2_ = _dafny.Array(int(0), (self).tlbSize)
        d_2_vals_ = nw2_
        d_3_valid_: _dafny.Array
        nw3_ = _dafny.Array(False, (self).tlbSize)
        d_3_valid_ = nw3_
        (self).tlbKeys = d_1_keys_
        (self).tlbVals = d_2_vals_
        (self).tlbValid = d_3_valid_
        (self).tlbNext = 0
        (self).currPfn = 1
        hi1_ = (self).tlbSize
        for d_4_i_ in range(0, hi1_):
            arr1_ = self.tlbValid
            arr1_[(d_4_i_)] = False

    def buildAddr(self, pfn, offset):
        a: int = int(0)
        d_0_mask1_: int
        d_0_mask1_ = 1048575
        d_1_b1_: int
        d_1_b1_ = (pfn) & (d_0_mask1_)
        d_2_shifted_: int
        d_2_shifted_ = ((d_1_b1_) << (12)) & ((1 << 32) - 1)
        d_3_b_: int
        d_3_b_ = (d_2_shifted_) | (offset)
        a = d_3_b_
        return a
        return a

    def getOffset(self, a):
        return (a) & (4095)

    def getVpn(self, vaddr):
        vpn: int = int(0)
        d_0_mask_: int
        d_0_mask_ = 4290772992
        d_1_bv_: int
        d_1_bv_ = (vaddr) & (d_0_mask_)
        d_1_bv_ = (d_1_bv_) >> (22)
        vpn = d_1_bv_
        return vpn

    def maskVpn(self, vpn):
        part1: int = int(0)
        part2: int = int(0)
        d_0_mask1_: int
        d_0_mask1_ = 1023
        d_1_b1_: int
        d_1_b1_ = (vpn) & (d_0_mask1_)
        d_2_mask2_: int
        d_2_mask2_ = 1047552
        d_3_b2_: int
        d_3_b2_ = (vpn) & (d_2_mask2_)
        d_3_b2_ = (d_3_b2_) >> (10)
        part1 = d_1_b1_
        part2 = d_3_b2_
        return part1, part2

    def tryInsertMapping(self, vpnPart1, vpnPart2, pfn):
        err: int = int(0)
        d_0_entry1_: secondLevelPtr
        d_0_entry1_ = (self.root)[vpnPart1]
        if (d_0_entry1_) == (secondLevelPtr_Nil()):
            d_1_a_: _dafny.Array
            nw0_ = _dafny.Array(int(0), (self).numVpnParts)
            d_1_a_ = nw0_
            hi0_ = (self).numVpnParts
            for d_2_i_ in range(0, hi0_):
                (d_1_a_)[(d_2_i_)] = 0
            d_0_entry1_ = secondLevelPtr_Some(d_1_a_)
            arr0_ = self.root
            arr0_[(vpnPart1)] = d_0_entry1_
        d_3_entry2_: int
        d_3_entry2_ = ((d_0_entry1_).arr)[vpnPart2]
        if (d_3_entry2_) == (0):
            d_3_entry2_ = pfn
            arr1_ = (d_0_entry1_).arr
            arr1_[(vpnPart2)] = d_3_entry2_
        if (d_3_entry2_) == (pfn):
            d_4_getPfn_: int
            out0_: int
            out0_ = (self).tryGetMapping(vpnPart1, vpnPart2)
            d_4_getPfn_ = out0_
            err = 0
            return err
        elif True:
            err = 1
            return err
        return err

    def tryGetMapping(self, vpnPart1, vpnPart2):
        pfn: int = int(0)
        d_0_entry1_: secondLevelPtr
        d_0_entry1_ = (self.root)[vpnPart1]
        if (d_0_entry1_) == (secondLevelPtr_Nil()):
            pfn = 0
            return pfn
        d_1_entry2_: int
        d_1_entry2_ = ((d_0_entry1_).arr)[vpnPart2]
        pfn = d_1_entry2_
        return pfn
        return pfn

    def allocate(self, vaddr, size):
        err: int = int(0)
        d_0_pagesNeeded_: int
        d_0_pagesNeeded_ = 1
        d_1_freePages_: int
        d_1_freePages_ = (1048575) - (self.currPfn)
        if ((self.currPfn) == (0)) or ((d_1_freePages_) < (d_0_pagesNeeded_)):
            err = 1
            return err
        d_2_vpn_: int
        out0_: int
        out0_ = (self).getVpn(vaddr)
        d_2_vpn_ = out0_
        d_3_part1_: int
        d_4_part2_: int
        out1_: int
        out2_: int
        out1_, out2_ = (self).maskVpn(d_2_vpn_)
        d_3_part1_ = out1_
        d_4_part2_ = out2_
        (self).currPfn = (self.currPfn) + (1)
        out3_: int
        out3_ = (self).tryInsertMapping(d_3_part1_, d_4_part2_, (self.currPfn) - (1))
        err = out3_
        if (err) == (0):
            (self).tlbInsert(d_2_vpn_, (self.currPfn) - (1))
        return err

    def tlbLookup(self, vpn):
        pfn: int = int(0)
        hit: bool = False
        d_0_i_: int
        d_0_i_ = 0
        while (d_0_i_) < ((self).tlbSize):
            if ((self.tlbValid)[d_0_i_]) and (((self.tlbKeys)[d_0_i_]) == (vpn)):
                pfn = (self.tlbVals)[d_0_i_]
                hit = True
                return pfn, hit
            d_0_i_ = (d_0_i_) + (1)
        pfn = 0
        hit = False
        return pfn, hit

    def tlbInsert(self, vpn, pfn):
        d_0_idx_: int
        d_0_idx_ = self.tlbNext
        arr0_ = self.tlbKeys
        arr0_[(d_0_idx_)] = vpn
        arr1_ = self.tlbVals
        arr1_[(d_0_idx_)] = pfn
        arr2_ = self.tlbValid
        arr2_[(d_0_idx_)] = True
        if ((self.tlbNext) + (1)) < ((self).tlbSize):
            (self).tlbNext = (self.tlbNext) + (1)
        elif True:
            (self).tlbNext = 0

    def flushTLB(self):
        hi0_ = (self).tlbSize
        for d_0_i_ in range(0, hi0_):
            arr0_ = self.tlbValid
            arr0_[(d_0_i_)] = False
        (self).tlbNext = 0

    def translate(self, vaddr):
        paddr: int = int(0)
        ok: bool = False
        d_0_vpn_: int
        out0_: int
        out0_ = (self).getVpn(vaddr)
        d_0_vpn_ = out0_
        d_1_pfn_: int
        d_2_hit_: bool
        out1_: int
        out2_: bool
        out1_, out2_ = (self).tlbLookup(d_0_vpn_)
        d_1_pfn_ = out1_
        d_2_hit_ = out2_
        if d_2_hit_:
            d_3_offset_: int
            d_3_offset_ = (self).getOffset(vaddr)
            d_4_phys_: int
            out3_: int
            out3_ = (self).buildAddr(d_1_pfn_, d_3_offset_)
            d_4_phys_ = out3_
            paddr = d_4_phys_
            ok = True
            return paddr, ok
        d_5_part1_: int
        d_6_part2_: int
        out4_: int
        out5_: int
        out4_, out5_ = (self).maskVpn(d_0_vpn_)
        d_5_part1_ = out4_
        d_6_part2_ = out5_
        out6_: int
        out6_ = (self).tryGetMapping(d_5_part1_, d_6_part2_)
        d_1_pfn_ = out6_
        if (d_1_pfn_) == (0):
            d_7_err_: int
            out7_: int
            out7_ = (self).allocate(vaddr, 1)
            d_7_err_ = out7_
            if (d_7_err_) != (0):
                paddr = 0
                ok = False
                return paddr, ok
        d_8_offset_: int
        d_8_offset_ = (self).getOffset(vaddr)
        out8_: int
        out8_ = (self).buildAddr(d_1_pfn_, d_8_offset_)
        paddr = out8_
        ok = True
        return paddr, ok

    @property
    def pageSize(self):
        return 4095
    @property
    def numVpns(self):
        return 1048576
    @property
    def numOffsets(self):
        return 4096
    @property
    def numVpnParts(self):
        return 1024
    @property
    def tlbSize(self):
        return 16
    @property
    def levelSizes(self):
        return _dafny.SeqWithoutIsStrInference([10, 10])
    @property
    def offset(self):
        return 12
