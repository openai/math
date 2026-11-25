import OAI.Computability.NearSquareRoot.SynchronizedPackedPermutation
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress

/-! # Absolute address-bit location of every physical Beneš port -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open IntegerMultiplication SynchronizedBlocks ShortFourier

variable {box : List (ℕ × ℕ)} {k L : ℕ} (hb : BoxShape.Valid k L box)
  [∀ i, NeZero (modulus box i)] (hd : 4 ≤ box.length)

/-- Number of address bits in all preceding physical blocks. -/
def blockOffset (j : Fin (box.length/4)) : ℕ :=
  ∑ i : Fin j.val, physicalWidth (box := box) (Fin.castLE j.isLt.le i)

omit [∀ i, NeZero (modulus box i)] in
private theorem radix_is_pow (j : Fin (box.length/4)) :
    blockRadix box j = 2^physicalWidth (box := box) j := by
  rw [blockRadix, Finset.prod_pow_eq_pow_sum]
  rfl

/-- The rank of one block consists exactly of its bit interval in the flat tape address. -/
theorem packedRank_extract (t : Fin (2^k)) (j : Fin (box.length/4)) :
    ((blockAddressRank hb j) ((regroup hd _ ((recordIndex hb).symm t)) j)).val =
      t.val / 2^(blockOffset (box := box) j) % 2^physicalWidth (box := box) j := by
  let x := (recordIndex hb).symm t
  let y := fun j => blockAddressRank hb j (regroup hd _ x j)
  have h := recordIndex_blockRank hb hd x
  change (recordIndex hb x).val = CRT.rank (blockRadix box) (fun b => (y b).val) at h
  rw [CRT.rank_eq_finPiFinEquiv] at h
  rw [show recordIndex hb x = t from (recordIndex hb).apply_symm_apply t] at h
  have he := congrArg Fin.val (congrFun (finPiFinEquiv.symm_apply_apply y) j)
  change (finPiFinEquiv y).val / (∏ i : Fin j.val, blockRadix box (Fin.castLE j.isLt.le i)) %
    blockRadix box j = (y j).val at he
  simp only [←h,radix_is_pow,Finset.prod_pow_eq_pow_sum] at he
  exact he.symm

/-- In the most-significant-first labeling of the Beneš compiler, port `i` belongs
to bit `offset + (width - 1 - i)` of the original physical address word. -/
theorem packedRecord_port (t : Fin (2^k)) (j : Fin (box.length/4)) (i : Fin (physicalWidth (box := box) j)) :
    ((packedRecord hb hd t).2 j) i =
      t.val.testBit (blockOffset (box := box) j + (physicalWidth (box := box) j - 1 - i.val)) := by
  let d := physicalWidth (box := box) j
  let n := ((blockAddressRank hb j) ((regroup hd _ ((recordIndex hb).symm t)) j)).val
  let b := d-1-i.val
  have hdigit : n < 2^d := by
    have h := ((blockAddressRank hb j) ((regroup hd _ ((recordIndex hb).symm t)) j)).isLt
    exact h.trans_eq (radix_is_pow j)
  have hi : i.val < d := i.isLt
  have hbnd : b < d := by dsimp [b];omega
  have he := congrArg (fun s : List Bool => s[i.val]?) (packedRecord_field hb hd t j)
  change (List.ofFn ((packedRecord hb hd t).2 j))[i.val]? = (Bits.phrase d n).reverse[i.val]? at he
  have llen : i.val < (List.ofFn ((packedRecord hb hd t).2 j)).length := by simp
  rw [List.getElem?_eq_getElem llen,List.getElem_ofFn] at he
  have rlen : i.val < (Bits.phrase d n).reverse.length := by simpa [Bits.phrase_length] using hi
  rw [List.getElem?_eq_getElem rlen,List.getElem_reverse] at he
  have hbit := value_bit (Bits.phrase d n) b (by simpa [Bits.phrase_length] using hbnd)
  rw [Bits.value_phrase hdigit] at hbit
  have hh : ((packedRecord hb hd t).2 j) i = n.testBit b := by
    rw [hbit]
    exact Option.some.inj (by simpa [b,Bits.phrase_length] using he)
  rw [hh]
  change n.testBit b = _
  rw [show n = _ from packedRank_extract hb hd t j]
  rw [Nat.testBit_mod_two_pow,decide_eq_true hbnd,Bool.true_and,Nat.testBit_div_two_pow,Nat.add_comm]

end BoxFin

end NearSquareRoot
end Computability
end OAI
