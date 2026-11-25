import OAI.Computability.NearSquareRoot.PrecisionGridSplitRank
import OAI.Computability.NearSquareRoot.SynchronizedBlockCardinality
import OAI.Computability.NearSquareRoot.SynchronizedPhysicalFiber

/-! # The fixed Walsh bit and the rank of its spectators

Removing the high bit of the first field in a local block leaves the low bits of
that field followed by all other fields, in their original order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open ShortFourier SynchronizedBlocks
variable {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
  [∀ i, NeZero (modulus box i)]

/-- Number of lower positions of the first block field. -/
def lowRadix (j : Fin (box.length/4)) : ℕ := 2^((box.get (axis j (firstAxis j))).1-1)

include hb in
omit [∀ i, NeZero (modulus box i)] in
theorem firstRadix_eq (j : Fin (box.length/4)) :
    blockFieldRadix box j (firstAxis j) = lowRadix (box := box) j * 2 := by
  unfold blockFieldRadix lowRadix
  have hw := (hb.axisBounds _ (List.get_mem box (axis j (firstAxis j)))).1
  rw [← Nat.pow_succ]
  congr 1
  omega

/-- The rank of all remaining bits of the block after discarding its fixed Walsh bit. -/
noncomputable def numberedSpectator (j : Fin (box.length/4)) :
    Spectator (BoxAxis box) (fun i => (box.get i).1) j ≃
        Fin (Fintype.card (BlockAddress (BoxAxis box) j)/2) :=
  (Equiv.prodComm ..).trans (((blockSpectators hb j (firstAxis j)).prodCongr (Equiv.refl _)).trans
    (finProdFinEquiv.trans (finCongr (by
      have h := Fintype.card_congr (boxBits hb j)
      simp only [Fintype.card_prod,Fintype.card_fin] at h
      change _ * _ = Fintype.card (BlockAddress (BoxAxis box) j)/2
      rw [h,Nat.mul_div_cancel_left _ (by decide)]
      exact Nat.mul_comm ..))))

/-- The earlier fixed-bit layout, including its executable spectator numbering. -/
noncomputable def numberedBits (j : Fin (box.length/4)) :
    BlockAddress (BoxAxis box) j ≃ Fin 2 × Fin (Fintype.card (BlockAddress (BoxAxis box) j)/2) :=
  (boxBits hb j).trans ((Equiv.refl (Fin 2)).prodCongr (numberedSpectator hb j))

theorem numberedBits_fields (j : Fin (box.length/4)) (x : BlockAddress (BoxAxis box) j) :
    let p := lowRadix (box := box) j
    let q := (blockAddressRank hb j x).val
    (numberedBits hb j x).1.val = FieldSplit.col p 2 q ∧
    (numberedBits hb j x).2.val = FieldSplit.row p 2 q := by
  let f := firstAxis j
  let radix := blockFieldRadix box j
  let p := lowRadix (box := box) j
  let q := (blockAddressRank hb j x).val
  let dig := (field hb (axis j f) (x f)).val
  let spectators := ((boxBits hb j x).2.2)
  let row := (blockSpectators hb j f spectators).val
  have h := blockAxisLayout_fields hb j f x
  have hfirst : CRT.«prefix» radix f = 1 := by
    unfold CRT.«prefix»
    have he : Finset.Iio f = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := Finset.mem_Iio.mp hi
      exact (Nat.not_lt_zero i.val) this
    rw [he,Finset.prod_empty]
  have hr : radix f = p*2 := firstRadix_eq hb j
  change row = FieldSplit.row (CRT.«prefix» radix f) (radix f) q ∧
    dig = FieldSplit.col (CRT.«prefix» radix f) (radix f) q at h
  rw [hfirst,hr] at h
  simp only [FieldSplit.row,FieldSplit.col,Nat.mod_one,Nat.one_mul,Nat.zero_add,Nat.div_one] at h
  change dig/p = q/p%2 ∧ dig%p+p*row = q%p+p*(q/(p*2))
  rw [h.1,h.2,Nat.mod_mul_right_mod,Nat.mod_mul_right_div_self]
  exact ⟨rfl,rfl⟩

/-- Insertion of the designated bit from its numeric spectator rank. -/
theorem numberedBits_invert (j : Fin (box.length/4))
    (b : Fin 2) (s : Fin (Fintype.card (BlockAddress (BoxAxis box) j)/2)) :
    let p := lowRadix (box := box) j
    (blockAddressRank hb j ((numberedBits hb j).symm (b,s))).val =
      s.val%p + p*(b.val+2*(s.val/p)) := by
  let p := lowRadix (box := box) j
  let q := (blockAddressRank hb j ((numberedBits hb j).symm (b,s))).val
  have h := numberedBits_fields hb j ((numberedBits hb j).symm (b,s))
  simp only [Equiv.apply_symm_apply,FieldSplit.col,FieldSplit.row] at h
  change b.val = q/p%2 ∧ s.val = q%p+p*(q/(p*2)) at h
  have hp : 0 < p := Nat.two_pow_pos _
  have hl := Nat.mod_lt q hp
  have hdiv : s.val/p = q/(p*2) := by
    rw [h.2,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt hl,Nat.zero_add]
  have hmod : s.val%p = q%p := by rw [h.2]; simp
  change q = _
  rw [hdiv,hmod,h.1,← Nat.div_div_eq_div_mul]
  rw [Nat.mod_add_div, Nat.mod_add_div]

/-- Replacing spectator coordinates with their explicit ranks preserves every Walsh entry. -/
theorem numberedBits_block (active : Finset (Fin (box.length/4))) (j : Fin (box.length/4)) :
    SynchronizedSelected.block active (numberedBits hb) j = SynchronizedSelected.block active (boxBits hb) j := by
  classical
  by_cases hj : j ∈ active
  · ext x y
    simp [SynchronizedSelected.block,hj,numberedBits]
  · simp [SynchronizedSelected.block,hj]

/-- The concrete numeric layout used by the opcode compiler has the flattened tape Walsh
matrix, for any set of simultaneously active blocks. -/
theorem numberedWalsh_physical (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4))) :
    (SynchronizedPadding.tensorMatrix (SynchronizedSelected.block active (numberedBits hb))).submatrix
      (regroup hd _) (regroup hd _) =
      (flatWalsh (active.image (selectedPosition hb))).submatrix (recordIndex hb) (recordIndex hb) := by
  rw [show SynchronizedSelected.block active (numberedBits hb) = _ from funext (numberedBits_block hb active)]
  exact tensorWalsh_physical hb hd active

variable (j : Fin (box.length/4))

/-- Exact binary width of one original contiguous block of addresses. -/
def physicalWidth : ℕ := ∑ i : Fin (count j), (box.get (axis j i)).1

noncomputable def blockBitRank : BlockAddress (BoxAxis box) j ≃ Fin (2^physicalWidth (box := box) j) :=
  (blockAddressRank hb j).trans (finCongr (by rw [blockRadix,Finset.prod_pow_eq_pow_sum];rfl))

end BoxFin

end NearSquareRoot
end Computability
end OAI
