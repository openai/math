import OAI.Hierarchy.TaggedLocalBuckets
import OAI.Hierarchy.TaggedPassWideRead
import OAI.Hierarchy.TaggedPassInvariants
import OAI.Hierarchy.TaggedPackedBuckets

namespace OAI
/-! # The deterministic physical radix pass stably sorts one digit

All three oracle sockets remain exposed. Row projection proves that every
real digit bucket is carried in its original order, including repeated equal
words, while the wide bank puts these buckets into increasing digit order.
-/

namespace Hierarchy.Tagged.Radix.PassShape
open ThreeFlat Routing SortNetwork RadixStage SortedBlock WideOrder
open scoped Classical
noncomputable section

variable (s : PassShape) {w : ℕ} (dummy : Bits w) (real isDummy : Fin w) (digit : Fin s.digitBits → Fin w)

def realList (real : Fin w) {n : ℕ} (x : RowBits n w → Bool) : List (Bits w) :=
  (List.ofFn (fun i : Fin n => fun j : Fin w => x (i,j))).filter (fun z => z real)

/-- The static final unpacker preserves any rowwise invariant shared by all
input records and the padding word. -/
theorem keeps_words (room : s.packBits+2 ≤ s.digitBits) (P : Bits w → Prop) (fixed : P dummy)
    (x : RowBits s.rows w → Bool) (valid : ∀ i, P (fun j => x (i,j))) : ∀ i : Fin s.nextRows,
    P (fun j => s.run dummy real isDummy digit x (i,j)) := by
  intro i
  have dim := s.exact_packs (by omega)
  have bound : i.val/s.pack < s.packs :=
    (Nat.div_lt_iff_lt_mul (show 0<s.pack from Nat.two_pow_pos _)).mpr (i.isLt.trans_eq dim.symm)
  have inGrid : i.val/s.pack < 2^s.globalHeight := bound.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)
  let X := s.packedInput dummy real isDummy digit x
  let q : Row s.globalHeight := ⟨_,inGrid⟩
  let l : Fin s.pack := ⟨i.val%s.pack, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let sorted := stable (s.wideDigit digit isDummy) X
  have read : (fun j => s.run dummy real isDummy digit x (i,j)) = lane (sorted q) l :=
    s.leave_word sorted i inGrid
  rw [read]
  exact s.packed_words dummy real isDummy digit room P fixed x valid _ _

/-- Sorting and aligning the local blocks, then stably sorting the packed
words, preserves each real bucket and outputs globally sorted digits. -/
theorem correct (room : s.packBits+2 ≤ s.digitBits) (blank : dummy real = false) (flags : dummy isDummy= !(dummy real))
    (x : RowBits s.rows w → Bool) (valid : shapeFlags s.rows real isDummy x) :
    let new := realList real (s.run dummy real isDummy digit x)
    let old := realList real x
    new.Pairwise (fun a b => readKey digit a ≤ readKey digit b) ∧
      ∀ a, bucket (readKey digit) a new = bucket (readKey digit) a old := by
  let X := s.packedInput dummy real isDummy digit x
  let dp := Nat.two_pow_pos s.packBits
  let blockOutput := s.localOut dummy real isDummy digit x
  have same := s.pack_homogeneous dummy real isDummy digit room blank flags x valid
  have allFlags : ∀ q l, lane (X q) l isDummy = !(lane (X q) l real) :=
    s.packed_words dummy real isDummy digit room (fun z => z isDummy= !(z real)) flags x valid
  have support (q : Row s.globalHeight) (hr : lane (X q) ⟨0,dp⟩ real = true) : q.val < s.packs := by
    by_contra! h
    have off := s.wide_input_support dummy real isDummy digit room blank x q h ⟨0,dp⟩
    exact Bool.false_ne_true (off.symm.trans hr)
  have wide := pass_read s (by omega) digit real isDummy X same allFlags support
  refine ⟨wide.1,fun a => (wide.2 a).trans ?_⟩
  have bank : bucket (readKey digit) a (observed real X) =
      sweep (2^s.globalHeight) (fun r => sweep s.pack (fun i => observeRow real digit a (s.wideLane (staticRead (s.wideInput dummy) blockOutput) r i))) :=
    packed_bucket X real digit a
  have vol : s.nextRows ≤ 2^s.globalHeight*s.pack := by
    rw [←s.exact_packs (by omega)]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide : 1 < 2) _)
  rw [bank,s.wide_sweep dummy blockOutput (observeRow real digit a) (by simp [observeRow,blank]) (s.fits_local room) vol,
    s.retained_buckets dummy real isDummy digit room blank flags x valid a (s.fits_local room),sweep_rows]
  rfl

end
end Hierarchy.Tagged.Radix.PassShape

end OAI
