import OAI.Computability.VPVNP.LiveHeaderComplete

/-!
# Physical input and output exponent words of a nominated pair

The first-half count uses the counter arrays on the two adjacent cuts of
the live chain. In the first group the preceding array is all zero. The
header's output memory supplies both arrays to the native exponent checker,
also after the auxiliary computation has modified its own scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM CutSchedule ChainAssignments ExponentTrace LiveHeader LiveHeaderSchedule
open LiveHeaderDescriptors
open scoped Fin.CommRing

variable {w d t Z base : ℕ} {s : Sizes} {hw : 4 ≤ w} {advice : Bits s.advice} {cuts : AllCuts s.h s.delta}
  {tag : Mode.Tag} {m : Memory w}

private theorem counters_at {q : Fin (2^(s.h+1)+1)} (k : Fin (2^s.h)) (eq : q = firstCut k)
    (hi : 0 < q.val) (half : q.val ≤ 2^s.h) (fit : 1+t*Z ≤ s.delta) :
    (firstHalfLayout s.h s.delta q.val t Z hi half fit (cuts q)).2.2.1 =
      counters fit (liveCutEquiv s.h s.delta cuts).1 k.succ := by
  subst q
  rfl

private theorem decoded_side {g : Fin (2^(s.h+1))} (out : Output s base d hw advice cuts g tag m)
    (side : Side) (k : Fin (2^s.h)) (cut : incidentCut side g = firstCut k)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) :
    ExponentWords (counters fit (liveCutEquiv s.h s.delta cuts).1 k.succ) (exponentBase s base side) m := by
  have pos : 0 < (incidentCut side g).val := by rw [cut]; exact Nat.succ_pos _
  have half : (incidentCut side g).val ≤ 2^s.h := by rw [cut]; exact k.isLt
  obtain ⟨before,_,img⟩ := out.fieldImage
  have decoded := img.pair_exponents ev side he fit pos half
  rwa [counters_at k cut pos half fit] at decoded

/-- All outgoing counters and the immediately preceding incoming counters
from the mathematical contraction are present in the real scratch banks. -/
theorem Output.pairExponentWords (i : Fin (2^s.h))
    (out : Output s base d hw advice cuts (halves s.h (.inl i)) tag m)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) :
    let fst := (liveCutEquiv s.h s.delta cuts).1
    ExponentWords (counters fit fst i.castSucc) (exponentBase s base .left) m ∧
      ExponentWords (counters fit fst i.succ) (exponentBase s base .right) m := by
  dsimp only
  refine ⟨?_,decoded_side out .right i (Fin.ext rfl) ev he fit⟩
  by_cases first : i.val = 0
  · have hi : i.castSucc = 0 := Fin.ext first
    rw [hi]
    obtain ⟨before,zero,img⟩ := out.fieldImage
    apply img.first_exponents first he
    intro a b
    have low : exteriorBase s base .left ≤ exponentBase s base .left := by
      dsimp [exponentBase,exteriorBase]; omega
    rw [zero _ (low.trans (Nat.le_add_right ..)), RAMSerialization.wordBits_zero]
    rfl
  · let k : Fin (2^s.h) := ⟨i.val-1,(Nat.sub_le _ _).trans_lt i.isLt⟩
    have val : k.val+1 = i.val := by dsimp [k]; omega
    have hi : i.castSucc = k.succ := Fin.ext val.symm
    rw [hi]
    exact decoded_side out .left k (Fin.ext val.symm) ev he fit

/-- Exactly the buffer hypothesis consumed by the native first-half
exponent-stage count. The two public operands address the decoded banks. -/
theorem Output.pairBufferValues (i : Fin (2^s.h))
    (out : Output s base d hw advice cuts (halves s.h (.inl i)) tag m)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) (room : limit s base ≤ 2^w)
    (pub : Fin 5 → BurstRAM.Word w) (left : (pub 0).val = exponentBase s base .left)
    (right : (pub 1).val = exponentBase s base .right) :
    let fst := (liveCutEquiv s.h s.delta cuts).1
    LiveExponent.BufferValues pub (counters fit fst i.castSucc) (counters fit fst i.succ) m := by
  obtain ⟨before,after⟩ := out.pairExponentWords i ev he fit
  have bounds (side : Side) : exponentBase s base side+t*Z ≤ 2^w := by
    rw [← he]
    exact (dest_bounds s base side .exponents (by decide)).2.trans room
  exact exponentBufferValues (by omega) pub (left ▸ before) (right ▸ after)
    (left ▸ bounds .left) (right ▸ bounds .right)

/-- The nomination and pair phases may change scratch outside the two
read-only banks. The same native checker then sees the original counters. -/
theorem Output.pairBufferValues_after (i : Fin (2^s.h))
    (out : Output s base d hw advice cuts (halves s.h (.inl i)) tag m)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) (room : limit s base ≤ 2^w)
    (pub : Fin 5 → BurstRAM.Word w) (left : (pub 0).val = exponentBase s base .left)
    (right : (pub 1).val = exponentBase s base .right) (afterPair : Memory w)
    (frame : ∀ side j, j < t*Z → afterPair (exponentBase s base side+j) = m (exponentBase s base side+j)) :
    let fst := (liveCutEquiv s.h s.delta cuts).1
    LiveExponent.BufferValues pub (counters fit fst i.castSucc) (counters fit fst i.succ) afterPair := by
  obtain ⟨before,after⟩ := out.pairExponentWords i ev he fit
  have bounds (side : Side) : exponentBase s base side+t*Z ≤ 2^w := by
    rw [← he]
    exact (dest_bounds s base side .exponents (by decide)).2.trans room
  exact exponentBufferValues (by omega) pub (left ▸ before.congr (frame .left)) (right ▸ after.congr (frame .right))
    (left ▸ bounds .left) (right ▸ bounds .right)

private theorem exterior_at {q : Fin (2^(s.h+1)+1)} (k : Fin (2^s.h)) (eq : q = firstCut k)
    (hi : 0 < q.val) (half : q.val ≤ 2^s.h) (fit : 1+t*Z ≤ s.delta) (dst : ℕ)
    (stored : ∀ j : Fin (width (s.h+1) s.delta (2*q.val)),
      m (dst+j.val) = PrimedInputRAM.encodeBit w ((firstHalfLayout s.h s.delta q.val t Z hi half fit (cuts q)).2.1 j)) :
    ∀ j : Fin (width (s.h+1) s.delta (2*k.succ.val)),
      m (dst+j.val) = PrimedInputRAM.encodeBit w (exteriorOf fit (liveCutEquiv s.h s.delta cuts).1 k.succ j) := by
  subst q
  exact stored

private theorem decoded_exterior {g : Fin (2^(s.h+1))} (out : Output s base d hw advice cuts g tag m)
    (side : Side) (k : Fin (2^s.h)) (cut : incidentCut side g = firstCut k)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) :
    ∀ j : Fin (width (s.h+1) s.delta (2*k.succ.val)), m (exteriorBase s base side+j.val) =
      PrimedInputRAM.encodeBit w (exteriorOf fit (liveCutEquiv s.h s.delta cuts).1 k.succ j) := by
  have pos : 0 < (incidentCut side g).val := by rw [cut]; exact Nat.succ_pos _
  have half : (incidentCut side g).val ≤ 2^s.h := by rw [cut]; exact k.isLt
  obtain ⟨_,_,img⟩ := out.fieldImage
  exact exterior_at k cut pos half fit _ (img.pair_exterior ev side he fit pos half)

/-- The two exterior fields are the actual physical sources of the
auxiliary RAM at the adjacent primed even cuts. Empty fields at either
primed endpoint have no read addresses. -/
theorem Output.pairExteriorWords (i : Fin (2^s.h))
    (out : Output s base d hw advice cuts (halves s.h (.inl i)) tag m)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) :
    let ξ := exteriorOf fit (liveCutEquiv s.h s.delta cuts).1
    let L := PairedChain.lengths s.h s.delta s.advice i
    (∀ j : Fin L.leftCut, m (exteriorBase s base .left+j.val) = PrimedInputRAM.encodeBit w (ξ i.castSucc j)) ∧
    (∀ j : Fin L.rightCut, m (exteriorBase s base .right+j.val) = PrimedInputRAM.encodeBit w (ξ i.succ j)) := by
  dsimp only
  refine ⟨?_, decoded_exterior out .right i (Fin.ext rfl) ev he fit⟩
  change ∀ j : Fin (width (s.h+1) s.delta (2*i.castSucc.val)), m (exteriorBase s base .left+j.val) =
    PrimedInputRAM.encodeBit w (exteriorOf fit (liveCutEquiv s.h s.delta cuts).1 i.castSucc j)
  by_cases first : i.val = 0
  · intro j
    have zero : (width (s.h+1) s.delta (2*i.castSucc.val)) = 0 := by
      change width (s.h+1) s.delta (2*i.val) = 0
      simp [first]
    exact Fin.elim0 (j.cast zero)
  · let k : Fin (2^s.h) := ⟨i.val-1,(Nat.sub_le _ _).trans_lt i.isLt⟩
    have val : k.val+1 = i.val := by dsimp [k]; omega
    have hi : i.castSucc = k.succ := Fin.ext val.symm
    rw [hi]
    exact decoded_exterior out .left k (Fin.ext val.symm) ev he fit

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
