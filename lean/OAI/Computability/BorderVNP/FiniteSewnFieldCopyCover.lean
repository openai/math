import OAI.Computability.BorderVNP.FiniteSewnFieldPortCover

/-! # Concatenating the per-copy exterior intervals within a grouped port -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open scoped BigOperators Classical

/-- The actual copy-major intervals of a grouped word retain their new
source ordinals and shift the old offset by the copy's physical width. -/
noncomputable def copyIntervals (copies width : ℕ) (chunks : Fin copies → List Interval) : List Interval :=
  Finset.univ.toList.flatMap fun i => (chunks i).map (atOffset (i.val*width))

private theorem copyOrdinal {n m : ℕ} (i : Fin n) (j : Fin m) : (finProdFinEquiv (i,j)).val = i.val*m+j.val := by
  change j.val+m*i.val = _
  ac_rfl

/-- Repeated copying preserves the exact source classification of every old
bit, including zero clamps and empty grouped words. -/
theorem copies_cover {copies width next : ℕ} (read : Fin (copies*width) → Option (Fin next))
    (chunks : Fin copies → List Interval) (cover : ∀ i, Covers (chunks i) (fun j => read (finProdFinEquiv (i,j)))) :
    Covers (copyIntervals copies width chunks) read := by
  have mem (p : Interval) (hp : p ∈ copyIntervals copies width chunks) :
      ∃ i q, q ∈ chunks i ∧ atOffset (i.val*width) q = p := by
    simpa [copyIntervals,List.mem_flatMap,List.mem_map] using hp
  constructor
  · intro p hp
    obtain ⟨i,q,hq,rfl⟩ := mem p hp
    calc
      (i.val*width+q.oldStart)+q.width = i.val*width+(q.oldStart+q.width) := Nat.add_assoc ..
      _ ≤ i.val*width+width := Nat.add_le_add_left ((cover i).oldFit q hq) _
      _ = (i.val+1)*width := (Nat.succ_mul ..).symm
      _ ≤ copies*width := Nat.mul_le_mul_right width i.isLt
  · intro p hp j hj
    obtain ⟨i,q,hq,rfl⟩ := mem p hp
    exact (cover i).newFit q hq j hj
  · intro p hp j hj k hk
    obtain ⟨i,q,hq,rfl⟩ := mem p hp
    let l : Fin width := ⟨q.oldStart+j,(Nat.add_lt_add_left hj _).trans_le ((cover i).oldFit q hq)⟩
    have eqn : k = finProdFinEquiv (i,l) := Fin.ext (hk.trans ((Nat.add_assoc ..).trans (copyOrdinal i l).symm))
    rw [eqn]
    exact (cover i).agrees q hq j hj l rfl
  · intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨q,hq,l,hl,eqn⟩ := (cover i).covers j
    refine ⟨atOffset (i.val*width) q,List.mem_flatMap.mpr ⟨i,by simp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩,l,hl,?_⟩
    exact (copyOrdinal i j).trans ((congrArg (i.val*width+·) eqn).trans (Nat.add_assoc ..).symm)

/-- One physical width interval per copy of each genuine per-copy descriptor. -/
theorem copyIntervals_length {copies width : ℕ} (chunks : Fin copies → List Interval) :
    (copyIntervals copies width chunks).length = ∑ i, (chunks i).length := by
  simp [copyIntervals,List.length_flatMap]

end Packing.SewnField

end BorderVNP
end Computability
end OAI
