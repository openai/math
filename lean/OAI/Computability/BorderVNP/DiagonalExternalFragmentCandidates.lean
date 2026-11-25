import OAI.Computability.BorderVNP.DiagonalExternalFragmentStream
import OAI.Computability.BorderVNP.PackedDirectoryBudget
import OAI.Computability.BorderVNP.PrivatePlacementNetwork

/-! # The exact private and live candidate positions in the sparse fragment stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Packing.Directory RoutingISA
open private liveReencode from OAI.Computability.BorderVNP.PackedDirectoryBudget

/-- Exhaustive decoding of a raw public index in the compacting scan. The
field ranges can be empty, in which case there are no live candidates. -/
theorem candidate_cases (d : Layout) (pp lp : ℕ → ℕ × ℕ) (i : Fin d.candidates) :
    (∃ (j : Fin d.entries) (k : Fin 2), i.val = privateIndex j k ∧ d.row pp lp i = d.privateRow pp j k) ∨
      ∃ (t : Fin d.teams) (p : Fin d.processors) (f : Fin d.fields) (k : Fin (d.literal/d.block+2)),
        i.val = d.liveIndex t p f k ∧ d.row pp lp i = d.liveRow lp t p f k := by
  by_cases priv : i.val < 2*d.entries
  · let j : Fin d.entries := ⟨i.val/2,(Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)⟩
    let k : Fin 2 := ⟨i.val%2,Nat.mod_lt _ (by decide)⟩
    have eq : privateIndex j k = i.val := Nat.div_add_mod i.val 2
    exact Or.inl ⟨j,k,eq.symm,(congrArg (d.row pp lp) eq.symm).trans (d.row_privateIndex pp lp j k).2⟩
  · let q := i.val-2*d.entries
    let count := d.literal/d.block+2
    let u := q/count
    let a := u/d.fields
    have hq : q < d.teams*d.processors*d.fields*count := by
      have hi := i.isLt
      change i.val < 2*d.entries+d.teams*d.processors*d.fields*count at hi
      dsimp [q]; omega
    have hc : 0 < count := Nat.zero_lt_succ _
    have hf : 0 < d.fields := by
      by_contra! h
      rw [Nat.le_zero.mp h,Nat.mul_zero,Nat.zero_mul] at hq
      omega
    have hp : 0 < d.processors := by
      by_contra! h
      rw [Nat.le_zero.mp h,Nat.mul_zero,Nat.zero_mul,Nat.zero_mul] at hq
      omega
    have hu : u < d.teams*d.processors*d.fields := (Nat.div_lt_iff_lt_mul hc).mpr hq
    have ha : a < d.teams*d.processors := (Nat.div_lt_iff_lt_mul hf).mpr hu
    let t : Fin d.teams := ⟨a/d.processors,(Nat.div_lt_iff_lt_mul hp).mpr ha⟩
    let p : Fin d.processors := ⟨a%d.processors,Nat.mod_lt _ hp⟩
    let f : Fin d.fields := ⟨u%d.fields,Nat.mod_lt _ hf⟩
    let k : Fin count := ⟨q%count,Nat.mod_lt _ hc⟩
    have eq : d.liveIndex t p f k = i.val := liveReencode d i.val (by omega)
    exact Or.inr ⟨t,p,f,k,eq.symm,(congrArg (d.row pp lp) eq.symm).trans (d.row_liveIndex pp lp t p f k).2⟩

/-- The native private prefix pass puts every description after the actual
supplied width, before adding the reserved report gap and earlier descriptions. -/
theorem private_after_of_image {w : ℕ} (l : PrivatePlacement.Layout) (before after supplied : ℕ → ℕ)
    (image : l.Image before l.entries after) (fit : l.Fits w before)
    (counts : ∀ j : Fin l.entries, before (l.supplied+l.owner before j.val) = supplied (l.owner before j.val))
    (j : Fin l.entries) :
    supplied (ISA.placement after l.raw j.val).1 ≤ (ISA.placement after l.raw j.val).2 := by
  have owner := image.owner_eq fit j.isLt
  have slot := image.slots j.val j.isLt
  change supplied (after (l.raw+j.val*2)) ≤ after (l.raw+j.val*2+1)
  rw [Nat.mul_comm j.val 2,owner,slot,counts]
  omega

/-- Every private-tail candidate is rejected by the supplied-bank boundary test. -/
theorem live_private_none (d : Layout) (pp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (privateAfter : ∀ j : Fin d.entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (j : Fin d.entries) (k : ℕ) :
    live supplied base (d.privateRow pp j k) = none := by
  unfold live
  rw [ite_eq_right]
  rintro ⟨h,_⟩
  change (pp j.val).2 + _ < supplied (pp j.val).1 at h
  have := privateAfter j
  omega

/-- A retained data candidate has its true live source ordinals and within-field
step; the raw index can therefore be compared in its original traversal order. -/
theorem retained_live_candidate (d : Layout) (pp lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (privateAfter : ∀ j : Fin d.entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (i : Fin d.candidates) {q : Quad} (hq : live supplied base (d.row pp lp i) = some q) :
    ∃ (t : Fin d.teams) (p : Fin d.processors) (f : Fin d.fields) (k : Fin (d.literal/d.block+2)),
      i.val = d.liveIndex t p f k ∧ d.row pp lp i = d.liveRow lp t p f k := by
  rcases candidate_cases d pp lp i with ⟨j,k,_,hj⟩ | h
  · rw [hj,live_private_none d pp supplied base privateAfter] at hq
    cases hq
  · exact h

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
