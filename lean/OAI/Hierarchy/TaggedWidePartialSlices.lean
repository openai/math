import OAI.Hierarchy.TaggedShorterFields
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Removing the unused high coordinates of each physical lane -/

namespace Hierarchy.TaggedShorterFields
noncomputable section
open scoped Classical BigOperators
variable {I F : Type*} [Fintype I] [CommSemiring F] (bits width count : I → ℕ)

def highZeros (y : ∀ i, Fin (count i) → Fin (width i) → Bool) : Prop :=
  ∀ i k j, bits i ≤ k.val * width i + j.val → y i k j = false

def allSlices (x : ∀ i,Fin (bits i) → Bool) : ∀ i,Fin (count i) → Fin (width i) → Bool :=
  fun i k => slice (width i) (x i) k.val

private def reassemble (room : ∀ i,bits i≤count i*width i)
    (y : ∀ i,Fin (count i) → Fin (width i) → Bool) : ∀ i, Fin (bits i) → Bool :=
  fun i t => let atBit := finProdFinEquiv.symm (t.castLE (room i))
             y i atBit.1 atBit.2

omit [Fintype I] in
theorem slices_highZeros (x : ∀ i,Fin (bits i) → Bool) :
    highZeros bits width count (allSlices bits width count x) := by
  intro i k j hi
  simp [allSlices,slice,not_lt.mpr hi]

omit [Fintype I] in
private theorem reassemble_slices (room : ∀ i,bits i≤count i*width i)
    (y : ∀ i,Fin (count i) → Fin (width i) → Bool) (ok : highZeros bits width count y) :
    allSlices bits width count (reassemble bits width count room y) = y := by
  funext i k j
  by_cases h : k.val*width i+j.val < bits i
  · let u : Fin (bits i) := ⟨k.val*width i+j.val,h⟩
    have address : u.castLE (room i)=finProdFinEquiv (k,j) := by
      apply Fin.ext
      simp [u,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    change slice (width i) (reassemble bits width count room y i) k.val j = _
    rw [slice,dite_eq_left h]
    change y i (finProdFinEquiv.symm (u.castLE (room i))).1 (finProdFinEquiv.symm (u.castLE (room i))).2 = _
    rw [address,Equiv.symm_apply_apply]
  · simp [allSlices,slice,h,ok i k j (Nat.le_of_not_gt h)]

/-- After the physical stacks identify the two endpoints of each live lane,
the high-zero guards remove all unused coordinates. Even when several
slices belong to a single wide occurrence the remaining wires are summed
exactly once per original link bit assignment. -/
theorem sum_sliced (room : ∀ i,bits i≤count i*width i)
    (φ : (∀ i,Fin (count i) → Fin (width i) → Bool) → F) :
    (∑ y, if highZeros bits width count y then φ y else 0) =
      ∑ x,φ (allSlices bits width count x) := by
  classical
  let emb : (∀ i,Fin (bits i) → Bool) ↪ (∀ i,Fin (count i) → Fin (width i) → Bool) :=
    ⟨allSlices bits width count,fun a c h=>funext fun i=>
      (eq_iff_slices (room i) (a i) (c i)).mp (fun k=>congrFun (congrFun h i) k)⟩
  let weight (y : ∀ i,Fin (count i) → Fin (width i) → Bool) :=
    if highZeros bits width count y then φ y else 0
  change (∑ y,weight y)=_
  calc
    _ = ∑ y ∈ Finset.univ.map emb,weight y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ missing
      apply ite_eq_right
      intro ok
      exact missing (Finset.mem_map.mpr ⟨reassemble bits width count room y,Finset.mem_univ _,
        reassemble_slices bits width count room y ok⟩)
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro a _
      exact ite_eq_left (slices_highZeros bits width count a)

end
end Hierarchy.TaggedShorterFields

end OAI
