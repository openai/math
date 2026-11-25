import OAI.Computability.NearSquareRoot.SynchronizedPadding
import OAI.Computability.NearSquareRoot.SynchronizedPair

/-! # The Walsh slot of a synchronized transform

Each participating block exposes its designated bit at the first coordinate.
The tensor of the local Walsh rounds is the normalized Walsh matrix on these
bits on every fiber of the spectator addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedSelected

open Finset Matrix SynchronizedPadding SynchronizedPair

noncomputable section

variable {ι : Type*} {A S : ι → Type*} [DecidableEq ι] [∀ i, DecidableEq (A i)]
    [∀ i, DecidableEq (S i)] (active : Finset ι) (split : ∀ i, A i ≃ Fin 2 × S i)

/-- Local matrix of the slot, with the identity on an idle block. -/
def block (i : ι) : Matrix (A i) (A i) ℂ :=
  if i ∈ active then of fun u v ↦
    if (split i u).2 = (split i v).2 then walsh (split i u).1 (split i v).1 else 0
  else 1

/-- All unselected bits agree. -/
def sameFiber (x y : ∀ i, A i) : Prop :=
  ∀ i, if i ∈ active then (split i (x i)).2 = (split i (y i)).2 else x i = y i

/-- Number of simultaneous ones among the designated bits. Its parity gives
the Walsh sign. -/
def overlap (x y : ∀ i, A i) : ℕ :=
  (active.filter fun i ↦ (split i (x i)).1 = 1 ∧ (split i (y i)).1 = 1).card

private theorem walsh_apply (u v : Fin 2) :
    walsh u v = (w : ℂ) * (if u = 1 ∧ v = 1 then -1 else 1) := by
  fin_cases u <;> fin_cases v <;> simp [walsh]

variable [Fintype ι]

instance (x y : ∀ i, A i) : Decidable (sameFiber active split x y) := by
  unfold sameFiber
  infer_instance

/-- Explicit kernel of a synchronized Walsh round, with normalization
`(1 / √2)^s` for `s` participating blocks. -/
theorem tensorMatrix_block_apply (x y : ∀ i, A i) :
    tensorMatrix (block active split) x y =
      (if sameFiber active split x y then
        (w : ℂ)^active.card * (-1)^overlap active split x y else 0) := by
  classical
  change (∏ i, block active split i (x i) (y i)) = _
  split_ifs with h
  · have he (i : ι) : block active split i (x i) (y i) =
        if i ∈ active then walsh (split i (x i)).1 (split i (y i)).1 else 1 := by
      have hi := h i
      by_cases ha : i ∈ active
      · simp only [ha, ite_true] at hi
        simp [block, ha, hi]
      · simp only [ha, ite_false] at hi
        simp [block, ha, one_apply, hi]
    simp_rw [he]
    rw [prod_ite_mem_eq]
    simp_rw [walsh_apply]
    rw [prod_mul_distrib, prod_const]
    congr 1
    simp only [overlap, ← prod_const, prod_filter]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    apply prod_eq_zero (mem_univ i)
    by_cases ha : i ∈ active <;> simp [block, ha] at hi ⊢ <;> simp [hi, one_apply]

/-- Replace just the chosen bits of an address by an arbitrary bit assignment. -/
def setBits (x : ∀ i, A i) (bits : active → Fin 2) (i : ι) : A i :=
  if hi : i ∈ active then (split i).symm (bits ⟨i, hi⟩, (split i (x i)).2) else x i

section Fiber
omit [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (S i)] [Fintype ι]

theorem setBits_injective (x : ∀ i, A i) :
    Function.Injective (setBits active split x) := by
  intro u v h
  funext i
  have hi := congrArg (fun y : ∀ j, A j ↦ (split i (y i)).1) h
  simpa [setBits, i.property] using hi

theorem sameFiber_setBits (x : ∀ i, A i) (bits : active → Fin 2) :
    sameFiber active split x (setBits active split x bits) := by
  intro i
  by_cases hi : i ∈ active <;> simp [setBits, hi]

theorem mem_range_setBits (x y : ∀ i, A i) :
    y ∈ Set.range (setBits active split x) ↔ sameFiber active split x y := by
  constructor
  · rintro ⟨u, rfl⟩
    exact sameFiber_setBits active split x u
  · intro h
    refine ⟨fun i ↦ (split i (y i)).1, ?_⟩
    funext i
    have hf := h i
    by_cases hi : i ∈ active
    · simp only [hi, ite_true] at hf
      simp [setBits, hi, hf]
    · simpa [setBits, hi] using hf

end Fiber

/-- Application of the slot is exactly a sum over the selected settings. -/
theorem tensorMatrix_block_mulVec [∀ i, Fintype (A i)] (f : (∀ i, A i) → ℂ)
    (x : ∀ i, A i) :
    (tensorMatrix (block active split) *ᵥ f) x =
      (w : ℂ)^active.card * ∑ bits : active → Fin 2,
        (-1)^overlap active split x (setBits active split x bits) *
          f (setBits active split x bits) := by
  classical
  rw [mul_sum]
  change (∑ y, tensorMatrix (block active split) x y * f y) = _
  symm
  apply Fintype.sum_of_injective (setBits active split x) (setBits_injective active split x)
  · intro y hy
    have h := (mem_range_setBits active split x y).not.mp hy
    simp [tensorMatrix_block_apply, h]
  · intro bits
    simp [tensorMatrix_block_apply, sameFiber_setBits, mul_assoc]

end
end SynchronizedSelected

end NearSquareRoot
end Computability
end OAI
