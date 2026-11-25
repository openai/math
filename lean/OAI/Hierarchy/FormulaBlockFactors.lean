import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi

namespace OAI
/-! # Sums of tensors with low grouped rank on specified partitions -/

namespace Hierarchy.FormulaPartitionRank

open scoped BigOperators

variable {P J C : Type} {ν : P → Type} {F : Type*} [CommSemiring F]

/-- One product expansion on the blocks of the leg assignment `σ`. -/
def HasBlockFactors [Fintype J] (σ : P → J) (R : ℕ) (T : (∀ p, ν p) → F) : Prop :=
  ∃ g : Fin R → (j : J) → ((p : {p // σ p = j}) → ν p.val) → F,
    ∀ x, T x = ∑ r, ∏ j, g r j (fun p => x p.val)

/-- Each summand uses the leg partition at its own index. -/
def partitionRankSums [Fintype C] [Fintype J] (partition : C → P → J) (R : ℕ) :
    Set ((∀ p, ν p) → F) :=
  (fun Y : C → (∀ p, ν p) → F => ∑ c, Y c) '' {Y | ∀ c, HasBlockFactors (partition c) R (Y c)}

/-- Summing the rank terms belonging to each partition gives a family of
tensors with the required grouped ranks. -/
theorem mem_partitionRankSums_of_expansion [Fintype C] [Fintype J]
    (partition : C → P → J) (R : ℕ) (T : (∀ p, ν p) → F)
    (g : (c : C) → Fin R → (j : J) → ((p : {p // partition c p = j}) → ν p.val) → F)
    (h : ∀ x, T x = ∑ c, ∑ r, ∏ j, g c r j (fun p => x p.val)) :
    T ∈ partitionRankSums partition R := by
  let Y (c : C) (x : ∀ p, ν p) := ∑ r, ∏ j, g c r j (fun p => x p.val)
  refine ⟨Y, fun c => ⟨g c, fun _ => rfl⟩, ?_⟩
  funext x
  simpa only [Finset.sum_apply, Y] using (h x).symm

end Hierarchy.FormulaPartitionRank

end OAI
