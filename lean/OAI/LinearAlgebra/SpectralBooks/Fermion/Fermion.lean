import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # The energy grading of integral fermionic states -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset

abbrev State := Finset ℕ

/-- Twice the fermionic energy; each occupied mode `i` costs `2*i+1`. -/
def weight (S : State) : ℕ := ∑ i ∈ S, (2*i + 1)

theorem mode_lt_weight {S : State} {i : ℕ} (hi : i ∈ S) : i < weight S := by
  have h := Finset.single_le_sum (f := fun j : ℕ ↦ 2*j+1) (fun _ _ ↦ Nat.zero_le _) hi
  unfold weight
  omega

theorem card_le_weight (S : State) : S.card ≤ weight S := by
  simpa only [weight, sum_const, smul_eq_mul, mul_one] using
    Finset.sum_le_sum (s := S) (f := fun _ : ℕ ↦ 1) (g := fun j ↦ 2*j+1)
      (fun i _ ↦ by omega)

/-- The finite list of all states below an integer bound on doubled energy.
A negative bound gives the empty list. -/
def states (B : ℤ) : Finset State := ((range B.toNat).powerset).filter (fun S ↦ (weight S : ℤ) ≤ B)

@[simp] theorem mem_states {S : State} {B : ℤ} : S ∈ states B ↔ (weight S : ℤ) ≤ B := by
  simp only [states, mem_filter, mem_powerset, and_iff_right_iff_imp]
  intro h i hi
  apply mem_range.mpr
  exact (mode_lt_weight hi).trans_le (by omega)

abbrev Label (H : ℕ) := ↥((states H).erase ∅)

@[simp] theorem empty_mem_states_nat (H : ℕ) : ∅ ∈ states (H : ℤ) := by
  simp [weight]

theorem label_nonempty {H : ℕ} (i : Label H) : i.val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase i.property)

theorem label_weight_le {H : ℕ} (i : Label H) : weight i.val ≤ H := by
  have h := mem_states.mp (Finset.mem_of_mem_erase i.property)
  exact_mod_cast h

theorem card_label (H : ℕ) : Fintype.card (Label H) = (states H).card - 1 := by
  simp [Label, Finset.card_erase_of_mem (empty_mem_states_nat H)]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
