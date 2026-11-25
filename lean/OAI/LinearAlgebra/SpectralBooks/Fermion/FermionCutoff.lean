import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionFactor
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickModes
import OAI.LinearAlgebra.SpectralBooks.Fermion.Pascal

/-!
# Finite truncations of the fermionic coefficient identity

For each multiplier monomial the matrix product in one order uses an
intermediate state of doubled energy at most `E+H+2s`. The reversed order
uses at most `E+H-2s`. These estimates apply directly to the integral field
coefficients, including cutoffs below zero.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset Filter
open scoped BigOperators

/-- The entrywise field identity after a sufficiently large finite cutoff
on occupied modes. The threshold may depend on the specific coefficients. -/
def TruncatedIdentity : Prop :=
  ∀ (i j α β : State) (_ : i.Nonempty) (_ : i.card = j.card) (s : ℤ),
    let L := order (weight i) (weight j)
    ∀ᶠ N : ℕ in atTop,
      pairing i j * (if α = β then 1 else 0) =
        ∑ a ∈ range (L+1), multiplier L a *
          ((∑ k ∈ (range N).powerset, blockMode i (-s-1-L+a) α k * blockMode j (s-a) k β) -
            (-1)^(i.card*j.card) * ∑ k ∈ (range N).powerset,
              blockMode j (s-a) α k * blockMode i (-s-1-L+a) k β)

private theorem states_subset {B : ℤ} {N : ℕ} (hN : B ≤ N) :
    states B ⊆ (range N).powerset := by
  intro S hS
  apply mem_powerset.mpr
  intro i hi
  have hw := mem_states.mp hS
  exact mem_range.mpr ((mode_lt_weight hi).trans_le (by omega))

/-- Mode cutoff and intermediate-energy cutoff give the same weighted matrix
entry. Only modes occupied by the field inputs and outputs can contribute. -/
theorem coefficientIdentity_of_truncated (h : TruncatedIdentity) :
    CoefficientIdentity pairing blockMode := by
  intro H E s i j hij α β
  have hi := label_weight_le i
  have hj := label_weight_le j
  have hβ := mem_states.mp β.property
  let L := order (weight i.val) (weight j.val)
  have hL : L ≤ H := by dsimp [L, order]; omega
  obtain ⟨N, hN, hN'⟩ := ((h i.val j.val α.val β.val (label_nonempty i) hij s).and
    (eventually_ge_atTop (max (E+H+2*s).toNat (E+H-2*s).toNat))).exists
  let term (U V : Finset State) (a : ℕ) : ℤ := multiplier L a *
    ((∑ k ∈ U, blockMode i.val (-s-1-L+a) α.val k * blockMode j.val (s-a) k β.val) -
      (-1)^(i.val.card*j.val.card) * ∑ k ∈ V,
        blockMode j.val (s-a) α.val k * blockMode i.val (-s-1-L+a) k β.val)
  have hc : α = β ↔ α.val = β.val := Subtype.ext_iff
  rw [if_congr hc rfl rfl, hN]
  dsimp only
  trans ∑ a : Fin (H+1), term (states (E+H+2*s)) (states (E+H-2*s)) a.val
  swap
  · apply sum_congr rfl
    intro a _
    dsimp only [term]
    rw [sum_coe_sort (states (E+H+2*s)) (fun k ↦ blockMode i.val (-s-1-L+a) α.val k *
      blockMode j.val (s-a) k β.val),
      sum_coe_sort (states (E+H-2*s)) (fun k ↦ blockMode j.val (s-a) α.val k *
        blockMode i.val (-s-1-L+a) k β.val)]
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset_zero_on_sdiff (range_mono (Nat.succ_le_succ hL))
  · intro a ha
    have hla : L < a := by
      have hn := (mem_sdiff.mp ha).2
      simpa only [mem_range, not_lt, Nat.succ_le_iff] using hn
    simp [term, multiplier, Nat.choose_eq_zero_of_lt hla]
  · intro a ha
    have haL := mem_range_succ_iff.mp ha
    dsimp only [term]
    congr 1
    congr 1
    · apply (sum_subset (states_subset (B := E+H+2*s) (by omega)) ?_).symm
      intro k _ hk
      rw [mem_states] at hk
      by_cases hmk : blockMode j.val (s-a) k β.val = 0
      · simp [hmk]
      · have hw := weight_eq_of_blockMode_ne_zero hmk
        omega
    · congr 1
      apply (sum_subset (states_subset (B := E+H-2*s) (by omega)) ?_).symm
      intro k _ hk
      rw [mem_states] at hk
      by_cases hmk : blockMode i.val (-s-1-L+a) k β.val = 0
      · exact mul_eq_zero_of_right _ hmk
      · have hw := weight_eq_of_blockMode_ne_zero hmk
        omega

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
