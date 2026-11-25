import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Counting leaves in the straightening procedure

Replacing one packet of `m` bits branches at most `2^(σm)` times and lowers
the integral potential by at least `m` along every branch. The actual packet
width and the children can depend on the current graph. A terminal expansion
costs a fixed factor for the bounded-width wires that still cross.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

section

/-- Iterate direct-sum comparisons, with bounds on the number of sources and
on each source's incident widths. `bounded y x` records the latter condition,
and `good` is the noncrossing predicate. -/
theorem straightening_count_of_steps {S R : Type*} [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] (tensor : S → R) (potential : S → ℕ)
    (good : S → Prop) (bounded : S → S → Prop)
    (trans : ∀ {u v w}, bounded u v → bounded v w → bounded u w) {σ D : ℝ} (hσ : 0 ≤ σ)
    (step : ∀ x : S,
      (∃ (L : ℕ) (terms : Fin L → S), (L:ℝ) ≤ (2:ℝ)^D ∧
        (∀ i, good (terms i) ∧ bounded (terms i) x) ∧ tensor x ≤ ∑ i, tensor (terms i)) ∨
      (∃ m : ℕ, 0 < m ∧ ∃ (L : ℕ) (terms : Fin L → S), (L:ℝ) ≤ (2:ℝ)^(σ*m) ∧
        (∀ i, potential (terms i) + m ≤ potential x ∧ bounded (terms i) x) ∧
        tensor x ≤ ∑ i, tensor (terms i))) (x : S) :
    ∃ (L : ℕ) (terms : Fin L → S), (L:ℝ) ≤ (2:ℝ)^(σ * potential x + D) ∧
      (∀ i, good (terms i) ∧ bounded (terms i) x) ∧ tensor x ≤ ∑ i, tensor (terms i) := by
  induction h : potential x using Nat.strong_induction_on generalizing x with
  | h d ih =>
    rcases step x with ⟨L,t,hL,ht,hs⟩ | ⟨m, hm, L, t, hL, ht, hs⟩
    · refine ⟨L, t, hL.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_), ht, hs⟩
      linarith only [mul_nonneg hσ (Nat.cast_nonneg (α := ℝ) d)]
    · have smaller (i : Fin L) : potential (t i) < d := by
        have := (ht i).1
        omega
      choose size leaf hcount hleaf hcomp using fun i => ih _ (smaller i) _ rfl
      let P := (i : Fin L) × Fin (size i)
      let fam (p : P) := leaf p.1 p.2
      let e := Fintype.equivFin P
      let b := (2:ℝ)^(σ * ((d:ℝ)-m) + D)
      have hb (i : Fin L) : (size i : ℝ) ≤ b := by
        apply (hcount i).trans
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_left _ hσ
        have hpm : potential (t i) + m ≤ d := (ht i).1.trans_eq h
        have hh : (potential (t i):ℝ) + m ≤ d := by exact_mod_cast hpm
        linarith
      refine ⟨Fintype.card P, fam ∘ e.symm, ?_, fun i => ⟨(hleaf _ _).1,
        trans (hleaf _ _).2 (ht _).2⟩, ?_⟩
      · calc
          (Fintype.card P:ℝ) = ∑ i, (size i : ℝ) := by simp [P]
          _ ≤ ∑ _i : Fin L, b := Finset.sum_le_sum fun i _ => hb i
          _ = L*b := by simp
          _ ≤ (2:ℝ)^(σ*m)*b := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (by norm_num) _)
          _ = _ := by
            dsimp [b]
            rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
            congr 1
            ring
      · calc
          tensor x ≤ ∑ i, tensor (t i) := hs
          _ ≤ ∑ i, ∑ j, tensor (leaf i j) := Finset.sum_le_sum fun i _ => hcomp i
          _ = ∑ p : P, tensor (fam p) := (Fintype.sum_sigma (fun p : P => tensor (fam p))).symm
          _ = _ := Fintype.sum_equiv e _ _ fun p => by simp

end

end

end SpectralBooks
end LinearAlgebra
end OAI
