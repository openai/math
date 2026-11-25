import OAI.LinearAlgebra.SpectralBooks.FactorialEstimate
import OAI.LinearAlgebra.SpectralBooks.WordPermutations
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Counting balanced words

Numbering the positions of each letter shows that the number of words with
constant multiplicity `k` is `(R * k)! / (k!)^R`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Balanced words of length `R * k` on `R` letters. -/
abbrev BalancedWords (R k : ℕ) := WordsOfContent (Fin (R * k)) (Fin R) (fun _ => k)

/-- Label the positions in each fiber of a word by the second coordinate of a bijection. -/
private def labelFiber {ι α β : Type*} (w : ι → α) (e : ι ≃ α × β)
    (h : ∀ i, (e i).1 = w i) (a : α) : {i // w i = a} ≃ β where
  toFun i := (e i.1).2
  invFun b := ⟨e.symm (a, b), by rw [← h, e.apply_symm_apply]⟩
  left_inv i := by
    apply Subtype.ext
    apply e.injective
    change e (e.symm (a, (e i.1).2)) = e i.1
    rw [e.apply_symm_apply]
    exact Prod.ext ((h i.1).trans i.2).symm rfl
  right_inv b := by simp

private def joinLabels {ι α β : Type*} (w : ι → α) (label : ∀ a, {i // w i = a} ≃ β) :
    ι ≃ α × β :=
  (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight label).trans (Equiv.sigmaEquivProd _ _))

private def firstWord {R k : ℕ} (e : Fin (R * k) ≃ Fin R × Fin k) :
    BalancedWords R k :=
  ⟨fun i => (e i).1, fun a => (Fintype.card_congr (labelFiber _ e (fun _ => rfl) a)).trans
    (Fintype.card_fin _)⟩

private def firstWordFiberEquiv {R k : ℕ}
    (w : BalancedWords R k) :
    {e // firstWord e = w} ≃ ((a : Fin R) → {i // w.1 i = a} ≃ Fin k) where
  toFun e := labelFiber w.1 e.1 fun i => congrArg (fun w => w.1 i) e.2
  invFun label := ⟨joinLabels w.1 label, Subtype.ext rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Prod.ext (congrArg (fun w => w.1 i) e.2).symm rfl
  right_inv label := by
    funext a
    apply Equiv.ext
    rintro ⟨i, rfl⟩
    rfl

/-- The multinomial formula for the type with all letter counts equal to `k`. -/
theorem card_balancedWords_mul_factorial (R k : ℕ) :
    Fintype.card (BalancedWords R k) * k.factorial ^ R =
      (R * k).factorial := by
  classical
  let E := Fin (R * k) ≃ Fin R × Fin k
  have hfiber (w : BalancedWords R k) : Fintype.card {e : E // firstWord e = w} = k.factorial ^ R := by
    rw [Fintype.card_congr (firstWordFiberEquiv w), Fintype.card_pi]
    have he (a : Fin R) : Fintype.card ({i // w.1 i = a} ≃ Fin k) = k.factorial := by
      rw [Fintype.card_equiv (Fintype.equivFinOfCardEq (w.2 a)), w.2 a]
    simp [he]
  calc
    _ = ∑ _w : BalancedWords R k, k.factorial ^ R := by simp
    _ = ∑ w : BalancedWords R k, Fintype.card {e : E // firstWord e = w} := Finset.sum_congr rfl fun w _ =>
      (hfiber w).symm
    _ = Fintype.card E := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv firstWord)
    _ = _ := by
      rw [Fintype.card_equiv finProdFinEquiv.symm, Fintype.card_fin]

theorem card_balancedWords_le (R k : ℕ) :
    Fintype.card (BalancedWords R k) ≤ R ^ (R * k) := by
  simpa using Fintype.card_le_of_injective (fun w : BalancedWords R k => w.1) (fun _ _ h => Subtype.ext h)

/-- Explicit two-sided form of the balanced-word count in the permutation stretch. -/
theorem logb_card_balancedWords_bounds {R k : ℕ} (hR : 0 < R) (hk : 0 < k) :
    (R : ℝ) * k * Real.logb 2 R - R * (1 / Real.log 2 + Real.logb 2 k / 2) ≤
        Real.logb 2 (Fintype.card (BalancedWords R k)) ∧
      Real.logb 2 (Fintype.card (BalancedWords R k)) ≤ (R : ℝ) * k * Real.logb 2 R := by
  refine ⟨balanced_logb_lower hR hk (card_balancedWords_mul_factorial R k), ?_⟩
  have hpos : 0 < Fintype.card (BalancedWords R k) := Nat.pos_of_mul_pos_right
    ((card_balancedWords_mul_factorial R k) ▸ Nat.factorial_pos _)
  have hupper : (Fintype.card (BalancedWords R k) : ℝ) ≤ (R : ℝ) ^ (R * k) := by
    exact_mod_cast card_balancedWords_le R k
  simpa only [Real.logb_pow, Nat.cast_mul] using
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hpos) hupper

open Filter in
open scoped Topology in
/-- Along multiples of the alphabet size, balanced words have the same exponential
growth rate as all words. -/
theorem tendsto_logb_card_balancedWords_div_length {R : ℕ} (hR : 0 < R) :
    Tendsto (fun k : ℕ ↦ Real.logb 2 (Fintype.card (BalancedWords R k)) / ((R : ℝ) * k))
      atTop (𝓝 (Real.logb 2 R)) :=
  tendsto_balanced_logb_div_length hR _ (fun k _ => card_balancedWords_mul_factorial R k)
    (fun k _ => card_balancedWords_le R k)

end SpectralBooks
end LinearAlgebra
end OAI
