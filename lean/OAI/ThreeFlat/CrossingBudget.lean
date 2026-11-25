import OAI.ThreeFlat.CrossingSupply
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Module.BigOperators

namespace OAI
/-! # Width budgets after pooling catalytic crossing supplies -/

namespace ThreeFlat.CrossingSupply

open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators

noncomputable section

private theorem matching_width (c : Bool) (w : ℕ) : matching c w = w • matching c 1 := by
  cases c <;> simp [matching, wire, smul_add, Finsupp.smul_single]

private theorem slack_width (w : ℕ) : slack w = w • slack 1 := by
  simp [slack, wire, smul_add, Finsupp.smul_single]

/-- Pooling the two terminal transfers keeps them supported on the arms of the four sites. -/
def pooledArms (q R : ℕ) (n : SupplyChoice → ℕ) : Widths 6 :=
  ∑ j, n j • (transfer q R 0 2 j.2.1 + transfer q R 1 3 j.2.2)

theorem arms_supported (i : Fin 4) (u v : ℕ) (e : Chord 6)
    (he : ¬ (e.1.1 < 4 ∧ 4 ≤ e.1.2)) : arms i u v e = 0 := by
  have hw (k : Fin 6) (hik : site i < k) (hk : 4 ≤ k) (w : ℕ) :
      wire (site i) k hik w e = 0 := by
    apply Finsupp.single_eq_of_ne'
    rintro rfl
    exact he ⟨i.isLt, hk⟩
  simp only [arms, Finsupp.add_apply, hw 4 _ le_rfl, hw 5 _ (by decide), zero_add]

theorem pooledArms_supported (q R : ℕ) (n : SupplyChoice → ℕ) (e : Chord 6)
    (he : ¬ (e.1.1 < 4 ∧ 4 ≤ e.1.2)) : pooledArms q R n e = 0 := by
  classical
  have htransfer (i j : Fin 4) (sign : Bool) : transfer q R i j sign e = 0 := by
    cases sign <;> simp [transfer, arms_supported _ _ _ e he]
  simp [pooledArms, htransfer, Finsupp.finsetSum_apply]

theorem side_load (i : Fin 6) (hi : 4 ≤ i) (u v t : ℕ) :
    load i (matching true u + matching false v + slack t) = 0 := by
  have hne (j : Fin 6) (hj : j < 4) : i ≠ j := ne_of_gt (hj.trans_le hi)
  simp [matching, slack, hne 0 (by decide), hne 1 (by decide),
    hne 2 (by decide), hne 3 (by decide)]

/-- Each local matching uses a common width on its two edges. Their pooled widths total
the demand width. The equal contribution on all six internal pairs and the total loads
at the two memory terminals survive every selector word of a finite wire tile. -/
theorem aggregate_supply_budgets (q R : ℕ) (hR : 2 ≤ R)
    (n : SupplyChoice → ℕ) {m : ℕ} (hm : ∑ j, n j = m) :
    ∃ u v : ℕ, u + v = 4*q*m ∧
      (∑ j, n j • supply q R j) =
        matching true u + matching false v + slack (2*m) + pooledArms q R n ∧
      load 4 (∑ j, n j • supply q R j) = 4*q*R*m ∧
      load 5 (∑ j, n j • supply q R j) = 4*q*R*m := by
  classical
  let U (j : SupplyChoice) := if j.1 then n j * (4*q) else 0
  let V (j : SupplyChoice) := if j.1 then 0 else n j * (4*q)
  refine ⟨∑ j, U j, ∑ j, V j, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib, ← hm, Nat.mul_comm (4*q), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by cases h : j.1 <;> simp [U, V, h]
  · have hmatch (j : SupplyChoice) :
        n j • matching j.1 (4*q) =
          U j • matching true 1 + V j • matching false 1 := by
      rw [matching_width j.1, smul_smul]
      cases h : j.1 <;> simp [U, V, h]
    simp only [supply, smul_add, hmatch, Finset.sum_add_distrib, pooledArms]
    rw [← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul, hm,
      ← matching_width, ← matching_width, slack_width 2, smul_smul, Nat.mul_comm m 2,
      ← slack_width]
  · simp only [map_sum, map_nsmul, supply_load_four q R hR, Nat.nsmul_eq_mul,
      ← Finset.sum_mul, hm, Nat.mul_comm m]
  · simp only [map_sum, map_nsmul, supply_load_five q R hR, Nat.nsmul_eq_mul,
      ← Finset.sum_mul, hm, Nat.mul_comm m]

end
end ThreeFlat.CrossingSupply

end OAI
