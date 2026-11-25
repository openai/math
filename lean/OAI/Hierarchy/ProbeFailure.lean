import OAI.Hierarchy.ProbeIntegerBatch
import OAI.Hierarchy.ProtocolConflictPack

namespace OAI
/-! # A positive density of usable, disjoint failed tests

Prices are per bit, and physical inventories are integral.  The batch below
uses exactly the integer part of w/(Kb), corresponding to alpha=1/K. -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- A fixed, finite discrepancy threshold in the native conflict scan gives a positive
number of disjoint roots when the mean discrepancy exceeds it. -/
theorem failed_packing {n d : ℕ} (disc : Fin n → ℝ) (adj : Fin n → Fin d → Fin n)
    (symm : ∀ v j, ∃ l, adj (adj v j) l = v) {ε C : ℝ} (hC : 0 ≤ C)
    (bounded : ∀ v, disc v ≤ C) (large : ε * n + ε * n ≤ ∑ v, disc v) :
    let fail := fun v => decide (ε < disc v)
    ε*n ≤ (ProtocolConflictPack.picked fail adj).card * (d+1:ℝ) * C := by
  classical
  let fail := fun v => decide (ε < disc v)
  let bad := Finset.univ.filter (fun v => fail v=true)
  have hε : 0 ≤ ε ∨ ε ≤ 0 := le_total _ _
  rcases hε with hε | neg
  · have row (v : Fin n) : disc v ≤ ε + if v ∈ bad then C else 0 := by
      by_cases h : v ∈ bad
      · simpa [h] using (show disc v ≤ ε+C by linarith [bounded v])
      · have ex : ¬ε < disc v := by simpa [bad,fail] using h
        simpa [h] using le_of_not_gt ex
    have total := Finset.sum_le_sum (s:=Finset.univ) fun v _ => row v
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Finset.sum_ite_mem,Finset.univ_inter,nsmul_eq_mul] at total
    have bounds := ProtocolConflictPack.density fail adj symm
    have realBound : (bad.card:ℝ) ≤ (ProtocolConflictPack.picked fail adj).card*(d+1:ℝ) := by
      exact_mod_cast bounds
    have cover := mul_le_mul_of_nonneg_right realBound hC
    change _ ≤ (ProtocolConflictPack.picked fail adj).card*(d+1:ℝ)*C
    linarith
  · exact (mul_nonpos_of_nonpos_of_nonneg neg (by positivity)).trans (by positivity)
end
end Hierarchy.AdaptiveProbe

end OAI
