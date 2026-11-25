import OAI.Hierarchy.ProbeDensity
import OAI.Hierarchy.ProbeScore

namespace OAI
/-! # The exact fraction of marked physical tiles, summed over disjoint signed strata -/

namespace Hierarchy.AdaptiveProbe
open scoped Classical BigOperators
noncomputable section

/-- `stratum` may be the first signed axis passing the native per-stock ROM lookup.
Only its proved coverage is used for this lower bound, permitting any deterministic
tie rule. There are exactly 2k signed directions per true tile. -/
theorem stratum_count {V : Type*} [Fintype V] {k : ℕ} (hk : 0 < k) {M s T : ℝ}
    (_hs : 0 ≤ s) (s1 : s ≤ 1) (hT : 0 < T) (x : V → Fin k × Bool → ℝ)
    (cap : ∀ v j, rise M (x v j) ≤ 1)
    (energy : (Fintype.card V:ℝ) ≤ ∑ v, ∑ j, s*(rise M (x v j)/T)^2)
    (stratum : Fin k × Bool → Finset V)
    (covers : ∀ v, (∃ j, 1/(4*k) ≤ s*(rise M (x v j)/T)^2) → ∃ j, v ∈ stratum j) :
    (T^2/(4*k))*(Fintype.card V:ℝ) ≤ ∑ j, ((stratum j).card:ℝ) := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let charge := fun v j => s*(rise M (x v j)/T)^2
  let hit := Finset.univ.filter (fun v => ∃ j, 1/(4*k) ≤ charge v j)
  have unit (v : V) (j : Fin k × Bool) : charge v j ≤ 1/T^2 := by
    dsimp [charge]
    have r : (rise M (x v j))^2 ≤ (1:ℝ) := by
      nlinarith only [mul_self_le_mul_self (rise_nonneg M (x v j)) (cap v j)]
    have sc := mul_le_mul_of_nonneg_right s1 (sq_nonneg (rise M (x v j)/T))
    rw [one_mul,div_pow] at sc
    simpa only [div_pow] using sc.trans (div_le_div_of_nonneg_right r (sq_nonneg _))
  have many := mark_density charge unit energy
  have shape : (Fintype.card (Fin k × Bool):ℝ)=2*k := by simp [mul_comm]
  dsimp only at many
  rw [shape,show (2:ℝ)*(2*k)=4*k by ring] at many
  change (Fintype.card V:ℝ)/2 ≤ (hit.card:ℝ)*(2*k*(1/T^2)) at many
  have cover : hit ⊆ Finset.univ.biUnion stratum := by
    intro v hv
    obtain ⟨j,mem⟩ := covers v ((Finset.mem_filter.mp hv).2)
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,mem⟩
  have card := (Finset.card_le_card cover).trans (Finset.card_biUnion_le ..)
  have bound : (hit.card:ℝ) ≤ ∑ j, ((stratum j).card:ℝ) := by exact_mod_cast card
  apply le_trans _ bound
  have kp : 0 < (k:ℝ) := by exact_mod_cast hk
  rw [div_mul_eq_mul_div,div_le_iff₀ (show 0 < 4*(k:ℝ) by positivity)]
  have norm : (hit.card:ℝ)*(2*k*(1/T^2))=(hit.card*(2*k))/T^2 := by ring
  rw [norm,le_div_iff₀ (sq_pos_of_pos hT)] at many
  nlinarith only [many]

end
end Hierarchy.AdaptiveProbe

end OAI
