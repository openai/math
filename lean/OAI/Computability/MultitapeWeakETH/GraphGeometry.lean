import OAI.Computability.MultitapeWeakETH.Supply

/-! # Quantitative placement estimates for a padded multigraph -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.SpectralGeometry VPVNP.WireGeometry
open scoped BigOperators

/-- The three conclusions of the placement argument on the same graph.
Here P = 2^(176k), β is proportional to log P, and C depends only on the
fixed degree. Lengths are measured in a common positive scale a. -/
theorem padded_graph_geometry (price : PriceZero) {E : Type} [Fintype E] (k e : ℕ)
    (src dst : E → Fin (2^(176*k)))
    (degree : ∀ v, (Finset.univ.filter fun x => src x = v).card +
      (Finset.univ.filter fun x => dst x = v).card + 2^88 ≤ 2^e)
    (large : 10000*(e+3) ≤ 176*k)
    (gap : 2*(2:ℝ)^e/(2:ℝ)^88 ≤ (176*k:ℕ)/(10000*((e:ℝ)+3))) :
    let V := Fin (2^(176*k))
    let P : ℝ := Fintype.card V
    let β : ℝ := (176*k:ℕ)/(10000*((e:ℝ)+3))
    let C := 2*(2:ℝ)^e/(2:ℝ)^88
    ∃ (X : SpectralTarget) (p : V → X.carrier) (o : X.carrier) (a : ℝ), 0 < a ∧
      (𝔼 j, 𝔼 i, (normalizedDist a p i j)^2) = 1 ∧
      (∀ (w : E → ℝ) (cap : ℝ), 0 ≤ cap → (∀ edge, w edge ≤ cap) →
        ∑ edge, w edge*normalizedDist a p (src edge) (dst edge) ≤
          cap*Real.sqrt (Fintype.card E)*Real.sqrt ((2:ℝ)^e*P/β)) ∧
      (∀ N (A B : Fin N ↪ V), (∑ j, ∑ i, (normalizedDist a p (A i) (B j)-1)^2) ≤
        12*(N:ℝ)*P*(C/β)) ∧
      (∀ h : V → ℝ, (∀ v, 0 ≤ h v) →
        (∑ v, h v*(a*dist (p v) o)) ≤ (∑ v, h v)/Real.sqrt 2 +
          Real.sqrt (∑ v, (h v)^2)*Real.sqrt (P*(C/β))) := by
  intro V P β C
  have posβ : 0 < β := by
    have hk : 0 < 176*k := by omega
    exact div_pos (Nat.cast_pos.mpr hk) (by positivity)
  have posC : 0 < C := by dsimp [C]; positivity
  obtain ⟨H,contains,scalar,X,p,short⟩ := common_placement price k e large gap
    (supplyMultiplicity src dst) (supplyMultiplicity_symm src dst)
    (fun i => by rw [supplyMultiplicity_row]; exact degree i)
  let A := normalizeArcs H (2^e)
  have nonnegative (i j) : 0 ≤ A i j := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨a,apos,unit,small⟩ := normalize_placement p A posβ nonnegative short
  have var (f : V → ℝ) (hf : ∀ i j, |f i-f j| ≤ dist (p i) (p j)) :
      (𝔼 i, (a*f i - 𝔼 j, a*f j)^2) ≤ C/β :=
    (normalized_variance A nonnegative posC.le scalar p a f hf).trans
      (by rw [div_eq_mul_one_div C]; exact mul_le_mul_of_nonneg_left small.le posC.le)
  obtain ⟨o,center⟩ := normalized_center (hasCATZeroSegments_of_realizable _ X.fractions X.realizable)
    p apos unit var
  refine ⟨X,p,o,a,apos,unit,?_,fun N L R => normalized_terminals p apos (div_nonneg posC.le posβ.le)
    unit var L R,center⟩
  intro w cap hcap widths
  apply weighted_supply_cost w _ widths hcap (fun edge => mul_nonneg apos.le dist_nonneg)
  simp only [mul_pow, ← Finset.mul_sum]
  have edges := supply_energy_le p src dst H (show 0 < 2^e by positivity) contains
  have posP : 0 < P := Nat.cast_pos.mpr Fintype.card_pos
  have ratio := (div_lt_div_iff₀ posP posβ).mp small
  apply (le_div_iff₀ posβ).mpr
  push_cast at edges
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left edges (sq_nonneg a)) posβ.le,
    mul_le_mul_of_nonneg_left ratio.le (show 0 ≤ (2:ℝ)^e by positivity)]

end OAI.Computability.MultitapeWeakETH
