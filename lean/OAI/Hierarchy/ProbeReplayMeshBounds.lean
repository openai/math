import OAI.Hierarchy.ProbePublicTimes

namespace OAI
/-! # One reserve mesh and one repair fuel for every later population and payload width -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

/-- Fix the reserve mesh before the input length and word width. After the common
minimum width, both the actual integer feed error and all quadratic Taylor errors
sum to at most one eighth of the frozen purchase reward throughout cooling. -/
theorem reserve_mesh_bounds (D U s₀ a ρ reward : ℝ) (cap : ℕ) (hD : 0≤D) (hU : 0≤U)
    (hs : 0<s₀) (ha : 0<a) (hρ : 0<ρ) (hw : 0<reward) :
    ∃ m floor : ℕ, 0 < m ∧ m≤floor ∧ ∀ w≥floor, ∀ s≥s₀, ∀ n coords : ℕ,
    (coords:ℝ)≤D*n → (m:ℝ)*((coords:ℝ)*(2*U/w+(((cap:ℝ)+2+cap)/m)^2/(2*s*a))) ≤ (n:ℝ)*ρ*reward/8 := by
  let tol := ρ*reward/16
  let R := (cap:ℝ)+2+cap
  let T := D*R^2/(2*s₀*a)
  have ht : 0<tol := by dsimp [tol]; positivity
  obtain ⟨m,hmesh⟩ := exists_nat_gt (max 0 (T/tol))
  have mp : 0<(m:ℝ) := (le_max_left ..).trans_lt hmesh
  have mNat : 0 < m := Nat.cast_pos.mp mp
  have budget : T≤tol*m := by
    have bound := (div_lt_iff₀ ht).mp ((le_max_right ..).trans_lt hmesh)
    linarith
  obtain ⟨f,hfloor⟩ := exists_nat_gt (2*m*D*U/tol)
  refine ⟨m,max m f,mNat,le_max_left ..,?_⟩
  intro w large s later n coords dimension
  have f_le : f≤w := (le_max_right ..).trans large
  have wp : 0<(w:ℝ) := Nat.cast_pos.mpr (mNat.trans_le ((le_max_left ..).trans large))
  have sp := hs.trans_le later
  have one : 2*m*D*U/w≤tol := by
    apply (div_le_iff₀ wp).2
    have fReal : (f:ℝ)≤w := by exact_mod_cast f_le
    have bound := (div_lt_iff₀ ht).mp (hfloor.trans_le fReal)
    linarith
  have den : 2*s₀*a≤2*s*a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left later (by norm_num)) ha.le
  have two : D*R^2/(2*s*a)/m≤tol := by
    apply (div_le_iff₀ mp).2
    exact (div_le_div_of_nonneg_left (mul_nonneg hD (sq_nonneg R)) (by positivity) den).trans budget
  let piece := 2*U/w+(R/m)^2/(2*s*a)
  have piece_nn : 0≤piece := by dsimp [piece]; positivity
  have total : (m:ℝ)*(D*piece)≤2*tol := calc
    _ = 2*m*D*U/w + D*R^2/(2*s*a)/m := by dsimp [piece]; field_simp
    _ ≤ _ := by linarith
  change (m:ℝ)*(coords*piece)≤_
  calc (m:ℝ)*(coords*piece) ≤ m*((D*n)*piece) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right dimension piece_nn) mp.le
       _ = n*(m*(D*piece)) := by ring
       _ ≤ n*(2*tol) := mul_le_mul_of_nonneg_left total (Nat.cast_nonneg _)
       _ = _ := by dsimp [tol]; ring

/-- A full slice of unsuccessful native corrections pays the original flat fee,
the worst remaining reserve, and a strict eighth of the same purchase reward. -/
theorem reserve_repair_fuel (fee dimension U ρ γ ρBuy reward : ℝ) (K cap : ℕ)
    (hρ : 0<ρ) (hγ : 0<γ) (hK : 0<K) :
    ∃ fuel : ℕ, 0<fuel ∧ fee+dimension*cap*U+ρBuy*reward/8≤(fuel:ℝ)*(ρ*γ/(8*K)) := by
  let gain := ρ*γ/(8*K)
  have pos : 0<gain := by dsimp [gain]; positivity
  obtain ⟨n,more⟩ := exists_nat_gt (max 0 ((fee+dimension*cap*U+ρBuy*reward/8)/gain))
  exact ⟨n,Nat.cast_pos.mp ((le_max_left ..).trans_lt more),
    ((div_lt_iff₀ pos).mp ((le_max_right ..).trans_lt more)).le⟩

end
end Hierarchy.AdaptiveProbe

end OAI
