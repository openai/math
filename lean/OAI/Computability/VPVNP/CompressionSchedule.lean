import OAI.Computability.VPVNP.WireExpanders
import OAI.Computability.VPVNP.DegreeRefreshSupply
import OAI.Computability.VPVNP.PackedShrinkStep
import OAI.Computability.VPVNP.PackingLanes

/-!
# Choosing one fixed compression block

Section 7.4 chooses the number of shrinking steps before their output
degrees. The refresh multiplier depends only on the common expander bound,
the expander degree and the fixed initial degree. Each subsequent power of
two can therefore be chosen large enough to represent the four supply masses,
and the last one can be an order of the common expander family.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open SpectralGeometry

/-- An admissible strict version of the six-party squared-distance bound. -/
noncomputable def shrinkComparison : ℝ := 63 / 32

/-- The relative mass lost in replacing real weights by integral slots. -/
noncomputable def shrinkLoss : ℝ := 1 / 128

/-- Leading energy factor of a shrinking step with the chosen constants. -/
noncomputable def shrinkMultiplier : ℝ := shrinkComparison / (2 * (1 - shrinkLoss))

theorem shrink_constants :
    (31 / 16 : ℝ) < shrinkComparison ∧ 0 < shrinkLoss ∧ shrinkLoss < 1 ∧
      shrinkComparison < 2 * (1 - shrinkLoss) ∧
      shrinkMultiplier = 126 / 127 ∧ 0 < shrinkMultiplier ∧ shrinkMultiplier < 1 := by
  norm_num [shrinkComparison, shrinkLoss, shrinkMultiplier]

/-- The exact position-count ratio in the dyadic packing at degree `2^a`. -/
def packingFactor (a : ℕ) : ℕ := 2 ^ (2 * 2 ^ a + 1) * 2 ^ a

theorem two_lt_packingFactor (a : ℕ) : 2 < packingFactor a := by
  have h₁ := Nat.two_pow_pos a
  have h₂ : 2 ≤ 2 * 2 ^ a + 1 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h₂
  exact (show 2 < 2 ^ (2 * 2 ^ a + 1) by omega).trans_le
    (Nat.le_mul_of_pos_right _ h₁)

/-- A transition between exponents meets the mass and slot capacity bounds
of the actual regularized shrinking step. -/
abbrev AllowsShrink (a a' : ℕ) : Prop :=
  ShrinkMotif.Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ a') shrinkLoss

private theorem eventually_allowsShrink (a : ℕ) :
    ∃ N : ℕ, ∀ a' : ℕ, N ≤ 2 ^ a' → AllowsShrink a a' := by
  have hd := Nat.two_pow_pos a
  obtain ⟨N, hN⟩ := ShrinkMotif.eventually_ready _ _ hd
    (show 2 ≤ 2 * 2 ^ a + 1 by omega) shrink_constants.2.1 shrink_constants.2.2.1
  exact ⟨N, fun a' hn ↦ hN (2 ^ a') hn⟩

/-- The leading refresh factor (7.3), independent of the port count. -/
noncomputable def refreshMultiplier (d₀ dH : ℕ) (γ : ℝ) : ℝ :=
  d₀ + 2 * (2 * γ * d₀ / dH + 1)

/-- A fixed block of shrinking degrees followed by an expander refresh. -/
structure BlockSchedule (k : Type*) [Field k] where
  /-- Binary logarithm of the common expander degree used in the final refresh. -/
  expanderExponent : ℕ
  /-- Uniform Poincaré bound required of the port graph at the end of the block. -/
  poincare : ℝ
  poincare_pos : 0 < poincare
  /-- Number of shrinking substeps before the degree refresh. -/
  steps : ℕ
  steps_pos : 0 < steps
  /-- Base-two degree exponent at each boundary of the shrinking sequence, including its
  initial and final boundaries. -/
  degreeExponent : Fin (steps + 1) → ℕ
  initial : degreeExponent 0 = expanderExponent + 1
  shrink : ∀ i : Fin steps, AllowsShrink (degreeExponent i.castSucc) (degreeExponent i.succ)
  port_order : 2 ≤ 2 ^ degreeExponent (Fin.last steps)
  /-- Regular port graph on the final shrinking degree's ports, with degree fixed by
  `expanderExponent`. -/
  graph : RegularArcGraph (Fin (2 ^ degreeExponent (Fin.last steps))) (2 ^ expanderExponent)
  port_bound : Refresh.SpectralPortBound k graph poincare
  quarter : refreshMultiplier (2 ^ degreeExponent 0) (2 ^ expanderExponent) poincare *
    shrinkMultiplier ^ steps ≤ 1 / 4

variable {k : Type*} [Field k]

/-- All the constants and the graph in the schedule are selected before
the network, its lane count, and its widths. -/
theorem exists_blockSchedule (h : HasWireExpanders k) : Nonempty (BlockSchedule k) := by
  classical
  obtain ⟨e, γ, hγ, graphs⟩ := h
  let a₀ := e + 1
  let C := refreshMultiplier (2 ^ a₀) (2 ^ e) γ
  have hC : 0 < C := by unfold C refreshMultiplier; positivity
  obtain ⟨_, _, _, _, _, hρ, hρlt⟩ := shrink_constants
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 1 / (4 * C)) hρlt
  let steps := n + 1
  have hquarter : C * shrinkMultiplier ^ steps ≤ 1 / 4 := by
    have hmono : shrinkMultiplier ^ steps ≤ shrinkMultiplier ^ n :=
      pow_le_pow_of_le_one hρ.le hρlt.le (by omega)
    have hscaled := (lt_div_iff₀ (by positivity : 0 < 4 * C)).mp (hmono.trans_lt hn)
    linarith
  choose threshold hthreshold using eventually_allowsShrink
  choose nextOrder hOrder hexp using fun a : ℕ ↦ graphs (max 2 (threshold a))
  let degree : ℕ → ℕ := Nat.rec (motive := fun _ ↦ ℕ) a₀ (fun _ a ↦ nextOrder a)
  have hg := hexp (degree n)
  obtain ⟨G, _, hG⟩ := hg
  refine ⟨⟨e, γ, hγ, steps, Nat.succ_pos _, fun i ↦ degree i.val, rfl,
    fun i ↦ hthreshold _ _ ((le_max_right _ _).trans (hOrder _)), ?_, G,
    fun F ↦ hG _ F, hquarter⟩⟩
  exact (le_max_left _ _).trans (hOrder _)

namespace BlockSchedule

variable (S : BlockSchedule k)

/-- Initial and final restored degree. -/
def baseDegree : ℕ := 2 ^ S.degreeExponent 0

/-- Number of lane bits consumed by the whole block, including the port index. -/
def laneBits : ℕ := (∑ i : Fin S.steps, packingLaneBits (S.degreeExponent i.castSucc) 0) +
  S.degreeExponent (Fin.last S.steps)

/-- Number of old positions per final position; refresh keeps all the positions. -/
def positionFactor : ℕ := ∏ i : Fin S.steps, packingFactor (S.degreeExponent i.castSucc)

theorem degree_bounds : 2 ≤ S.baseDegree ∧ 2 ^ S.expanderExponent + 1 ≤ S.baseDegree := by
  have h := Nat.two_pow_pos S.expanderExponent
  rw [baseDegree, S.initial, pow_succ]
  omega

theorem laneBits_pos : 0 < S.laneBits := by
  have h : 0 < S.degreeExponent (Fin.last S.steps) := by
    by_contra! hn
    have hD := S.port_order
    simp [Nat.eq_zero_of_le_zero hn] at hD
  exact Nat.add_pos_right _ h

theorem positionFactor_gt_two : 2 < S.positionFactor := by
  let i : Fin S.steps := ⟨0, S.steps_pos⟩
  apply (two_lt_packingFactor (S.degreeExponent i.castSucc)).trans_le
  exact Finset.single_le_prod (fun j _ ↦ (two_lt_packingFactor (S.degreeExponent j.castSucc)).le.trans'
    (by decide : 1 ≤ 2)) (Finset.mem_univ i)

/-- The scheduled exponent at an index, with later indices held at the
last exponent. This permits sums over ordinary half-open index ranges. -/
def exponentAt (i : ℕ) : ℕ := S.degreeExponent ⟨min i S.steps, by omega⟩

theorem exponentAt_castSucc (i : Fin S.steps) :
    S.exponentAt i.val = S.degreeExponent i.castSucc := by
  simp only [exponentAt, min_eq_left i.isLt.le]
  rfl

/-- Lane coordinates required by the suffix starting at shrink `i`.
Extra unused coordinates can be appended to every suffix. -/
def remainingBits (i : ℕ) : ℕ :=
  (∑ j ∈ Finset.Ico i S.steps, packingLaneBits (S.exponentAt j) 0) +
    S.degreeExponent (Fin.last S.steps)

theorem remainingBits_zero : S.remainingBits 0 = S.laneBits := by
  rw [remainingBits, laneBits, ← Finset.range_eq_Ico,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ packingLaneBits (S.exponentAt j) 0)]
  simp only [exponentAt_castSucc]

theorem remainingBits_step (i : Fin S.steps) (extra : ℕ) :
    S.remainingBits i.val + extra =
      packingLaneBits (S.degreeExponent i.castSucc) (S.remainingBits (i.val + 1) + extra) := by
  rw [remainingBits, Finset.sum_eq_sum_Ico_succ_bot i.isLt, S.exponentAt_castSucc]
  simp [remainingBits, packingLaneBits, Nat.add_assoc]

theorem remainingBits_last : S.remainingBits S.steps = S.degreeExponent (Fin.last S.steps) := by
  simp [remainingBits]

end BlockSchedule
end Compression

end VPVNP
end Computability
end OAI
