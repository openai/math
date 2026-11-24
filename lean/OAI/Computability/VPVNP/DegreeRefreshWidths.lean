import OAI.Computability.VPVNP.DegreeRefresh
import OAI.Computability.VPVNP.DegreeRefreshTopology

/-!
# Widths on the refreshed slots

Each port has one concatenated external field, one field per internal expander
arc, and zero bits on every padding arc. This module charges the resulting
actual slots in the paper's normalization and derives the bound (7.3) from
the internal motif's bound with masses divided by the old arc mass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.DegreeRefresh

variable {B : Type*} [Fintype B] {D dH d₀ : ℕ}

/-- Widths of the external, internal and padding slots, respectively. -/
def newWidths (hd : dH + 1 ≤ d₀) (w : Widths B D) (s : B → Fin D × Fin dH → ℕ)
    (u : B × Fin D) (k : Fin d₀) : ℕ :=
  match (refreshSlots hd).symm k with
  | .inl _ => ∑ j, w u j
  | .inr (.inl h) => s u.1 (u.2,h)
  | .inr (.inr _) => 0

/-- Energy of the expander slots in a single block. -/
noncomputable def internalEnergy (p' : ℝ) (s : Fin D × Fin dH → ℕ) : ℝ :=
  ∑ e, (s e : ℝ) ^ 2 / p'

theorem newWidths_energy (hd : dH + 1 ≤ d₀) (w : Widths B D) (s : B → Fin D × Fin dH → ℕ)
    (p' : ℝ) :
    (∑ u, ∑ k, (newWidths hd w s u k : ℝ) ^ 2 / p') =
      externalEnergy p' w + ∑ z, internalEnergy p' (s z) := by
  have localEnergy (u : B × Fin D) :
      (∑ k, (newWidths hd w s u k : ℝ) ^ 2 / p') =
        ((∑ j, w u j : ℕ) : ℝ) ^ 2 / p' + ∑ h, (s u.1 (u.2,h) : ℝ) ^ 2 / p' := by
    rw [← (refreshSlots hd).sum_comp (fun k ↦ (newWidths hd w s u k : ℝ) ^ 2 / p')]
    simp [Fintype.sum_sum_type, newWidths]
  simp only [localEnergy, Finset.sum_add_distrib, internalEnergy, externalEnergy, Fintype.sum_prod_type]

omit [Fintype B] in
/-- The internal motif inequality uses demand mass one and supply mass
`D / d₀`. Multiplying by the reciprocal old arc mass restores the actual
energies used in the network. -/
theorem internalEnergy_of_motif (target : Equiv.Perm (B × Fin D))
    (lane : B × Fin D → Equiv.Perm (Fin D)) (w : Widths B D) (s : Fin D × Fin dH → ℕ) (z : B)
    {H' C p p' : ℝ} (hp : 0 < p) (hd₀ : 0 < d₀)
    (hmass : (D : ℝ) * p = d₀ * p')
    (hterm : (∑ e, (s e : ℝ) ^ 2 / ((D : ℝ) / d₀)) ≤
      H' * (∑ t : Tie D, (tieWidth target lane w z t : ℝ) ^ 2) + C) :
    internalEnergy p' s ≤ H' * demandEnergy p target lane w z + C / p := by
  have hd₀' : 0 < (d₀ : ℝ) := Nat.cast_pos.mpr hd₀
  have heq : (D : ℝ) / d₀ * p = p' := by
    rw [div_mul_eq_mul_div, div_eq_iff hd₀'.ne', mul_comm p']
    exact hmass
  have h := div_le_div_of_nonneg_right hterm hp.le
  simp only [div_eq_mul_inv, Finset.sum_mul, add_mul, mul_assoc] at h
  simp only [internalEnergy, demandEnergy, div_eq_mul_inv, Finset.mul_sum]
  have hscale : (↑D * (↑d₀ : ℝ)⁻¹)⁻¹ * p⁻¹ = p'⁻¹ := by
    rw [← mul_inv, ← heq, div_eq_mul_inv]
  simpa only [hscale, Finset.mul_sum, mul_assoc] using h

/-- The network estimate (7.3) for the actual refreshed widths, including
the zero-width padding slots. `B` indexes blocks of `D` ports. The leading
coefficient is independent of `D` whenever the chosen motif coefficient is. -/
theorem newWidths_energy_le [Nonempty B] (hd : dH + 1 ≤ d₀) (hD : 0 < D)
    (target : Equiv.Perm (B × Fin D)) (lane : B × Fin D → Equiv.Perm (Fin D))
    (w : Widths B D) (s : B → Fin D × Fin dH → ℕ) {H' C : ℝ} (hH : 0 ≤ H')
    (hterm : ∀ z, (∑ e, (s z e : ℝ) ^ 2 / ((D : ℝ) / d₀)) ≤
      H' * (∑ t : Tie D, (tieWidth target lane w z t : ℝ) ^ 2) + C) :
    let P := (Fintype.card B : ℝ) * D
    (∑ u, ∑ k, (newWidths hd w s u k : ℝ) ^ 2 / (1 / (P * d₀))) ≤
      (d₀ + 2 * H') * oldEnergy (1 / (P * D)) w + C * P ^ 2 := by
  let P := (Fintype.card B : ℝ) * D
  let p := 1 / (P * D)
  let p' := 1 / (P * d₀)
  have hd₀ : 0 < d₀ := by omega
  have hD' : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hd₀' : 0 < (d₀ : ℝ) := Nat.cast_pos.mpr hd₀
  have hB : 0 < (Fintype.card B : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hP : 0 < P := mul_pos hB hD'
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : 0 < p' := by dsimp [p']; positivity
  have hm : (D : ℝ) * p = d₀ * p' := by dsimp [p,p']; field_simp
  have ho : 1 / p = (Fintype.card B : ℝ) * D * D := by simp [p,P]
  dsimp only
  rw [newWidths_energy]
  exact refresh_energy_le target lane w (fun z ↦ internalEnergy p' (s z)) hp hp' hH hm ho
    (fun z ↦ internalEnergy_of_motif target lane w _ z hp hd₀ hm (hterm z))

omit [Fintype B] in
/-- For fixed degrees and motif coefficients, every new slot has width
bounded by a constant times one plus the maximum old width. The same bound
applies to the concatenated fields read by the external segment ties. -/
theorem newWidths_max_le (hd : dH + 1 ≤ d₀) (hD : 0 < D)
    (target : Equiv.Perm (B × Fin D)) (lane : B × Fin D → Equiv.Perm (Fin D))
    (w : Widths B D) (s : B → Fin D × Fin dH → ℕ) {H' C : ℝ} (hH : 0 ≤ H') (hC : 0 ≤ C)
    (hterm : ∀ z, (∑ e, (s z e : ℝ) ^ 2 / ((D : ℝ) / d₀)) ≤
      H' * (∑ t : Tie D, (tieWidth target lane w z t : ℝ) ^ 2) + C)
    {W : ℕ} (hw : ∀ e i, w e i ≤ W) (u : B × Fin D) (k : Fin d₀) :
    (newWidths hd w s u k : ℝ) ≤
      max (D : ℝ) (Real.sqrt (((D : ℝ) / d₀) * (H' * Fintype.card (Tie D) + C))) * (W + 1) := by
  let q := (D : ℝ) / d₀
  have hq : 0 < q := div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr (by omega))
  let A := q * (H' * Fintype.card (Tie D) + C)
  have hA : 0 ≤ A := mul_nonneg hq.le (add_nonneg (mul_nonneg hH (Nat.cast_nonneg _)) hC)
  have hW : 0 ≤ (W : ℝ) + 1 := by positivity
  obtain ⟨i | h | j,rfl⟩ := (refreshSlots hd).surjective k
  · simp only [newWidths, Equiv.symm_apply_apply, Nat.cast_sum]
    have hx : (∑ j : Fin D, (w u j : ℝ)) ≤ ∑ _ : Fin D, ((W : ℝ) + 1) :=
      Finset.sum_le_sum fun j _ ↦ (Nat.cast_le.mpr (hw u j)).trans (le_add_of_nonneg_right zero_le_one)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW)
  · simp only [newWidths, Equiv.symm_apply_apply]
    have ht (t : Tie D) : tieWidth target lane w u.1 t ≤ W := by
      unfold tieWidth incoming
      split_ifs <;> exact hw _ _
    have htSum : (∑ t : Tie D, (tieWidth target lane w u.1 t : ℝ) ^ 2) ≤
        (Fintype.card (Tie D) : ℝ) * ((W : ℝ) + 1) ^ 2 := by
      have hsum := Finset.sum_le_sum (s := Finset.univ) fun t _ ↦
        pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (tieWidth target lane w u.1 t))
          ((Nat.cast_le.mpr (ht t)).trans (le_add_of_nonneg_right zero_le_one)) 2
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
    have hsum := Finset.single_le_sum (s := Finset.univ) (fun (i : Fin D × Fin dH) _ ↦
      div_nonneg (sq_nonneg (s u.1 i : ℝ)) hq.le) (Finset.mem_univ (u.2,h))
    have hsmall := (div_le_iff₀ hq).mp (hsum.trans (hterm u.1))
    have hC' := le_mul_of_one_le_right hC (one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) W]
      : 1 ≤ (W : ℝ) + 1) (n := 2))
    have hscale := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left htSum hH) hC') hq.le
    have hs : (s u.1 (u.2,h) : ℝ) ≤ √A * (W + 1) := by
      apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hW)).mp
      rw [mul_pow, Real.sq_sqrt hA]
      exact hsmall.trans (hscale.trans_eq (by unfold A; ring))
    exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hW)
  · simp only [newWidths, Equiv.symm_apply_apply, Nat.cast_zero]
    exact mul_nonneg ((Nat.cast_nonneg D).trans (le_max_left _ _)) hW

section ActualSlots

variable {V H L : Type*}

/-- Present the actual old width profile in the source order of each bundle. -/
def bundleWidths (port : H ≃ Fin D) (w : (V × Fin D) × (H × L) → ℕ) : Widths (V × L) D :=
  fun b j ↦ w ((bundleCoordinates port).symm (b,j))

/-- Group actual refreshed slots by their block and port, followed by their
outgoing slot number. -/
def refreshedCoordinates : (((V × Fin D) × Fin d₀) × L) ≃ (((V × L) × Fin D) × Fin d₀) where
  toFun p := (((p.1.1.1,p.2),p.1.1.2),p.1.2)
  invFun p := (((p.1.1.1,p.1.2),p.2),p.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The profile assigned to the actual slots of the new lifted topology. -/
def actualWidths (hd : dH + 1 ≤ d₀) (port : H ≃ Fin D) (w : (V × Fin D) × (H × L) → ℕ)
    (s : (V × L) → Fin D × Fin dH → ℕ) (a : ((V × Fin D) × Fin d₀) × L) : ℕ :=
  newWidths hd (bundleWidths port w) s (refreshedCoordinates a).1 (refreshedCoordinates a).2

variable [Fintype V] [Fintype H] [Fintype L]

private theorem bundleWidths_energy (port : H ≃ Fin D) (w : (V × Fin D) × (H × L) → ℕ) (p : ℝ) :
    oldEnergy p (bundleWidths port w) = ∑ a, (w a : ℝ) ^ 2 / p := by
  unfold oldEnergy
  rw [← Fintype.sum_prod_type']
  exact (bundleCoordinates port).symm.sum_comp (fun a ↦ (w a : ℝ) ^ 2 / p)

/-- Equation (7.3) in the original and refreshed actual-arc coordinates. The
two half-wire ties use the old graph's residual-lane shift and its port shift,
so all widths may vary with the lane. -/
theorem actualWidths_energy_le [Nonempty V] [Nonempty L] [AddCommGroup H] [AddCommGroup L]
    (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D) (hd : dH + 1 ≤ d₀) (hD : 0 < D)
    (w : (V × Fin D) × (H × L) → ℕ) (s : (V × L) → Fin D × Fin dH → ℕ)
    {H' C : ℝ} (hH : 0 ≤ H')
    (hterm : ∀ z, (∑ e, (s z e : ℝ) ^ 2 / ((D : ℝ) / d₀)) ≤
      H' * (∑ t : Tie D, (tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w) z t : ℝ) ^ 2) + C) :
    let P := (Fintype.card (V × (H × L)) : ℝ)
    (∑ a, (actualWidths hd port w s a : ℝ) ^ 2 / (1 / (P * d₀))) ≤
      (d₀ + 2 * H') * (∑ a, (w a : ℝ) ^ 2 / (1 / (P * D))) + C * P ^ 2 := by
  have hcard : Fintype.card (V × (H × L)) = Fintype.card (V × L) * D := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_congr port, Fintype.card_fin, Fintype.card_prod]
    ring
  dsimp only
  rw [hcard, Nat.cast_mul]
  have hh := newWidths_energy_le hd hD (bundleTarget G) (bundlePort G port) (bundleWidths port w) s hH hterm
  dsimp only at hh
  rw [bundleWidths_energy] at hh
  apply le_trans (le_of_eq ?_) hh
  rw [← Fintype.sum_prod_type']
  exact refreshedCoordinates.sum_comp (fun u ↦
    (newWidths hd (bundleWidths port w) s u.1 u.2 : ℝ) ^ 2 /
      (1 / ((Fintype.card (V × L) : ℝ) * D * d₀)))

end ActualSlots

end Compression.DegreeRefresh

end VPVNP
end Computability
end OAI
