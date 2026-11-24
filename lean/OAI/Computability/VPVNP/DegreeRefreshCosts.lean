import OAI.Computability.VPVNP.DegreeRefreshConversion
import OAI.Computability.VPVNP.DegreeRefreshWidths

/-!
# Cost of each admitted expander-motif term

Apply the fixed block of Theorem 6.1 with unit mass on each internal tie
and mass `D / d₀` on each expander arc. A payload is admitted by its weighted
norm. Its wire carries both that payload and the common list of selectors.
The same padded widths are used in the actual slots for the energy bound and
the maximum-width bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.DegreeRefresh

open MotifBlocks MotifGrid MotifConversion

variable {D dH d₀ : ℕ} {k : Type*} [Field k]
variable {P : MotifSelector.Supply (Fin D) (Fin D × Fin dH)} {H H' : ℝ}

/-- Fixed motif block converting refresh tie wires into the specified supply on the port graph. -/
abbrev RefreshBlock (k : Type*) [Field k] (P : MotifSelector.Supply (Fin D) (Fin D × Fin dH))
    (d₀ : ℕ) (H H' : ℝ) :=
  FixedBlock k Refresh.tieSource Refresh.tieTarget P (realWidths Refresh.tieMass)
    (realWidths (Refresh.expanderMass d₀)) H H'

variable (F : RefreshBlock k P d₀ H H')

/-- Convert the executable admission condition on the outer payload into the
normalized termwise energy inequality needed in the refresh. -/
theorem termWidths_energy (hD : 0 < D) (hd₀ : 0 < d₀) (b : Tie D → ℕ)
    (v : Fin D × Fin dH → ℕ) (hadmit : v ∈ outerIndices F b) :
    (∑ e, (supplyWidths F b v e : ℝ) ^ 2 / ((D : ℝ) / d₀)) ≤
      H' * (∑ t, (b t : ℝ) ^ 2) + F.energyConstant := by
  have hp (t : Tie D) : 0 < Refresh.tieMass t := zero_lt_one
  have hq (e : Fin D × Fin dH) : 0 < Refresh.expanderMass d₀ e :=
    div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hd₀)
  have h := energy_le F hp hq b v hadmit
  rw [norm_sq (realWidths (Refresh.expanderMass d₀)) _ (fun e ↦ Rat.cast_pos.mpr (hq e)),
    norm_sq (realWidths Refresh.tieMass) _ (fun t ↦ Rat.cast_pos.mpr (hp t))] at h
  simpa only [realWidths, Refresh.tieMass, Refresh.expanderMass, Rat.cast_one, div_one,
    Rat.cast_div, Rat.cast_natCast] using h

/-- A surviving motif entry uses one scalar parameter per block repetition.
This number is bounded linearly in the maximum old width for a fixed port count. -/
theorem term_repetitions_le (b : Tie D → ℕ) {W : ℕ} (hw : ∀ t, b t ≤ W) :
    repetitions F b ≤ Fintype.card (Tie D) * W := by
  rw [repetitions_eq F (fun _ ↦ zero_lt_one)]
  unfold FixedBlock.repetitions MotifWidths.copies
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.mpr F.scale_pos)]
  have hN : widthNorm (realWidths Refresh.tieMass) (fun t ↦ (b t : ℝ)) ≤
      (Fintype.card (Tie D) : ℝ) * W := by
    unfold widthNorm
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simp only [realWidths, Refresh.tieMass, Rat.cast_one, div_one, mul_pow]
    have hs := Finset.sum_le_sum (s := Finset.univ) fun t _ ↦
      pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (b t)) (Nat.cast_le.mpr (hw t)) 2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_pow (by decide : 0 < 2) : (Fintype.card (Tie D) : ℝ) ≤ _)
      (sq_nonneg _))
  rw [Nat.cast_mul]
  exact hN.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast F.scale_pos))

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L]
  [AddCommGroup E] [AddCommGroup L]

/-- Equation (7.3) for each admitted collection of expander payloads,
with the selector bits included on every internal supply arc. -/
theorem admitted_actual_energy [Nonempty V] [Nonempty L] (G : LiftedSlots V D (E × L))
    (port : E ≃ Fin D) (hd : dH + 1 ≤ d₀) (hD : 0 < D) (hH' : 0 ≤ H')
    (w : (V × Fin D) × (E × L) → ℕ) (v : V × L → Fin D × Fin dH → ℕ)
    (hadmit : ∀ z, v z ∈ outerIndices F
      (tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w) z)) :
    let n := (Fintype.card (V × (E × L)) : ℝ)
    let b := tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w)
    let s := fun z ↦ supplyWidths F (b z) (v z)
    (∑ a, (actualWidths hd port w s a : ℝ) ^ 2 / (1 / (n * d₀))) ≤
      (d₀ + 2 * H') * (∑ a, (w a : ℝ) ^ 2 / (1 / (n * D))) + F.energyConstant * n ^ 2 := by
  exact actualWidths_energy_le G port hd hD w _ hH' fun z ↦
    termWidths_energy F hD (by omega) _ _ (hadmit z)

omit [Fintype V] [Fintype E] [Fintype L] in
/-- For every admitted collection of block choices the same bound on field
lengths works at all the actual slots, independently of the old graph and lanes. -/
theorem admitted_actual_width (G : LiftedSlots V D (E × L)) (port : E ≃ Fin D)
    (hd : dH + 1 ≤ d₀) (hD : 0 < D) (hH' : 0 ≤ H')
    (w : (V × Fin D) × (E × L) → ℕ) (v : V × L → Fin D × Fin dH → ℕ)
    (hadmit : ∀ z, v z ∈ outerIndices F
      (tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w) z)) {W : ℕ} (hw : ∀ a, w a ≤ W) (a : ((V × Fin D) × Fin d₀) × L) :
    let b := tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w)
    let s := fun z ↦ supplyWidths F (b z) (v z)
    (actualWidths hd port w s a : ℝ) ≤
      max (D : ℝ) (Real.sqrt (((D : ℝ) / d₀) *
        (H' * Fintype.card (Tie D) + max 0 F.energyConstant))) * (W + 1) := by
  apply newWidths_max_le hd hD (bundleTarget G) (bundlePort G port) _ _ hH' (le_max_left _ _)
    (fun z ↦ (termWidths_energy F hD (by omega) _ _ (hadmit z)).trans
      (add_le_add_right (le_max_right 0 F.energyConstant) _))
  exact fun _ _ ↦ hw _

end Compression.DegreeRefresh

namespace Compression.Refresh

open DegreeRefresh SpectralGeometry

variable {k : Type*} [Field k] {D dH d₀ : ℕ} {K K' : ℝ}
variable {V E L : Type} [Fintype V] [Fintype E] [Fintype L] [AddCommGroup E] [AddCommGroup L]
  (G : LiftedSlots V D (E × L)) (port : E ≃ Fin D) (w : (V × Fin D) × (E × L) → ℕ)
  (P : RegularArcGraph (Fin D) dH) (hdH : 0 < dH) (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) d₀ K K') (hD : 1 < D) (hd : dH + 1 ≤ d₀)

include hD

/-- Equation (7.3) for every branch of `expanderRefreshStep`. In the block
chosen by `exists_expander_parameters`, the coefficient `K'` equals
`2 * γ * d₀ / dH + 1`, so the leading coefficient is uniform over port counts. -/
theorem expander_branch_energy_le [Nonempty V] [Nonempty L] (hK' : 0 ≤ K')
    (c : BlockChoices G port w P hdH hconn F) :
    let n := (Fintype.card (V × (E × L)) : ℝ)
    (∑ a, (actualWidths hd port w (blockSupplyWidths G port w P hdH hconn F c) a : ℝ) ^ 2 /
      (1 / (n * d₀))) ≤
        (d₀ + 2 * K') * (∑ a, (w a : ℝ) ^ 2 / (1 / (n * D))) + F.energyConstant * n ^ 2 := by
  have ha (z : V × L) := (c z).property
  simp only [blockDemandWidths_eq] at ha
  have he : blockSupplyWidths G port w P hdH hconn F c = fun z ↦ MotifConversion.supplyWidths F
      (tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w) z) (c z).val := by
    funext z
    exact congrArg (fun b ↦ MotifConversion.supplyWidths F b (c z).val)
      (congrFun (blockDemandWidths_eq G port w) z)
  rw [he]
  exact
    admitted_actual_energy F G port hd (by omega) hK' w (fun z ↦ (c z).val) ha

omit [Fintype V] [Fintype E] [Fintype L] in
/-- All external, internal and padding widths in an admitted branch of
`expanderRefreshStep` obey the same linear bound in the largest old field. -/
theorem expander_branch_width_le (hK' : 0 ≤ K') (c : BlockChoices G port w P hdH hconn F)
    {W : ℕ} (hw : ∀ a, w a ≤ W) (a : ((V × Fin D) × Fin d₀) × L) :
    (actualWidths hd port w (blockSupplyWidths G port w P hdH hconn F c) a : ℝ) ≤
      max (D : ℝ) (Real.sqrt (((D : ℝ) / d₀) *
        (K' * Fintype.card (Tie D) + max 0 F.energyConstant))) * (W + 1) := by
  have ha (z : V × L) := (c z).property
  simp only [blockDemandWidths_eq] at ha
  have he : blockSupplyWidths G port w P hdH hconn F c = fun z ↦ MotifConversion.supplyWidths F
      (tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w) z) (c z).val := by
    funext z
    exact congrArg (fun b ↦ MotifConversion.supplyWidths F b (c z).val)
      (congrFun (blockDemandWidths_eq G port w) z)
  rw [he]
  exact
    admitted_actual_width F G port hd (by omega) hK' w (fun z ↦ (c z).val) ha hw a

end Compression.Refresh

end VPVNP
end Computability
end OAI
