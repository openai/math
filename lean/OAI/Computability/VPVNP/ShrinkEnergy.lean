import OAI.Computability.VPVNP.SlotDemandEnergy
import OAI.Computability.VPVNP.SurvivingSlots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Energy of the surviving wires in a shrinking step

Section 7.2 of *VP and VNP differ over every field* applies the six-party
identity separately at each motif, then chooses one layout for the entire
list of terms. The chosen layout retains at most half the total supply
energy. Subdivision into the graph's integral slots incurs the multiplicative
mass loss and a rounding error of at most one quarter per slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkEnergy

open SurvivingSlots

variable {M T : Type*} [Fintype M] [Fintype T]

/-- Energy in one of the two surviving supply groups, at actual mass `p*q`. -/
noncomputable def groupEnergy (p : ℝ) (q : T → ℝ) (w : M → Bool → T → ℕ) (layout : Bool) : ℝ :=
  ∑ m, ∑ e, (w m layout e : ℝ) ^ 2 / (p * q e)

/-- One deterministic choice of layout for the whole list. Equal costs retain
BC, BN, CN and DM (`false` in `SurvivingSlots`). -/
noncomputable def chosenLayout (p : ℝ) (q : T → ℝ) (w : M → Bool → T → ℕ) : Bool :=
  if groupEnergy p q w false ≤ groupEnergy p q w true then false else true

/-- Actual widths on the subdivided genuine arc IDs. -/
def slotWidth (m : T → ℕ) (w : M → Bool → T → ℕ) (layout : Bool) (i : Id M m) : ℕ :=
  splitWidth (w i.2.1 layout i.1) (m i.1) i.2.2

theorem chosen_half (p : ℝ) (q : T → ℝ) (w : M → Bool → T → ℕ) :
    2 * groupEnergy p q w (chosenLayout p q w) ≤
      groupEnergy p q w false + groupEnergy p q w true := by
  unfold chosenLayout
  split_ifs <;> linarith

/-- Scaling the relative masses of Lemma 6.2 by `p` also scales the
additive energy allowance per motif by `1/p`. -/
theorem group_sum_le (w : M → Bool → T → ℕ) (ab cd : M → ℕ) (q : T → ℝ)
    {p H C : ℝ} (hp : 0 < p) (hterm : ∀ m,
      (∑ l : Bool, ∑ e, (w m l e : ℝ) ^ 2 / q e) ≤ H * (3 * (ab m : ℝ) ^ 2 + (cd m : ℝ) ^ 2) + C) :
    groupEnergy p q w false + groupEnergy p q w true ≤
      H * (∑ m, ((ab m : ℝ) ^ 2 / (p / 3) + (cd m : ℝ) ^ 2 / p)) + Fintype.card M * C / p := by
  have hs (m : M) : (∑ e, (w m false e : ℝ) ^ 2 / (p * q e)) +
      (∑ e, (w m true e : ℝ) ^ 2 / (p * q e)) ≤
      H * ((ab m : ℝ) ^ 2 / (p / 3) + (cd m : ℝ) ^ 2 / p) + C / p := by
    have hh := div_le_div_of_nonneg_right (hterm m) hp.le
    rw [Fintype.sum_bool, add_div, Finset.sum_div, Finset.sum_div] at hh
    convert hh using 1
    · simp only [div_div, mul_comm p, add_comm]
    · rw [div_div_eq_mul_div]; ring
  unfold groupEnergy
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_le_sum (fun m _ ↦ hs m)).trans_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_div_assoc]

/-- Summed rounding cost after choosing a layout, including every parallel slot. -/
theorem parallel_energy_le (w : M → Bool → T → ℕ) (q : T → ℝ) (m : T → ℕ) (layout : Bool)
    {p p' α : ℝ} (hp : 0 < p) (hp' : 0 < p') (hα : 0 < α) (hq : ∀ e, 0 < q e)
    (hm : ∀ e, 0 < m e) (hmass : ∀ e, α * p * q e ≤ (m e : ℝ) * p') :
    (∑ i : Id M m, (slotWidth m w layout i : ℝ) ^ 2 / p') ≤
      groupEnergy p q w layout / α + Fintype.card M * (∑ e, (m e : ℝ)) / (4 * p') := by
  have one (v : M) (e : T) : (∑ i : Fin (m e), (splitWidth (w v layout e) (m e) i : ℝ) ^ 2 / p') ≤
      (w v layout e : ℝ) ^ 2 / (p * q e) / α + (m e : ℝ) / (4 * p') := by
    apply (splitWidth_energy_le _ _ (hm e) p' hp').trans
    apply add_le_add_left
    rw [div_div, mul_comm (p * q e), ← mul_assoc]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (mul_pos hα hp) (hq e)) (hmass e)
  unfold groupEnergy slotWidth
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum (fun v _ ↦ Finset.sum_le_sum (fun e _ ↦ one v e))).trans_eq ?_
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_div]
  simp [mul_div_assoc]

/-- Substitute each six-party identity, choose the smaller layout, and
regularize the surviving widths. The displayed errors account separately
for splitting the thick bundle, selecting a motif term, and rounding slots. -/
theorem shrinking_step_le (w : M → Bool → T → ℕ) (ab cd : M → ℕ) (q : T → ℝ) (m : T → ℕ)
    {p p' α H C L B : ℝ} (hp : 0 < p) (hp' : 0 < p') (hα : 0 < α) (hH : 0 ≤ H)
    (hq : ∀ e, 0 < q e) (hm : ∀ e, 0 < m e) (hmass : ∀ e, α * p * q e ≤ (m e : ℝ) * p')
    (hdemand : (∑ i, ((ab i : ℝ) ^ 2 / (p / 3) + (cd i : ℝ) ^ 2 / p)) ≤ L + B)
    (hterm : ∀ v, (∑ l : Bool, ∑ e, (w v l e : ℝ) ^ 2 / q e) ≤
      H * (3 * (ab v : ℝ) ^ 2 + (cd v : ℝ) ^ 2) + C) :
    (∑ i : Id M m, (slotWidth m w (chosenLayout p q w) i : ℝ) ^ 2 / p') ≤
      (H / (2 * α)) * L + (H * B + Fintype.card M * C / p) / (2 * α) +
        Fintype.card M * (∑ e, (m e : ℝ)) / (4 * p') := by
  apply (parallel_energy_le w q m _ hp hp' hα hq hm hmass).trans
  apply add_le_add_left
  have h := (chosen_half p q w).trans (group_sum_le w ab cd q hp hterm)
  have h' := h.trans (add_le_add_left (mul_le_mul_of_nonneg_left hdemand hH) _)
  have h₂ : (0 : ℝ) < 2 * α := by positivity
  rw [show H / (2 * α) * L + (H * B + Fintype.card M * C / p) / (2 * α) =
    (H * (L + B) + Fintype.card M * C / p) / (2 * α) by ring]
  apply (le_div_iff₀ h₂).mpr
  simpa [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, hα.ne'] using h'

/-- A common quadratic error coefficient for all position counts, widths and
term lists at the fixed old and new degrees. `Q` is the number of AB pieces. -/
noncomputable def roundingConstant (d d' Q : ℕ) (H C α : ℝ) (m : T → ℕ) : ℝ :=
  ((H * (Q : ℝ) * (3 / 4) + max C 0) * (d : ℝ) ^ 2) / (2 * α) +
    ((d : ℝ) * d' * ∑ e, (m e : ℝ)) / 4

private theorem errors_quadratic (d d' Q : ℕ) (H C α : ℝ) (m : T → ℕ)
    (n sites bundles motifs : ℕ) (hsites : sites ≤ n) (hbundles : bundles ≤ n * d)
    (hmotifs : motifs ≤ n * d) (hH : 0 ≤ H) (hα : 0 < α) :
    let p := (1 : ℝ) / ((n : ℝ) * d)
    let p' := (1 : ℝ) / ((sites : ℝ) * d')
    (H * (bundles * (Q : ℝ) / (4 * (p / 3))) + motifs * C / p) / (2 * α) +
      motifs * (∑ e, (m e : ℝ)) / (4 * p') ≤ roundingConstant d d' Q H C α m * n ^ 2 := by
  intro p p'
  have hB : (bundles : ℝ) ≤ (n : ℝ) * d := by exact_mod_cast hbundles
  have hM : (motifs : ℝ) ≤ (n : ℝ) * d := by exact_mod_cast hmotifs
  have hS : (sites : ℝ) ≤ n := by exact_mod_cast hsites
  have hm0 : 0 ≤ ∑ e, (m e : ℝ) := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hb : (bundles : ℝ) * Q / (4 * (p / 3)) ≤ ((n : ℝ) * d) * Q * ((n : ℝ) * d) * (3 / 4) := by
    calc
      _ = (bundles : ℝ) * Q * ((n : ℝ) * d) * (3 / 4) := by
        simp only [p, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
        ring
      _ ≤ _ := by gcongr
  have hc : (motifs : ℝ) * C / p ≤ ((n : ℝ) * d) * max C 0 * ((n : ℝ) * d) := by
    rw [show (motifs : ℝ) * C / p = (motifs : ℝ) * C * ((n : ℝ) * d) by
      dsimp only [p]; rw [div_div_eq_mul_div, div_one]]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (mul_le_mul_of_nonneg_left (le_max_left C 0) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hM (le_max_right C 0))
  have hslots : (motifs : ℝ) * (∑ e, (m e : ℝ)) / (4 * p') ≤
      (((n : ℝ) * d) * (∑ e, (m e : ℝ)) * ((n : ℝ) * d')) / 4 := by
    rw [show (4 : ℝ) * p' = 4 / ((sites : ℝ) * d') by dsimp [p']; ring, div_div_eq_mul_div]
    gcongr
  refine (add_le_add (div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hb hH) hc)
    (by positivity)) hslots).trans_eq ?_
  unfold roundingConstant
  ring

/-- Uniform mass of a single arc on a degree-`d` graph on `V`. -/
noncomputable def equalArcMass (V : Type*) [Fintype V] (d : ℕ) : ℝ :=
  1 / ((Fintype.card V : ℝ) * d)

end Compression.ShrinkEnergy

namespace Compression.PackingData

open ShrinkEnergy SurvivingSlots

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [Nonempty V]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Equation (7.2) for an actual packed graph. Each motif uses one selected
supply term. The chosen layout is shared by every motif. The error coefficient
depends only on the degrees, number of color bits, relative masses, subdivision
and fixed conversion constants. -/
theorem packed_energy_le (P : PackingData V H Tag L d c) (hc : 2 ≤ c) (hd : 0 < d)
    {d' : ℕ} (hd' : 0 < d')
    (number : P.BundleNumbering) (old : Arc V H Tag L d c → ℕ) (w : P.Motif → Bool → Fin 4 → ℕ)
    (q : Fin 4 → ℝ) (m : Fin 4 → ℕ) {α factor C : ℝ} (hα : 0 < α) (hf : 0 ≤ factor)
    (hq : ∀ e, 0 < q e) (hm : ∀ e, 0 < m e)
    (hmass : ∀ e, α * equalArcMass (Position V H Tag L c) d * q e ≤
      (m e : ℝ) * equalArcMass (Site V Tag L) d')
    (hterm : ∀ v, (∑ l : Bool, ∑ e, (w v l e : ℝ) ^ 2 / q e) ≤
      factor * (3 * (P.abWidth number old v : ℝ) ^ 2 + (old v.1 : ℝ) ^ 2) + C) :
    let p := equalArcMass (Position V H Tag L c) d
    let p' := equalArcMass (Site V Tag L) d'
    (∑ i : Id P.Motif m, (slotWidth m w (chosenLayout p q w) i : ℝ) ^ 2 / p') ≤
      factor / (2 * α) * (∑ a, (old a : ℝ) ^ 2 / p) +
        roundingConstant d d' (pieceCount d c) factor C α m *
          (Fintype.card (Position V H Tag L c) : ℝ) ^ 2 := by
  intro p p'
  have hp : 0 < p := one_div_pos.mpr
    (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr hd))
  have hp' : 0 < p' := one_div_pos.mpr
    (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr hd'))
  have he := shrinking_step_le w (P.abWidth number old) (fun v ↦ old v.1) q m hp hp' hα hf
    hq hm hmass (P.demand_energy_le hc hd number old hp) hterm
  rw [add_assoc] at he
  apply he.trans (add_le_add_right _ _)
  apply errors_quadratic
  · exact Fintype.card_le_of_injective (fun x : Site V Tag L ↦ (⟨x, 0, 0⟩ : Position V H Tag L c))
      fun _ _ h ↦ congrArg Prod.fst h
  · rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (Fintype.card_le_of_injective
      (fun x : Site V Tag L ↦ (⟨x, 0, 0⟩ : Position V H Tag L c)) fun _ _ h ↦ congrArg Prod.fst h)
  · refine (Fintype.card_le_of_injective Subtype.val (Subtype.val_injective (p := _))).trans_eq ?_
    simp only [Arc, Position, Fintype.card_prod, Fintype.card_fin]
    ring
  · exact hf
  · exact hα

end Compression.PackingData

end VPVNP
end Computability
end OAI
