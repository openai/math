import OAI.ThreeFlat.Diagonal.ShrinkDemandEnergy
import OAI.ThreeFlat.Diagonal.ShrinkIntegerLayout
import OAI.ThreeFlat.Diagonal.ShrinkSubdivision
import OAI.Computability.VPVNP.MotifGrid

namespace OAI
/-! # Energy of the numbered six-party shrinking stage -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression Computability.VPVNP.MotifGrid
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)

private theorem widthNorm_sq {I : Type*} [Fintype I] (p : I → ℝ) (x : I → ℝ) (h : ∀ i, 0 < p i) :
    widthNorm p x ^ 2 = ∑ i, x i ^ 2 / p i :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (h i).le)

/-- The uniform additive constant of the fixed six-party grid is charged once per physical motif.
The AB demand additionally pays the balanced rounding error on the thick bundles. -/
theorem shrink_supply_energy (w : Arc V H Tag L d c → ℕ) (hQ : 0<Q)
    (hcount : Q = 3*(2^(c-2)*d)) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (width : P.Motif → Fin 8 → ℕ) {μ C : ℝ} (hμ : 0<μ)
    (localBound : ∀ m, widthNorm ShrinkMotif.supplyMass (fun e => (width m e : ℝ))^2 ≤
      (63/32 : ℝ)*widthNorm ShrinkMotif.demandMass (fun e => (demandWidth P w num m e : ℝ))^2+C) :
    (∑ m, ∑ e, (width m e : ℝ)^2 / ShrinkMotif.supplyMass e) / μ ≤
      (63/32 : ℝ)*((∑ e, (w e : ℝ)^2/μ)+ Fintype.card (Site V Tag L × Fin d)*(Q/(4*(1/3)*μ))) +
      Fintype.card P.Motif*(C/μ) := by
  have sup (e : Fin 8) : 0 < ShrinkMotif.supplyMass e := by fin_cases e <;> norm_num [ShrinkMotif.supplyMass]
  have dem (e : Fin 2) : 0 < ShrinkMotif.demandMass e := by fin_cases e <;> norm_num [ShrinkMotif.demandMass]
  have h (m : P.Motif) := div_le_div_of_nonneg_right (localBound m) hμ.le
  simp_rw [widthNorm_sq _ _ sup, widthNorm_sq _ _ dem] at h
  let a (m : P.Motif) := (SlotEnergy.piece (thickWidth P w (num m).1) Q (num m).2 : ℝ)
  have local' (m : P.Motif) :
      (∑ e, (width m e : ℝ)^2 / ShrinkMotif.supplyMass e) / μ ≤
        (63/32 : ℝ)*(a m^2/((1/3)*μ)+(w m.val : ℝ)^2/μ) + C/μ := by
    have hm := h m
    simp only [Fin.sum_univ_two, ShrinkMotif.demandMass, demandWidth, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, div_one] at hm
    convert hm using 1; dsimp [a]; ring
  have total := Finset.sum_le_sum (s := Finset.univ) fun m _ => local' m
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at total
  exact total.trans (add_le_add (mul_le_mul_of_nonneg_left
    (assigned_demands_le P w hQ hcount num hμ) (by norm_num : (0:ℝ) ≤ 63/32)) le_rfl)

variable (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)

/-- Sum of the physical crossing-edge terms equals the four selected entries of each motif. -/
theorem crossing_energy_eq (width : P.Motif → Fin 8 → ℕ) (layout : Bool) {μ : ℝ} :
    (∑ e : CrossEdge P layout, (width e.1 e.2 : ℝ)^2 / (SlotEnergy.retainedMass (typeIndex P hn good layout e)*μ)) =
      ShrinkMotif.retainedEnergy (fun m e => (width m e : ℝ)^2 / ShrinkMotif.supplyMass e) layout / μ := by
  rw [Fintype.sum_sigma, ShrinkMotif.retainedEnergy, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [← (crossTypeEquiv P hn good layout m).sum_comp, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp [typeIndex, ShrinkMotif.retained_mass, div_div]

/-- A numerically chosen common layout followed by the actual subdivision of every crossing edge.
The leading constant is the six-party energy times the layout and floor losses. -/
theorem numbered_shrink_energy (width : P.Motif → Fin 8 → ℕ) (n : Fin 4 → ℕ)
    (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
    [Nonempty (Numbered V Tag L (usedDegree n c d+pad))]
    {μ old extra : ℝ} (hμ : 0<μ)
    (enough : ∀ i, (1-1/128)* (SlotEnergy.retainedMass i * μ) ≤
      n i * (1/(Fintype.card (Numbered V Tag L (usedDegree n c d+pad)) : ℝ)))
    (supply : (∑ m, ∑ e, (width m e : ℝ)^2 / ShrinkMotif.supplyMass e)/μ ≤ (63/32)*old + extra) :
    let layout := ShrinkMotif.chooseWidths width
    let ns := fun e : CrossEdge P layout => n (typeIndex P hn good layout e)
    let bs := fun e : CrossEdge P layout => width e.1 e.2
    let cover := allPieceSlots P hn good layout n order hc pad
    let Z : ℝ := Fintype.card (Numbered V Tag L (usedDegree n c d+pad))
    (∑ a, (SlotRefinement.actualWidth ns bs cover a : ℝ)^2/(1/Z)) ≤ (126/127)*old + (64/127)*extra + Z^2/4 := by
  intro layout ns bs cover Z
  let E := fun m e => (width m e : ℝ)^2/ShrinkMotif.supplyMass e
  have chosen : 2*ShrinkMotif.retainedEnergy E layout ≤ ∑ m, ∑ e, E m e := by
    dsimp only [layout]
    rw [ShrinkMotif.chooseWidths_eq]
    exact ShrinkMotif.chosen_energy E
  have h := div_le_div_of_nonneg_right chosen hμ.le
  have hm (e : CrossEdge P layout) : 0 < SlotEnergy.retainedMass (typeIndex P hn good layout e)*μ :=
    mul_pos (lt_of_lt_of_le (by norm_num) (SlotEnergy.min_retainedMass _)) hμ
  have rounded := SlotRefinement.actual_energy_le ns bs (fun e => positive _) cover
    (fun e => SlotEnergy.retainedMass (typeIndex P hn good layout e)*μ) hm (δ := 1/128)
    (by norm_num) (fun e => enough _)
  change (∑ a, (SlotRefinement.actualWidth ns bs cover a : ℝ)^2/(1/Z)) ≤
    (∑ e : CrossEdge P layout, (width e.1 e.2 : ℝ)^2/(SlotEnergy.retainedMass (typeIndex P hn good layout e)*μ)) /
      (1-1/128) + Z^2/4 at rounded
  rw [crossing_energy_eq] at rounded
  rw [mul_div_assoc] at h
  change (∑ m, ∑ e, E m e)/μ ≤ (63/32)*old + extra at supply
  change _ ≤ (ShrinkMotif.retainedEnergy E layout / μ) / (1-1/128) + Z^2/4 at rounded
  apply rounded.trans
  calc
    _ = (64/127:ℝ)*(2*(ShrinkMotif.retainedEnergy E layout / μ)) + Z^2/4 := by ring
    _ ≤ (64/127:ℝ)*((63/32)*old+extra) + Z^2/4 :=
      add_le_add (mul_le_mul_of_nonneg_left (h.trans supply) (by norm_num : (0:ℝ) ≤ 64/127)) le_rfl
    _ = _ := by ring

/-- The scale used in the slot floor is exactly the new arc mass divided by the old one. -/
theorem shrink_slots_enough {Z μ scale : ℝ} (hμ : 0<μ) (hs : 0<scale) (small : scale≤1/1024)
    (ratio : scale * μ = 1/Z) (i : Fin 4) :
    (1-1/128)*(SlotEnergy.retainedMass i*μ) ≤ SlotEnergy.slotCount scale i * (1/Z) := by
  rw [← ratio, ← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (SlotEnergy.slotCount_mass hs small i).2.1 hμ.le

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
