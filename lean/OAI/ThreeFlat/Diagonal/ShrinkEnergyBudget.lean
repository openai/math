import OAI.ThreeFlat.Diagonal.ShrinkStageEnergy
import OAI.ThreeFlat.Diagonal.MotifChosenEnergy

namespace OAI
/-! # Uniform additive error for an actual physical shrinking stage -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths MotifOuterTerms
open scoped BigOperators Classical
noncomputable section

private theorem overhead {old sites deg Q D C : ℝ} (h : 0<old) (hs : 0≤ sites) (hd : 0<deg)
    (hQ : 0≤Q) (_hD : 0≤D) (hC : 0≤C) (hsize : sites ≤ old) :
    let μ := 1/(old*deg)
    (64/127 : ℝ)*((63/32)*(sites*deg)*(Q/(4*(1/3)*μ))+(sites*deg*Q)*(C/μ))+(sites*D)^2/4 ≤
      ((64/127)*((63/32)*deg^2*(3/4)*Q+deg^2*Q*C)+ D^2/4)*old^2 := by
  intro μ
  have hc : 0 ≤ (64/127 : ℝ)*((63/32)*deg^2*(3/4)*Q+deg^2*Q*C) := by positivity
  have hd' : 0 ≤ D^2/4 := by positivity
  have pair := mul_le_mul_of_nonneg_right hsize h.le
  have sq := pow_le_pow_left₀ hs hsize 2
  calc
    _ = ((64/127)*((63/32)*deg^2*(3/4)*Q+deg^2*Q*C))*(sites*old) + (D^2/4)*sites^2 := by
      dsimp only [μ]
      field_simp [h.ne',hd.ne']
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (by simpa only [pow_two] using mul_le_mul_of_nonneg_left pair hc)
        (mul_le_mul_of_nonneg_left sq hd')

variable {c d Q : ℕ} {V H Tag L : Type} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c)

omit [AddCommGroup Tag] [AddCommGroup L] in
private theorem card_numbered (D : ℕ) :
    Fintype.card (Numbered V Tag L D) = Fintype.card (Site V Tag L)*D := by
  simp only [Numbered,Site,Fintype.card_prod,Fintype.card_fin]
  ac_rfl

include P in
omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
/-- The slot floor has the right relative mass for the old and new physical graphs. -/
theorem numbered_slot_mass (n : Fin 4 → ℕ) (pad : ℕ) (hd : 0<d)
    (hs : 0<Fintype.card (Site V Tag L)) (hD : 0<usedDegree n c d+pad)
    (small : ((2^c*d*d:ℕ):ℝ)/(usedDegree n c d+pad:ℕ) ≤ 1/1024)
    (floorCounts : ∀ j, n j = SlotEnergy.slotCount (((2^c*d*d:ℕ):ℝ)/(usedDegree n c d+pad:ℕ)) j) :
    ∀ j, 0<n j ∧ (1-1/128)*(SlotEnergy.retainedMass j*(1/((Fintype.card (Position V H Tag L c):ℝ)*d))) ≤
      n j*(1/(Fintype.card (Numbered V Tag L (usedDegree n c d+pad)) : ℝ)) := by
  let D := usedDegree n c d+pad
  let μ := 1/((Fintype.card (Position V H Tag L c):ℝ)*d)
  let scale := ((2^c*d*d:ℕ):ℝ)/(D:ℝ)
  have ha : 0<(Fintype.card (Site V Tag L):ℝ) := Nat.cast_pos.mpr hs
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hD' : 0<(D:ℝ) := Nat.cast_pos.mpr hD
  have hμ : 0 < μ := by dsimp only [μ]; rw [position_count P,Nat.cast_mul]; positivity
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have ratio : scale*μ = 1/(Fintype.card (Numbered V Tag L D):ℝ) := by
    dsimp only [scale,μ]
    rw [position_count P, card_numbered]
    push_cast
    field_simp [ha.ne',hd'.ne',hD'.ne']
  intro j
  rw [floorCounts j]
  exact ⟨(SlotEnergy.slotCount_mass hscale small j).1, shrink_slots_enough hμ hscale small ratio j⟩

/-- Bundle rounding, the per-motif additive error and final parallel subdivision all cost at
most a fixed multiple of the number of old positions squared. -/
theorem physical_shrink_bound (w : Arc V H Tag L d c → ℕ) (hQ : 0<Q) (hd : 0<d)
    (hcount : Q=3*(2^(c-2)*d)) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (hn : ∀ a : Tag, -a=a) (good : TagConditions P.slots (shift P) P.offset)
    (width : P.Motif → Fin 8 → ℕ) (n : Fin 4 → ℕ) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
    [Nonempty (Numbered V Tag L (usedDegree n c d+pad))] (hs : 0<Fintype.card (Site V Tag L))
    (hD : 0<usedDegree n c d+pad) (small : ((2^c*d*d:ℕ):ℝ)/(usedDegree n c d+pad:ℕ) ≤ 1/1024)
    (floorCounts : ∀ j, n j = SlotEnergy.slotCount (((2^c*d*d:ℕ):ℝ)/(usedDegree n c d+pad:ℕ)) j)
    {C : ℝ} (hC : 0≤C) (localBound : ∀ m, widthNorm ShrinkMotif.supplyMass (fun e => (width m e : ℝ))^2 ≤
      (63/32 : ℝ)*widthNorm ShrinkMotif.demandMass (fun e => (demandWidth P w num m e : ℝ))^2+C) :
    let D : ℝ := usedDegree n c d+pad
    let count : ℝ := Fintype.card (Position V H Tag L c)
    let layout := ShrinkMotif.chooseWidths width
    let ns := fun e : CrossEdge P layout => n (typeIndex P hn good layout e)
    let bs := fun e : CrossEdge P layout => width e.1 e.2
    let cover := allPieceSlots P hn good layout n order hc pad
    let Z : ℝ := Fintype.card (Numbered V Tag L (usedDegree n c d+pad))
    (∑ a, (SlotRefinement.actualWidth ns bs cover a : ℝ)^2/(1/Z)) ≤
      (126/127)*(∑ e, (w e : ℝ)^2/(1/(count*d))) +
        ((64/127)*((63/32)*(d:ℝ)^2*(3/4)*Q+(d:ℝ)^2*Q*C)+D^2/4)*count^2 := by
  intro D count layout ns bs cover Z
  let sites : ℝ := Fintype.card (Site V Tag L)
  let μ := 1/(count*d)
  have hcCount : sites ≤ count := by
    dsimp only [sites,count]
    exact_mod_cast (show Fintype.card (Site V Tag L) ≤ Fintype.card (Position V H Tag L c) by
      rw [position_count P]; exact Nat.le_mul_of_pos_right _ (by positivity))
  have hsites : 0<sites := Nat.cast_pos.mpr hs
  have hcPos : 0<count := hsites.trans_le hcCount
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have mass := numbered_slot_mass P n pad hd hs hD small floorCounts
  obtain ⟨hb,hm⟩ : (Fintype.card (Site V Tag L × Fin d):ℝ)=sites*d ∧ (Fintype.card P.Motif:ℝ)=sites*d*Q := by
    dsimp only [sites]
    simp only [Fintype.card_congr num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,and_self]
  have supply := shrink_supply_energy P w hQ hcount num width hμ localBound
  rw [hb,hm] at supply
  have sumBound := numbered_shrink_energy P hn good width n (fun j => (mass j).1) order hc pad hμ
    (fun j => (mass j).2) (old := ∑ e, (w e:ℝ)^2/μ) (extra := (63/32)*(sites*d)*(Q/(4*(1/3)*μ))+(sites*d*Q)*(C/μ))
    (by linarith only [supply])
  have zEq : Z=sites*D := by dsimp only [Z,sites,D]; rw [card_numbered,Nat.cast_mul,Nat.cast_add]
  have extra := overhead hcPos hsites.le hd' (Nat.cast_nonneg Q) (by dsimp [D]; positivity : 0≤D) hC hcCount
  change _ ≤ (126/127)*_ + _ + Z^2/4 at sumBound
  rw [zEq,add_assoc] at sumBound
  exact sumBound.trans (add_le_add le_rfl extra)

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
