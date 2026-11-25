import OAI.ThreeFlat.Diagonal.ShrinkIssuedWidth

namespace OAI
/-! # Copy counts of the two actual old demands at a shrink motif -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L F : Type} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [Field F]
    (T : ShrinkMotif.Table F) (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)

/-- The AB intervals partition the thick widths. Each other old arc occurs once as a CD field. -/
theorem sum_demandWidth (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (hQ : 0<Q) :
    (∑ m, ∑ j, demandWidth P w num m j) = ∑ e, w e := by
  let f (a : (Site V Tag L × Fin d) × Fin Q) := SlotEnergy.piece (thickWidth P w a.1) Q a.2
  have hab : (∑ m, SlotEnergy.piece (thickWidth P w (num m).1) Q (num m).2) = ∑ p, thickWidth P w p := by
    change (∑ m, f (num m)) = _
    rw [num.sum_comp f,Fintype.sum_prod_type]
    simp only [f,SlotEnergy.sum_piece _ _ hQ]
  simp only [Fin.sum_univ_two,demandWidth,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Finset.sum_add_distrib,hab]
  change (∑ p, ∑ a : ThickAt P p, w a.val) + (∑ m : P.Motif, w m.val) = _
  exact_mod_cast (old_arc_sum P (fun e => (w e : ℝ)))

variable (code : Arc V H Tag L d c ↪ ℕ) (hc : 2≤c)

theorem PhysicalShrink.sum_copies_le (hd : 0<d) :
    (∑ m, PhysicalShrink.r T P w code hc m) ≤ Fintype.card P.Motif + ∑ e, w e := by
  have big : 4 ≤ 2^c*d := (Nat.pow_le_pow_right (by decide : 0<2) hc :
    2^2 ≤ 2^c).trans (Nat.le_mul_of_pos_right _ hd)
  have hQ : 0<PhysicalShrink.count (c:=c) (d:=d) := by unfold PhysicalShrink.count; omega
  calc
    _ ≤ ∑ m : P.Motif, (1+∑ j, PhysicalShrink.b P w code hc m j) :=
      Finset.sum_le_sum fun m _ => FixedMotifMaxWidth.score_le_sentinel _ T.base (PhysicalShrink.picked T P w code hc m)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,PhysicalShrink.b,
        sum_demandWidth P w _ hQ]

/-- The local copy factor depends on the two fixed degrees and is independent of the table row. -/
def shrinkCopyFactor (c d : ℕ) := 1+2*widthMultiplicity c d

theorem PhysicalShrink.copies_le {W : ℕ} (hw : ∀ e, w e ≤ W) (m : P.Motif) :
    PhysicalShrink.r T P w code hc m ≤ shrinkCopyFactor c d*(1+W) := by
  have hr := FixedMotifMaxWidth.score_le_sentinel (PhysicalShrink.b P w code hc m) T.base
    (PhysicalShrink.picked T P w code hc m)
  have h₀ := demandWidth_le P w (motifNumbers P code hc) hw m 0
  have h₁ := demandWidth_le P w (motifNumbers P code hc) hw m 1
  rw [Fin.sum_univ_two] at hr
  unfold PhysicalShrink.r
  apply hr.trans
  change 1 + (demandWidth P w (motifNumbers P code hc) m 0 + demandWidth P w (motifNumbers P code hc) m 1) ≤ _
  unfold shrinkCopyFactor
  nlinarith only [h₀,h₁,Nat.zero_le W,Nat.zero_le (widthMultiplicity c d)]

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
