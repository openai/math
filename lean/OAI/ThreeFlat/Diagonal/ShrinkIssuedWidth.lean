import OAI.ThreeFlat.Diagonal.FixedMotifMaxWidth
import OAI.ThreeFlat.Diagonal.PhysicalShrink
import OAI.ThreeFlat.Diagonal.ShrinkDemandEnergy

namespace OAI
/-! # Width of each issued motif field and its numbered physical pieces -/

namespace ThreeFlat.Diagonal

open Computability.VPVNP.Compression
open scoped Classical BigOperators
noncomputable section

namespace SlotEnergy

theorem piece_le_total (b m : ℕ) (i : Fin m) : piece b m i ≤ b := by
  calc
    piece b m i ≤ ∑ j, piece b m j :=
      Finset.single_le_sum (f := piece b m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = b := sum_piece b m ((Nat.zero_le i.val).trans_lt i.isLt)

end SlotEnergy

namespace SlotRefinement

theorem actualWidth_le {E D Pad : Type} (n b : E → ℕ)
    (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) {W : ℕ} (H : ∀ e, b e ≤ W) (i : D) :
    actualWidth n b cover i ≤ W := by
  unfold actualWidth
  rcases cover.symm i with ⟨e,j⟩ | pad
  · exact (SlotEnergy.piece_le_total _ _ j).trans (H e)
  · exact Nat.zero_le _

end SlotRefinement

namespace CompressorPacking

def widthMultiplicity (c d : ℕ) : ℕ := 1 + 2^(c-2)*d

variable {c d Q : ℕ} {V H Tag L : Type} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)

theorem demandWidth_le (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) {W : ℕ}
    (hw : ∀ e, w e ≤ W) (m : P.Motif) (j : Fin 2) :
    demandWidth P w num m j ≤ widthMultiplicity c d * W := by
  have thick (p : Site V Tag L × Fin d) : thickWidth P w p ≤ (2^(c-2)*d)*W := by
    calc
      thickWidth P w p ≤ ∑ _a : ThickAt P p, W :=
        Finset.sum_le_sum fun i _ => hw i.val
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,card_thickAt,nsmul_eq_mul,Nat.cast_id]
  fin_cases j
  · change SlotEnergy.piece _ Q _ ≤ _
    exact (SlotEnergy.piece_le_total _ _ _).trans ((thick _).trans
      (Nat.mul_le_mul_right W (by unfold widthMultiplicity; omega)))
  · change w m.val ≤ _
    have h : 1 ≤ widthMultiplicity c d := by unfold widthMultiplicity; omega
    exact (hw _).trans (by simpa only [one_mul] using Nat.mul_le_mul_right W h)

variable {F : Type} [Field F]

def shrinkMotifWidthFactor (T : ShrinkMotif.Table F) (c d : ℕ) : ℕ :=
  (FixedMotifMaxWidth.tile_bound T.base T.block (widthMultiplicity c d)).choose

theorem PhysicalShrink.issued_le (T : ShrinkMotif.Table F) (code : Arc V H Tag L d c ↪ ℕ)
    (hc : 2 ≤ c) {W : ℕ} (hw : ∀ e, w e ≤ W) (x : PhysicalShrink.Hists T P w code hc)
    (m : P.Motif) (e : Fin 8) :
    PhysicalShrink.issued T P w code hc x m e ≤ shrinkMotifWidthFactor T c d * (1+W) := by
  exact (FixedMotifMaxWidth.tile_bound T.base T.block (widthMultiplicity c d)).choose_spec W
    (PhysicalShrink.b P w code hc m) (demandWidth_le P w _ hw m)
    (PhysicalShrink.picked T P w code hc m) (x m) e

end CompressorPacking
end
end ThreeFlat.Diagonal

end OAI
