import OAI.ThreeFlat.Diagonal.PhysicalShrinkCopies
import OAI.ThreeFlat.Diagonal.PhysicalStateWidth
import OAI.ThreeFlat.Diagonal.BlockEnergyPotential
import OAI.ThreeFlat.Diagonal.PhysicalStageShrink
import OAI.ThreeFlat.Diagonal.CompressorScanCost
import OAI.ThreeFlat.Diagonal.CompressorDemandOrdinal

namespace OAI
/-! # Total and local work of the selected motif scores in a binary shrink -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F]

theorem shrinkCopies_budget {d lanes rem hbits tags c : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord c × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d c)
    (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d c ↪ ℕ)
    (hc : 2≤c) (hd : 0<d) :
    let w := A.width ∘ (StageAddress.splitEdge u).symm
    let r := PhysicalShrink.r T P w code hc
    (∑ m, r m) ≤ d*A.positions+A.widthSum ∧
      ∀ m, r m ≤ shrinkCopyFactor c d*(1+A.maxWidth) := by
  intro w r
  let E := Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d c
  have hE : Fintype.card E = d*A.positions := by
    rw [←Fintype.card_congr (StageAddress.splitEdge (V:=A.Base) (d:=d) u), State.positions,
      ←Fintype.card_congr A.chart]
    simp only [Fintype.card_prod,Fintype.card_fin]
    ac_rfl
  have hM : Fintype.card P.Motif ≤ Fintype.card E :=
    Fintype.card_le_of_injective (fun m : P.Motif => m.val) Subtype.val_injective
  have hw : (∑ e, w e) = A.widthSum := (StageAddress.splitEdge u).symm.sum_comp A.width
  constructor
  · exact (PhysicalShrink.sum_copies_le T P w code hc hd).trans
      (Nat.add_le_add (hM.trans_eq hE) hw.le)
  · exact PhysicalShrink.copies_le T P w code hc (fun e => A.width_le_maxWidth _)

section Binary

variable (T : ShrinkMotif.Table F) (s rem : ℕ)
  (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem))))

abbrev shrinkGroups := (Ordered.binaryPacking A.order.symm A.graph).Motif

/-- This is the copy count in the histogram type of `shrinkRaw`. The mixed radix
order, binary lane split and selected motif row are the ones used by the move. -/
def shrinkCopies : shrinkGroups s rem A → ℕ :=
  let d := 2^s
  let c := 2*d+1
  let t := CompressorPacking.tagBits d
  let P := Ordered.binaryPacking A.order.symm A.graph
  let u := laneSplit c s t rem
  let ord : A.Base ↪ ℕ := A.order.toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩
  let code := demandOrdinal P ord (Native.tagOrdinal t).toEmbedding (Native.tagOrdinal rem).toEmbedding
  PhysicalShrink.r T P (oldWidth A u) code (by
    have := Nat.two_pow_pos s
    omega)

/-- The same finite family gives the total charge and its maximum local multiplicity. -/
theorem shrinkCopies_bounds :
    (∑ m, shrinkCopies T s rem A m) ≤ (2^s)*A.positions+A.widthSum ∧
      ∀ m, shrinkCopies T s rem A m ≤ shrinkCopyFactor (2*(2^s)+1) (2^s)*(1+A.maxWidth) := by
  unfold shrinkCopies
  apply shrinkCopies_budget
  all_goals first | exact Nat.two_pow_pos _

end Binary
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
