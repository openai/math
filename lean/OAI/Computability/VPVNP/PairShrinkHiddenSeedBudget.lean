import OAI.Computability.VPVNP.PairShrinkHiddenRows

/-!
# Sizes of the selected shrinking hidden rows

The native guess stream concatenates one little-endian word for each absorbed
edge at its owner. Its length is the sum of the selected field widths there.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenRows

open Compression Compression.ShrinkMotif CompressorRecords ShrinkHistoryRows NetworkKernel
open MotifBlocks MotifGrid MotifConversion

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (side : Bool)
  (ws : X.packingData.Motif → Bool × Fin 4 → ℕ)
  (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
  (h : Placed (X.packingData.shrinkInternalOwner side) (internalLabel ws side) v)

/-- The physical row contains exactly four absorbed roles per resident motif count. -/
theorem rows_length :
    (ShrinkHiddenSlots.rows X side ws v h).length = ShrinkResidentLayout.rowCapacity a false := by
  classical
  rw [ShrinkHiddenSlots.rows, List.length_ofFn]
  change Fintype.card {e : X.packingData.Motif × Fin 4 //
    v = X.packingData.shrinkInternalOwner side e} = _
  exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => eq_comm))).trans
    (hidden_count X side v)

open scoped Classical in
/-- Reindex the physical scan by the absorbed edges owned at this vertex. -/
theorem stream_length :
    (ShrinkHiddenGuess.stream (ShrinkHiddenSlots.rows X side ws v h)).length =
      ∑ e : {e : X.packingData.Motif × Fin 4 // X.packingData.shrinkInternalOwner side e = v},
        ws e.val.1 (!side, e.val.2) := by
  let o := residents (hiddenOrder X) (X.packingData.shrinkInternalOwner side) v
  let index := o.entries.trans (Equiv.subtypeEquivRight (fun _ => eq_comm))
  simp only [ShrinkHiddenGuess.stream, ShrinkHiddenSlots.rows, List.length_flatMap,
    List.map_ofFn, Function.comp_def, List.length_ofFn, List.sum_ofFn]
  exact index.sum_comp (fun e => ws e.val.1 (!side, e.val.2))

variable {K : Type*} [_root_.Field K] {factor : ℝ}
  (F : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
  (sel : X.ShrinkSelection F)
  (seed : Placed (X.packingData.shrinkInternalOwner side) (internalLabel (widths X F sel) side) v)

/-- The actual selected stream length is linear in the state's maximum wire width. -/
theorem selected_stream_le :
    (ShrinkHiddenGuess.stream (ShrinkHiddenSlots.rows X side (widths X F sel) v seed)).length ≤
      ShrinkResidentLayout.rowCapacity a false * fieldFactor F * (X.maxWireWidth + 1) := by
  classical
  rw [stream_length]
  exact X.packingData.shrinkSite_internalWidth_le (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) F sel side v

variable {S : BlockSchedule K} (B : S.Templates)

/-- One row capacity works for every degree in the finite shrinking schedule. -/
def stageCapacity (S : BlockSchedule K) : ℕ :=
  Finset.univ.sup fun i : Fin S.steps =>
    ShrinkResidentLayout.rowCapacity (S.degreeExponent i.castSucc) false

theorem rowCapacity_le_stageCapacity (i : Fin S.steps) :
    ShrinkResidentLayout.rowCapacity (S.degreeExponent i.castSucc) false ≤ stageCapacity S :=
  Finset.le_sup (f := fun j : Fin S.steps =>
    ShrinkResidentLayout.rowCapacity (S.degreeExponent j.castSucc) false)
    (Finset.mem_univ i)

/-- Uniform bounds for both the field count and the guessed bits, for any site and branch. -/
theorem scheduled_seed_bounds (i : Fin S.steps)
    (Y : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (choice : Y.ShrinkSelection B.shrink) (site : (Y.Base × BitWord (Shrink.J _)) × BitWord g)
    (hidden : Placed (Y.packingData.shrinkInternalOwner side)
      (internalLabel (widths Y B.shrink choice) side) site) :
    let rows := ShrinkHiddenSlots.rows Y side (widths Y B.shrink choice) site hidden
    rows.length ≤ stageCapacity S ∧
      (ShrinkHiddenGuess.stream rows).length ≤
        stageCapacity S * fieldFactor B.shrink * (Y.maxWireWidth + 1) := by
  intro rows
  have cap := rowCapacity_le_stageCapacity (S := S) i
  exact ⟨(rows_length Y side _ site hidden).le.trans cap,
    (selected_stream_le Y side site B.shrink choice hidden).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ cap))⟩

end PairSimulation.ShrinkHiddenRows

end VPVNP
end Computability
end OAI
