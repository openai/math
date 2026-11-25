import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedCases
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedRelease

/-! # Native repair release from four typed physical passes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims Space InterchangeROM InterchangeAddress Interchange.Template
  InterchangeROMStageVolume Interchange.StageScript InterchangeSpectralFibre

def ordinaryFactor (x : Data) := LocalTable.Lift.localFactor x.modulusIndex x.labels
  (rows x) (checks x) x.m (Selected.half x) x.repair

theorem computable_ordinaryFactor : Computable ordinaryFactor :=
  LocalTable.Lift.computable_localFactor Data.primrec_modulusIndex.to_comp
    (Data.primrec_header 4).to_comp (Raw.primrec_rowCount.comp (Data.primrec_header 2)).to_comp
    (Raw.primrec_checkCount.comp (Data.primrec_header 2)).to_comp (Data.primrec_header 2).to_comp
    (Raw.primrec_halfCode.comp Data.primrec_modulusIndex).to_comp Data.primrec_repair.to_comp

def phaseRate (x : Data) (chart conversion correction : ℕ) :=
  max (ordinaryFactor x) (max chart (max conversion correction))

theorem computable_phaseRate {chart conversion correction : Data → ℕ}
    (hc : Computable chart) (hs : Computable conversion) (ht : Computable correction) :
    Computable (fun x => phaseRate x (chart x) (conversion x) (correction x)) :=
  Primrec.nat_max.to_comp.comp computable_ordinaryFactor
    (Primrec.nat_max.to_comp.comp hc (Primrec.nat_max.to_comp.comp hs ht))

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D : Type}
variable [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

/-- Execution contract at the actual wide and short banks emitted by the selected code. -/
abbrev NativeCases (h : Data.Valid j threshold x) (P G S : Tape) (f : ℕ) (pay : Series D)
    (width : ℕ) (env : Env) (time cap depth chart conversion correction : ℕ) :=
  Cases x x.spec (flags ∘ Prod.fst) (lift (directions false x.half)) (lift (directions true x.half))
    (Data.stagePayload h) (wideBank x P G S f pay) (shortBank x P G S f pay) env (send (InterchangeROMAddress.header f P G S))
    (Raw.rowCount x.m * cost (Data.wordPrice h) (Data.predictorStage h)) (x.labels*Raw.checkCount x.m)
    time cap depth (mass (send (InterchangeROMAddress.header f P G S)) (SweepBank.layout P G S x.a x.m x.b f).count width)
    chart conversion correction

private theorem local_commands (x : Data) (a : Leaf) :
    LocalTable.Lift.choose (matrixLeaf x) (commands x) a = commands x a := by cases a <;> rfl

/-- Only the native chart, two sweeps and sign table require separate
certificates. The five arithmetic commands are discharged by their own ROMs. -/
theorem program_of_cases (h : Data.Valid j threshold x) (pay : Series D) (width : ℕ)
    (hw : pay.count ≤ width) (env : Env) (time cap depth chart conversion correction : ℕ)
    (runs : NativeCases h P G S f pay width env time cap depth chart conversion correction)
    (u : x.Wide P G S f D) (deck : Deck) (base : ℕ) (hr : DeckCap base deck) :
    let H := send (InterchangeROMAddress.header f P G S)
    let M := mass H (SweepBank.layout P G S x.a x.m x.b f).count width
    let localBound := compiledRate x (phaseRate x chart conversion correction) * M
    BoundedFits env (program x) (pile 0 (packet H (wideBank x P G S f pay u)) deck)
      (pile 0 (packet H (wideBank x P G S f pay (swapPayload u))) deck)
      (localBound+x.calls*time) (base+(localBound+cap)) (localBound+depth) := by
  apply program_of_phases h pay width hw env (phaseRate x chart conversion correction) time cap depth _ u deck base hr
  intro k xs ys tr r b hr
  let K := phaseRate x chart conversion correction
  have h₀ : ordinaryFactor x ≤ K := by dsimp [K,phaseRate]; omega
  have h₁ : chart ≤ K := by dsimp [K,phaseRate]; omega
  have h₂ : conversion ≤ K := by dsimp [K,phaseRate]; omega
  have h₃ : correction ≤ K := by dsimp [K,phaseRate]; omega
  by_cases route : LocalTable.Lift.Routed k
  · exact Cases.routed runs h₁ h₂ h₃ x.half k xs ys route tr r b hr
  · let ord := SweepBank.layout P G S x.a x.m x.b f
    let H := send (InterchangeROMAddress.header f P G S)
    let M := mass H ord.count width
    have hl : 0 < x.labels := h.1.2.2.2.2.2.2.1
    have hrow : 0 < Raw.rowCount x.m := by
      unfold Raw.rowCount Sizes.rows Sizes.basisCount Sizes.pencilOrder
      positivity
    have run := LocalTable.Lift.local_transition x.repair ord (fun _ => pay) Prod.mk H width
      (fun _ => hw) (Nat.mul_pos hl hrow) (commands x) tr route env r b hr
    change BoundedFits env (LocalTable.Lift.choose (matrixLeaf x) (commands x) k)
      (pile 0 (packet H xs) r) (pile 0 (packet H ys) r)
      (ordinaryFactor x*M) (b+ordinaryFactor x*M) (ordinaryFactor x*M) at run
    rw [local_commands] at run
    have hm := Nat.mul_le_mul_right M h₀
    exact run.mono (Nat.le_trans hm (Nat.le_add_right ..))
      (Nat.add_le_add_left (Nat.le_trans hm (Nat.le_add_right ..)) _)
      (Nat.le_trans hm (Nat.le_add_right ..))

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
