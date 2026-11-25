import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedIndices
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionNative
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankConcrete
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalEffective
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectGate
import OAI.Computability.NearSquareRoot.InterchangeROMStageQuote
import OAI.Computability.NearSquareRoot.InterchangeROMAddressWord

/-! # The repair command generated from a numeric interchange template

Every instruction is built from the stored characteristic, chart, check
matrix and shape. The same register count works for every finite template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code GeneratorSyntax CommonRegisters
  Interchange.Template

def slots (x : Data) := x.a+x.m+x.a
def ranks (x : Data) := (List.range x.m).map fun i => x.a+i
def rows (x : Data) := Raw.rowCount x.m
def checks (x : Data) := Raw.checkCount x.m
def half (x : Data) := Raw.halfCode x.modulusIndex

def matrixLeaf (x : Data) (k : LocalTable.Kind) : Cmd :=
  LocalTable.Lift.command k x.modulusIndex x.labels (rows x) (checks x) x.m (half x) x.repair

noncomputable def stage (x : Data) : Cmd :=
  InterchangeROMStage.rawStage x.roleFrame (x.modulusIndex+1) (rows x)
    (InterchangeROMStageTable.gateMatrix x.stageParameters) x.chart (OpcodeProgram.word x.b (slots x))

noncomputable def sweepLeaf (x : Data) (inverse : Bool) : Cmd :=
  SweepBank.command x.a x.m x.labels (checks x) x.b x.modulusIndex (half x) inverse

noncomputable def correct (x : Data) : Cmd :=
  let js := indices x.labels (checks x)
  Correction.nativeLeaf x.b (slots x) (ranks x) 0 (List.range x.m) x.modulusIndex (checks x)
    x.m x.repair js js

noncomputable def commands (x : Data) : Leaf → Cmd
  | .duplicate => matrixLeaf x .duplicate
  | .stage => stage x
  | .extract => matrixLeaf x .extract
  | .forward => sweepLeaf x false
  | .correct => correct x
  | .backward => sweepLeaf x true
  | .restore => matrixLeaf x .restore
  | .copyCube => matrixLeaf x .copyCube
  | .finish => matrixLeaf x .finish

private theorem slots_pr : Primrec slots := Primrec.nat_add.comp
  (Primrec.nat_add.comp (Data.primrec_header 3) (Data.primrec_header 2)) (Data.primrec_header 3)

private theorem rows_pr : Primrec rows := Raw.primrec_rowCount.comp (Data.primrec_header 2)
private theorem checks_pr : Primrec checks := Raw.primrec_checkCount.comp (Data.primrec_header 2)
private theorem half_pr : Primrec half := Raw.primrec_halfCode.comp Data.primrec_modulusIndex

private theorem matrix_effective (k : LocalTable.Kind) : Effective ltr (fun x => matrixLeaf x k) :=
  LocalTable.Lift.effective_command_pr k Data.primrec_modulusIndex (Data.primrec_header 4) rows_pr checks_pr
    (Data.primrec_header 2) half_pr Data.primrec_repair

theorem stage_effective : Effective ltr stage := by
  apply InterchangeROMStage.effective_rawStage Data.primrec_roleFrame.to_comp
    (Primrec.succ.comp Data.primrec_modulusIndex).to_comp rows_pr.to_comp
    Data.primrec_selected_gateMatrix.to_comp Data.primrec_chart.to_comp
  exact OpcodeProgram.word_effective ((Data.primrec_header 1).to_comp.comp Computable.fst)
    (slots_pr.to_comp.comp Computable.fst) Computable.snd

private theorem sweep_effective (inverse : Bool) : Effective ltr (fun x => sweepLeaf x inverse) :=
  SweepBank.effective_command (Data.primrec_header 3).to_comp (Data.primrec_header 2).to_comp
    (Data.primrec_header 4).to_comp checks_pr.to_comp (Data.primrec_header 1).to_comp
    Data.primrec_modulusIndex.to_comp half_pr.to_comp (Computable.const inverse)

theorem correct_effective : Effective ltr correct := by
  have hpos : Computable (fun x : Data => List.range x.m) :=
    (Primrec.list_range.comp (Data.primrec_header 2)).to_comp
  have hr : Computable ranks := Generator.computable_rangeMap (Data.primrec_header 2).to_comp
    (Primrec.nat_add.to_comp.comp ((Data.primrec_header 3).to_comp.comp Computable.fst) Computable.snd).to₂
  have hi := computable_indices (Data.primrec_header 4).to_comp checks_pr.to_comp
  exact Correction.effective_nativeLeaf (Data.primrec_header 1).to_comp slots_pr.to_comp hr
    (Computable.const 0) hpos Data.primrec_modulusIndex.to_comp checks_pr.to_comp (Data.primrec_header 2).to_comp
    Data.primrec_repair.to_comp hi hi

theorem effective_commands : Effective ltr (fun z : Data × Leaf => commands z.1 z.2) := by
  apply effective_dispatch
  intro k
  cases k with
  | stage => exact stage_effective
  | correct => exact correct_effective
  | forward => exact sweep_effective false
  | backward => exact sweep_effective true
  | duplicate | extract | restore | copyCube | finish => exact matrix_effective _

/-- The register bound applies to every stored chart word and every input
size. The numerical capacities of the tapes are part of the execution bound. -/
theorem commands_within : ∃ R, 4 ≤ R ∧ ∀ x k, Within R (commands x k) := by
  obtain ⟨u,hu⟩ := OpcodeProgram.word_within
  obtain ⟨v,hv⟩ := Correction.nativeLeaf_within
  let R := max (max 4 u) (max v (max 3 Sweep.nativeRegs))
  have h4 : 4 ≤ R := by dsimp [R]; omega
  have hu' : u ≤ R := by dsimp [R]; omega
  have hv' : v ≤ R := by dsimp [R]; omega
  have hs : max 3 Sweep.nativeRegs ≤ R := by dsimp [R]; omega
  refine ⟨R,h4,?_⟩
  intro x k
  have mat (a) : Within R (matrixLeaf x a) :=
    RegisterSelect.within_mono h4 _ (LocalTable.Lift.command_within ..)
  have sw (inv) : Within R (sweepLeaf x inv) :=
    RegisterSelect.within_mono hs _ (SweepBank.command_within ..)
  cases k with
  | stage =>
    exact InterchangeROMStage.rawStage_within h4 _ _ _ _ _ _
      (fun w => RegisterSelect.within_mono hu' _ (hu _ _ w))
  | correct =>
    exact RegisterSelect.within_mono hv' _ (hv ..)
  | forward => exact sw false
  | backward => exact sw true
  | duplicate | extract | restore | copyCube | finish => exact mat _

/-- Closed native syntax of the complete predictor, correction and restore schedule. -/
noncomputable def program (x : Data) : Cmd :=
  Physical.command (commands x) (steps (x.labels * rows x) (Sizes.pencilOrder x.m))

theorem effective_program : Effective ltr program :=
  effective_repair effective_commands
    ((Primrec.nat_mul.comp (Data.primrec_header 4) rows_pr).to_comp)
    ((Sizes.primrec_pencilOrder.comp (Data.primrec_header 2)).to_comp)

theorem program_within : ∃ R, ∀ x, Within R (program x) := by
  obtain ⟨R,hR,h⟩ := commands_within
  exact ⟨R,fun x => Physical.command_within hR _ (h x) _⟩

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
