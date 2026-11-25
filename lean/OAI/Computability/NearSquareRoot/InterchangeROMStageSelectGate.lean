import OAI.Computability.NearSquareRoot.InterchangeROMStageSelect
import OAI.Computability.NearSquareRoot.InterchangeROMStageTableGenerate

/-! # A selected template's five physical vector gates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open NearSquareRoot InterchangeROMRepair InterchangeROMStageTable InterchangeROMStage
  IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROMTable

theorem primrec_selected_gateMatrix :
    Primrec₂ fun (x : Template.Data) (t : Frame.Table) => gateMatrix x.stageParameters t :=
  (primrec_gateMatrix.comp (primrec_stageParameters.comp Primrec.fst) Primrec.snd).to₂

variable {j threshold : ℕ} {x : Template.Data} [Fact (x.modulusIndex+1).Prime]

/-- The same five typed gates acting on entire vectors as in `StageRoute.stage`. -/
def packedGate (h : Valid j threshold x) :
    (tag : Fin 5) → ((roleRealization h).Boundary (inputBoundary tag) → x.WideIndex → x.Ground) →
    (roleRealization h).Boundary (inputBoundary tag+1) → x.WideIndex → x.Ground
  | ⟨0,_⟩ => StageRoute.partialTable x.rect
  | ⟨1,_⟩ => StageRoute.mixTable x.rect (rowSel h) x.middleMatrix
  | ⟨2,_⟩ => StageRoute.scatterTable x.rect (colSel h)
  | ⟨3,_⟩ => StageRoute.sumQueries x.rect (mixerMap x.spec.base) (fun q => mixerMap (x.spec.term q))
  | ⟨4,_⟩ => StageRoute.finishTable x.rect

theorem selectedGate_eq_packed (h : Valid j threshold x) (tag : Fin 5) :
    selectedGate h tag = packedGate h tag := by
  fin_cases tag
  · funext y o d
    change StageRoute.partialTable x.rect (fun a => y a d) o = StageRoute.partialTable x.rect y o d
    rcases o with u | ⟨j,b⟩
    · rfl
    · simp [StageRoute.partialTable,Finset.sum_apply]
  · funext y o d
    change StageRoute.mixTable x.rect (rowSel h) x.middleMatrix (fun a => y a d) o =
      StageRoute.mixTable x.rect (rowSel h) x.middleMatrix y o d
    rcases o with u | ⟨j,i⟩
    · rfl
    · simp [StageRoute.mixTable,applyRows,Finset.sum_apply,mul_add]
  · funext y o d
    change StageRoute.scatterTable x.rect (colSel h) (fun a => y a d) o =
      StageRoute.scatterTable x.rect (colSel h) y o d
    rcases o with (v | ⟨j,v⟩) | ⟨j,b⟩
    · rfl
    · simp only [StageRoute.scatterTable,Finset.sum_apply,ite_apply,Pi.zero_apply]
    · simp only [StageRoute.scatterTable,Pi.sub_apply,Finset.sum_apply,dite_apply,Pi.zero_apply]
  · rfl
  · funext y o d
    change StageRoute.finishTable x.rect (fun a => y a d) o = StageRoute.finishTable x.rect y o d
    simp [StageRoute.finishTable,Finset.sum_apply]

/-- The generated five-gate coefficient tables produce the exact vectors of
the native grouped predictor on every source payload tuple. -/
theorem selected_packed_lookup (h : Valid j threshold x) (tag : Fin 5)
    [Fintype ((roleRealization h).Boundary (inputBoundary tag))]
    (y : (roleRealization h).Boundary (inputBoundary tag) → x.WideIndex → x.Ground) :
    let n := inputBoundary tag
    let inp := scalarOrder (roleRealization h) n (Raw.rowCount x.m)
    let out := scalarOrder (roleRealization h) (n+1) (Raw.rowCount x.m)
    let table := matrixTable (x.modulusIndex+1) inp.count (gateMatrix x.stageParameters (x.roleFrame.gate tag n))
    let src := stripe inp (fun a => numeral (y a.1 a.2).val)
    let dst := stripe out (fun b => numeral (packedGate h tag y b.1 b.2).val)
    RegisterLookup.read table src = dst ∧ (src,dst) ∈ table := by
  simpa only [selectedGate_eq_packed] using selected_gate_lookup h tag y

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
