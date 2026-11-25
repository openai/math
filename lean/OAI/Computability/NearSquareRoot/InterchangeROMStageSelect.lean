import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyPayload
import OAI.Computability.NearSquareRoot.InterchangeROMStageTableCoverage

/-! # Feeding the verified source template to the grouped-stage coefficient compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open NearSquareRoot InterchangeROMRepair InterchangeROMStageTable InterchangeROMStage
  IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROMTable

/-- Serialize the stage parameters directly from the selected numerical template.
The `j`th query matrix is slot `1+j` of the same ground tape validated by the
repair predicate. The middle matrix and base matrix retain row-major order. -/
def stageParameters (x : Template.Data) : Parameters :=
  (x.roleFrame, x.modulusIndex+1, Raw.rowCount x.m, x.middle, x.repair.getD 0 [],
    (List.range x.m).map fun j => x.repair.getD (1+j) [])

theorem primrec_roleFrame : Primrec roleFrame :=
  (primrec_header 2).pair ((primrec_header 4).pair ((primrec_header 5).pair
    (primrec_mask.pair (primrec_row.pair primrec_col))))

theorem primrec_stageParameters : Primrec stageParameters := by
  apply primrec_roleFrame.pair
  apply (Primrec.succ.comp primrec_modulusIndex).pair
  apply (Raw.primrec_rowCount.comp (primrec_header 2)).pair
  apply primrec_middle.pair
  apply ((Primrec.list_getD []).comp primrec_repair (.const 0)).pair
  apply Primrec.list_map (Primrec.list_range.comp (primrec_header 2))
  exact ((Primrec.list_getD []).comp (primrec_repair.comp .fst)
    (Primrec.nat_add.comp (.const 1) .snd)).to₂

variable {j threshold : ℕ} {x : Template.Data}

theorem stage_minor_matrix (h : Valid j threshold x) :
    (fun i k : Fin x.rank => ((decode x.stageParameters).minor i k : x.Ground)) = x.middleMatrix := by
  funext i k
  change (((x.middle[(i.val * x.row.length)+k.val]?).getD 0 : ℕ) : x.Ground) = _
  rw [(minor_lengths h).1]
  rfl

theorem stage_base_matrix (x : Template.Data) :
    (fun i k : x.WideIndex => ((decode x.stageParameters).base i k : x.Ground)) = x.spec.base := by
  rfl

theorem stage_query_matrix (x : Template.Data) (q : Fin x.m) :
    (fun i k : x.WideIndex => ((decode x.stageParameters).query q i k : x.Ground)) = x.spec.term q := by
  funext i k
  dsimp only [decode,stageParameters]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [List.getElem_map,List.getElem_range,Option.getD_some]
  rfl

variable [Fact (x.modulusIndex+1).Prime]

/-- The typed gates computed by the selected fixed-lane matrices. -/
def selectedGate (h : Valid j threshold x) :
    (tag : Fin 5) → ((roleRealization h).Boundary (inputBoundary tag) → x.WideIndex → x.Ground) →
    (roleRealization h).Boundary (inputBoundary tag+1) → x.WideIndex → x.Ground
  | ⟨0,_⟩, y,o,d => StageRoute.partialTable x.rect (fun a => y a d) o
  | ⟨1,_⟩, y,o,d => StageRoute.mixTable x.rect (rowSel h) x.middleMatrix (fun a => y a d) o
  | ⟨2,_⟩, y,o,d => StageRoute.scatterTable x.rect (colSel h) (fun a => y a d) o
  | ⟨3,_⟩, y,o,d => StageRoute.sumQueries x.rect (mixerMap x.spec.base)
      (fun q => mixerMap (x.spec.term q)) y o d
  | ⟨4,_⟩, y,o,d => StageRoute.finishTable x.rect (fun a => y a d) o

theorem gateNative_selected (h : Valid j threshold x) (tag : Fin 5) :
    let g := decode x.stageParameters
    gateNative (roleRealization h) _ (Raw.rowCount x.m) g.minor g.base g.query tag =
      selectedGate h tag := by
  dsimp only
  fin_cases tag
  · rfl
  · funext y o d
    change StageRoute.mixTable x.rect (rowSel h)
      (fun i k : Fin x.rank => ((decode x.stageParameters).minor i k : x.Ground)) (fun a => y a d) o = _
    rw [stage_minor_matrix h]
    rfl
  · rfl
  · funext y o d
    change StageRoute.sumQueries x.rect
      (mixerMap (fun i k : x.WideIndex => ((decode x.stageParameters).base i k : x.Ground)))
      (fun q : Fin x.m => mixerMap (fun i k : x.WideIndex =>
        ((decode x.stageParameters).query q i k : x.Ground))) y o d = _
    rw [stage_base_matrix x]
    simp_rw [stage_query_matrix x]
    rfl
  · rfl

/-- Every table entry emitted from the selected transcript agrees at every
address with the native stage using its confirmed minor and ground repair ROM. -/
theorem selected_gate_lookup (h : Valid j threshold x) (tag : Fin 5)
    [Fintype ((roleRealization h).Boundary (inputBoundary tag))]
    (y : (roleRealization h).Boundary (inputBoundary tag) → x.WideIndex → x.Ground) :
    let n := inputBoundary tag
    let inp := scalarOrder (roleRealization h) n (Raw.rowCount x.m)
    let out := scalarOrder (roleRealization h) (n+1) (Raw.rowCount x.m)
    let table := matrixTable (x.modulusIndex+1) inp.count (gateMatrix x.stageParameters (x.roleFrame.gate tag n))
    let src := stripe inp (fun a => numeral (y a.1 a.2).val)
    let dst := stripe out (fun b => numeral (selectedGate h tag y b.1 b.2).val)
    RegisterLookup.read table src = dst ∧ (src,dst) ∈ table := by
  let : Fact x.stageParameters.2.1.Prime := ⟨good_prime h⟩
  have he := @frame_gate_lookup x.stageParameters (roleRealization h) inferInstance tag
    (inferInstance : Fintype ((roleRealization h).Boundary (inputBoundary tag))) y
  have native := gateNative_selected h tag
  dsimp only at native ⊢
  rw [← native]
  exact he

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
