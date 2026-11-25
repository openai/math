import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyPayload

/-! # Recursive charges of the selected, decoded rectangle stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data
open InterchangeROMStage InterchangeROMRepair StageScript

variable {j threshold : ℕ} {x : Data}

/-- Price of the actual sequence loaded from an oriented chart-table operand. -/
def wordPrice (h : Valid j threshold x) (op : (roleRealization h).NativeMove) :=
  Opcode.price (lookup x.chart ((roleRealization h).operand op))

noncomputable def predictorStage (h : Valid j threshold x) [Fact (x.modulusIndex+1).Prime] :
    Program (roleRealization h).NativeMove (x.WideIndex → x.Ground) (Fin x.labels) (Fin x.labels) :=
  stageBank x.rect (rowSel h) (colSel h) x.spec x.middleMatrix

/-- The four predictors and the four check-bank spectral sweeps together fit
the numerical recursive charge stored in the template. -/
theorem predictor_charge (h : Valid j threshold x) [Fact (x.modulusIndex+1).Prime] :
    (4*Sizes.pencilOrder x.m) * (Raw.rowCount x.m * cost (wordPrice h) (predictorStage h)) +
      4*x.m*Raw.checkCount x.m*x.labels ≤ x.calls := by
  let A₀ (_ : Fin (4*Sizes.pencilOrder x.m)) := mixerMap x.spec.base
  let A (_ : Fin (4*Sizes.pencilOrder x.m)) (q : Fin x.m) := mixerMap (x.spec.term q)
  have charge := TemplateCost.bound_catalog (K:=x.Ground) (E:=x.WideIndex → x.Ground) (catalog h) (radix_gt_one h) (catalog_valid h)
    (rowSel h) (colSel h) x.middleMatrix (incident_degree h) A₀ A
  have eq : wordPrice h =
      fun op => ((AddressROM.instructions (catalog h) op).map IntegerMultiplication.Port.Lag.prices).sum :=
    funext (lookup_price h)
  simp only [eq,predictorStage,stageBank,A₀,A,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,Raw.rowCount,Raw.checkCount,calls] at charge ⊢
  convert charge using 1
  simp only [StageRoute.stage,StageRoute.partials,StageRoute.mix,StageRoute.scatter,StageRoute.collect,
    cost_seq,cost_route,cost_table]
  rfl

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
