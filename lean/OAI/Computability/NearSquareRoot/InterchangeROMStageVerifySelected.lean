import OAI.Computability.NearSquareRoot.InterchangeROMStageSelect
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyTrajectory

/-! # Twelve boundary states of the selected native pencil -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.Template.Data

open InterchangeROMStage InterchangeROMStageTable InterchangeROMRepair InterchangeSpectralFibre
  StageScript IntegerMultiplication.Strip.Dims

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D : Type}
  [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

def stageStates (h : Valid j threshold x) (v : x.Wide P G S f D) (n : ℕ) :
    (roleRealization h).Boundary n → x.Address P G S f × D → x.WideIndex → x.Ground :=
  let coeff := decode x.stageParameters
  (roleRealization h).states _ (Raw.rowCount x.m) coeff.minor coeff.base coeff.query
    (withPayload D (nativeLayout h P G S f)).perm v n

@[simp] theorem stageStates_initial (h : Valid j threshold x) (v : x.Wide P G S f D) : stageStates h v 0 = v :=
  rfl

theorem stageStates_route (h : Valid j threshold x) (v : x.Wide P G S f D) (k : Fin 6)
    (z : (roleRealization h).Boundary (Frame.Realization.routePos k+1)) (a : x.Address P G S f × D) :
    let r := roleRealization h
    let π := (withPayload D (nativeLayout h P G S f)).perm (I:=r.sel true) (J:=r.sel false)
    stageStates h v (Frame.Realization.routePos k+1) z a =
      stageStates h v (Frame.Realization.routePos k) (r.srcAt k z) ((π (r.moveAt k z)).symm a) :=
  (roleRealization h).states_route ..

theorem stageStates_gate (h : Valid j threshold x) (v : x.Wide P G S f D) (tag : Fin 5)
    (u : (roleRealization h).Boundary (inputBoundary tag+1)) (a : x.Address P G S f × D) :
    stageStates h v (inputBoundary tag+1) u a =
      selectedGate h tag (fun k => stageStates h v (inputBoundary tag) k a) u := by
  rw [← gateNative_selected h]
  exact (roleRealization h).states_gate ..

/-- The compiled finite role trajectory ends at the exact predictor stage used
for the four invocations in the checked repair schedule. -/
theorem stageStates_stagePayload (h : Valid j threshold x) (v : x.Wide P G S f D) :
    stageStates h v 11 = stagePayload h v := by
  refine ((roleRealization h).states_final _ (Raw.rowCount x.m)
    (decode x.stageParameters).minor (decode x.stageParameters).base (decode x.stageParameters).query
    (withPayload D (nativeLayout h P G S f)).perm v).trans ?_
  change eval _ (StageRoute.stage x.rect (rowSel h) (colSel h)
    (fun i k : Fin x.rank => ((decode x.stageParameters).minor i k : x.Ground))
    (mixerMap (fun i k : x.WideIndex => ((decode x.stageParameters).base i k : x.Ground)))
    (fun q : Fin x.m => mixerMap (fun i k : x.WideIndex => ((decode x.stageParameters).query q i k : x.Ground))))
      v = _
  rw [stage_minor_matrix h,stage_base_matrix x]
  simp_rw [stage_query_matrix x]
  rfl

end Interchange.Template.Data

end

end NearSquareRoot
end Computability
end OAI
