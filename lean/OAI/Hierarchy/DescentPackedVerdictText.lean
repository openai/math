import OAI.Hierarchy.DescentPackedEpochFold
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! Names used by the score scans and final decision in the native epoch fold. -/
namespace Hierarchy.DescentPackedEpochFold
open DescentPackedProfileValidity DescentTerminalEpochFlags DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM DescriptorExpr
noncomputable section
variable {A : Type}

private theorem step_names (w previous current exterior dest : ℕ) :
    names (DescentTerminalEpochFlags.step w previous current exterior dest)=123 := by
  rw [DescentTerminalEpochFlags.step,names_scan]; rfl

private theorem score_names (b : Banks) (w grain seats dest : ℕ) :
    names (proc b w grain seats dest)=343 := by
  have check : (checkExpr b grain).work=64 := rfl
  simp only [proc,SumScores.procedure,names,PhysicalInputPhases.writing,Term.labels_eq,SumScores.step_binds,check]

theorem fold_names (w previous final : ℕ) (ss : List (Stage A)) :
    names (fold w previous final ss)=123+466*ss.length := by
  induction ss generalizing previous with
  | nil => exact step_names w previous previous previous final
  | cons s ss ih =>
    rw [fold,single,names_seq,names_seq,score_names,step_names,ih,List.length_cons]
    omega

theorem fold_charge_le (w previous final : ℕ) (ss : List (Stage A)) :
    bill previous final ss+7*names (fold w previous final ss)+1 ≤ 16*bill previous final ss := by
  rw [fold_names,bill_eq]
  omega

end
end Hierarchy.DescentPackedEpochFold

end OAI
