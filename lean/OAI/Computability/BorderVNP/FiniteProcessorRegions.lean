import OAI.Computability.BorderVNP.FiniteProcessorEndpointLive
import OAI.Computability.BorderVNP.TeamSiteProcessorRow

/-! # Neutral raw-input and final-sorting phases of the finite-field processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamPrivateFragment
open FieldStack (AllNext allNext_rename)
variable {Q Γ : Type} {p r k a m g : ℕ} {F : Type*} [Field F] [Fintype F]

private theorem allNext_map {K L S T : Type} (op : StackOp K S) (ports : K → L) (labels : S → T) (A : T → Prop) :
    AllNext A (op.rename ports labels) ↔ AllNext (A ∘ labels) op := by cases op <;> rfl

private def startupRegion {P : TeamOpcode.Program p r k a} : Processor.Label P Q m g → Prop
  | .block (.startup ..) => True
  | .block _ | .close .. | .sort .. | .reject => False
  | _ => True

private theorem startup_closed (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (q : Processor.Label P Q m g) (h : ¬ startupRegion q) :
    AllNext (fun z => ¬startupRegion z) (Processor.code P lib q) := by
  cases q with
  | block q =>
    cases q with
    | startup _ _ => exact (h trivial).elim
    | loop last q =>
      simp only [Processor.code,allNext_map]
      cases q <;> simp only [Endpoint.code] <;> first
        | exact allNext_rename _ _ _ _ (fun _ => id)
        | exact id
    | finish sg q =>
      simp only [Processor.code,allNext_map]
      cases q <;> simp only [Endpoint.code] <;> first
        | exact allNext_rename _ _ _ _ (fun _ => id)
        | (rename_i ok; cases ok <;> exact id)
    | done _ => exact id
    | invalid => trivial
  | close _ _ => apply allNext_rename; intro z; cases z <;> exact id
  | sort _ _ => exact allNext_rename _ _ _ _ (fun _ => id)
  | reject => trivial
  | _ => exact (h trivial).elim

/-- The raw-input prelude cannot visit a private call before reaching the
startup decoder. Its original concrete run has the very same accumulator. -/
theorem prelude_lift (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (acc : F) {last s out n}
    (h : StackRuns (Processor.code P lib) n Processor.start s (Processor.beginBlock last) out) (bits : List Bool) :
    StackRuns (replay (code P lib weights)) n ((Processor.start,Fintype.equivFin F acc),bits) s
      ((Processor.beginBlock last,Fintype.equivFin F acc),bits) out := by
  apply FieldStack.neutral_backward _ _ startupRegion acc _ (startup_closed P lib) (replay_segment h bits) trivial
  intro q hq
  cases q with
  | block q => cases q <;> first | rfl | exact hq.elim
  | _ => rfl

private def sortRegion {P : TeamOpcode.Program p r k a} : Processor.Label P Q m g → Prop
  | .block (.done _) | .close .. | .sort .. | .reject => True
  | _ => False

/-- Once the endpoint has returned, the complete physical record closure and both
sorting lanes keep their actual elapsed time, checks and field element. -/
theorem sorter_lift (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (acc : F) {sg s q out bits rest n}
    (h : StackRuns (replay (Processor.code P lib)) n (.block (.done sg),bits) s (q,rest) out) :
    StackRuns (replay (code P lib weights)) n ((.block (.done sg),Fintype.equivFin F acc),bits) s
      ((q,Fintype.equivFin F acc),rest) out := by
  apply FieldStack.neutral_forward _ _ sortRegion acc _ _ h trivial
  · intro z hz
    cases z with
    | block z => cases z <;> first | rfl | exact hz.elim
    | _ => rfl
  · intro z hz
    cases z with
    | block z => cases z <;> first | exact hz.elim | trivial
    | close _ _ => apply allNext_rename; intro b; cases b <;> trivial
    | sort _ _ => exact allNext_rename _ _ _ _ (fun _ => trivial)
    | reject => trivial
    | _ => exact hz.elim

/-- Install the field-weighted endpoint at the real frame and site ports, preserving
the field product through its physical ingress and egress. -/
theorem endpoint_replay (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    {t q acc bits localBank q' acc' rest out}
    (h : StackRuns (replay (endpointCode P lib weights)) t ((q,acc),bits) localBank ((q',acc'),rest) out)
    (s : Stacks (TeamSite.Layout.Port r k (m*g))) (ready : s ∘ Processor.endpoint = localBank) :
    StackRuns (replay (code P lib weights)) t ((.block q,acc),bits) s ((.block q',acc'),rest)
      (installStacks Processor.endpoint s out) := by
  let label := fun z : FieldStack.ProductState (Endpoint.Label P Q m g) F => (Processor.Label.block z.1,z.2)
  have lift := TeamLink.replay_lift h (code P lib weights) Processor.endpoint Processor.endpoint_injective label s (by
    rintro ⟨z,i⟩ hz
    have eq : Processor.code P lib (.block z) = (Endpoint.code P lib z).rename Processor.endpoint .block := by
      cases z <;> first | rfl | simp [endpointCode,FieldStack.productCode,Endpoint.code,StackOp.returns] at hz
    have hf : factor lib weights (Processor.Label.block z) = endpointFactor lib weights z := by
      cases z with
      | loop _ z => cases z <;> rfl
      | _ => rfl
    simp only [label,code,endpointCode,FieldStack.productCode,hf,eq]
    cases Endpoint.code P lib z <;> rfl)
  rwa [installStacks_eq Processor.endpoint_injective s localBank (congrFun ready)] at lift

end FieldProcessor

end BorderVNP
end Computability
end OAI
