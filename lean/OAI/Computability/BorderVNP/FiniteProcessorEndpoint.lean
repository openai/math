import OAI.Computability.BorderVNP.FiniteProcessorLoopClose
import OAI.Computability.BorderVNP.FiniteNeutralReplay
import OAI.Computability.BorderVNP.TeamSiteEndpointLive

/-! # Field-augmented endpoint decoder, live loop and sender -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamSite.Endpoint TeamPrivateFragment TeamLocalClock TeamTapeHandoff
open BurstRAM (Word)
open RAMTape.PublicExprMachine
open private rename_acc from OAI.Computability.BorderVNP.FiniteProcessorWeightSegments

variable {Q Γ : Type} {p r k a m g w : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Only the instruction loop can contribute an endpoint field factor. -/
noncomputable def endpointFactor {P : TeamOpcode.Program p r k a} (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) : Endpoint.Label P Q m g → F
  | .loop _ q => loopFactor lib weights q
  | _ => 1

/-- Actual finite-control endpoint with its accumulator. -/
noncomputable def endpointCode (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a) :=
  FieldStack.productCode (Endpoint.code P lib) (endpointFactor lib weights)

private def closing {P : TeamOpcode.Program p r k a} : Endpoint.Label P Q m g → Prop
  | .loop _ (.close ..) | .finish .. | .done .. | .invalid => True
  | _ => False

private theorem closing_next (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (q : Endpoint.Label P Q m g) (hq : closing q) : FieldStack.AllNext closing (Endpoint.code P lib q) := by
  cases q with
  | startup _ _ => exact hq.elim
  | loop last q => cases q <;> first | exact hq.elim | trivial
  | finish sg q =>
    cases q <;> first
      | exact FieldStack.allNext_rename _ _ _ _ (fun _ => trivial)
      | (rename_i ok; cases ok <;> trivial)
  | done _ | invalid => trivial

omit [Fintype F] in
private theorem closing_neutral (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (q : Endpoint.Label P Q m g) (h : closing q) : endpointFactor lib weights q = 1 := by
  cases q with
  | loop last q => cases q <;> first | rfl | exact h.elim
  | _ => rfl

/-- All physical sender and closing rows preserve the field element. -/
theorem close_lift (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (acc : F) {last sg live bits s q tail out n}
    (h : StackRuns (replay (Endpoint.code P lib)) n (.loop last (.close sg live),bits) s (q,tail) out) :
    StackRuns (replay (endpointCode P lib weights)) n ((.loop last (.close sg live),Fintype.equivFin F acc),bits) s
      ((q,Fintype.equivFin F acc),tail) out :=
  FieldStack.neutral_forward _ _ closing acc (closing_neutral P lib weights) (closing_next P lib) h trivial

/-- The physically checked predecessor frame is decoded on the original stacks,
and the field control enters its chosen next phase at the same time. -/
theorem predecessor_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (acc : F) (last : Bool) (fits : p ≤ 2^w) (pub : Fin k → Word w)
    (f : Frame w r) (H limit cap : Word w) (suffix bits : List Bool) (base : Stacks (Endpoint.Port r k (m*g)))
    (ready : base ∘ Endpoint.startup = Startup.input pub H limit cap (f.bits++suffix)) :
    ∃ t ≤ Startup.budget r w+1, StackRuns (replay (endpointCode P lib weights)) t
      ((.startup last (Startup.entry p r),Fintype.equivFin F acc),bits) base
      ((afterStartup last (Startup.result p f limit),Fintype.equivFin F acc),bits)
      (installStacks Endpoint.startup base (Startup.decoded pub f H (Startup.remaining p f limit) cap suffix)) := by
  obtain ⟨t,ht,hr⟩ := Startup.run p fits pub f H limit cap suffix
  let label := fun z => (Endpoint.Label.startup (P := P) (Q := Q) (m := m) (g := g) last z,Fintype.equivFin F acc)
  have lift := hr.lift Endpoint.startup startup_injective label base (target := endpointCode P lib weights) (by
    intro z hz
    have eq : Endpoint.code P lib (.startup last z) = (Startup.code p r k z).rename Endpoint.startup (.startup last) := by
      cases z with
      | done b => cases b <;> contradiction
      | _ => rfl
    simp only [endpointCode,FieldStack.productCode,label,endpointFactor,Equiv.symm_apply_apply,mul_one,eq,rename_acc])
  rw [installStacks_eq startup_injective base _ (congrFun ready)] at lift
  let b := installStacks Endpoint.startup base (Startup.decoded pub f H (Startup.remaining p f limit) cap suffix)
  have step : StackRuns (endpointCode P lib weights) 1 (label (.done (Startup.result p f limit))) b
      (afterStartup last (Startup.result p f limit),Fintype.equivFin F acc) b := by
    apply StackRuns.cons _ (StackRuns.nil ..)
    exact .goto (by simp [endpointCode,FieldStack.productCode,Endpoint.code,label,endpointFactor,StackOp.rename])
  exact ⟨_,by omega,replay_segment (lift.trans step) bits⟩

/-- Install an entire weighted loop run in the physical endpoint, preserving both
accumulators, every choice bit and all non-loop stacks. -/
theorem loop_segment (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (last : Bool) {t q acc bits s q' v rest out}
    (hr : StackRuns (replay (loopCode P lib weights)) t ((q,acc),bits) s ((q',v),rest) out)
    (base : Stacks (Endpoint.Port r k (m*g))) (ready : base ∘ Endpoint.Port.site = s) :
    StackRuns (replay (endpointCode P lib weights)) t ((.loop last q,acc),bits) base
      ((.loop last q',v),rest) (installStacks Endpoint.Port.site base out) := by
  let label := fun z : FieldStack.ProductState (Loop.Label P Q m g) F => (Endpoint.Label.loop last z.1,z.2)
  have r := TeamLink.replay_lift hr (endpointCode P lib weights) Endpoint.Port.site (fun _ _ he => Endpoint.Port.site.inj he)
    label base (by
    rintro ⟨z,i⟩ hz
    have eq : Endpoint.code P lib (.loop last z) = (Loop.code P lib z).rename Endpoint.Port.site (.loop last) := by
      cases z <;> first | rfl | simp [loopCode,FieldStack.productCode,Loop.code,StackOp.returns] at hz
    simp only [label,endpointCode,loopCode,FieldStack.productCode,endpointFactor,eq]
    cases Loop.code P lib z <;> rfl)
  rwa [installStacks_eq (fun _ _ he => Endpoint.Port.site.inj he) base s (congrFun ready)] at r

end FieldProcessor

end BorderVNP
end Computability
end OAI
