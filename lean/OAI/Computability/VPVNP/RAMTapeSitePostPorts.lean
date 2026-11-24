import OAI.Computability.VPVNP.RAMTapeSitePostRecords
import OAI.Computability.VPVNP.RAMTapeSiteProcessorPorts

/-!
# Physical connection from the call loop to the local memory pass

The sorter reads the call loop's completed record buffer and the shared
guard's two predecessor records. Its address, width, slot count and remaining
incident tape use the original parser registers. All sorting scratch has its
own labels.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM LiveProgram RAMSerialization RAMBoundary
variable {k : ℕ} (r : ℕ) (expr : Fin k → PublicExpr)

/-- Connect sorting input to the call loop’s output, reuse the parsed fields and guard records,
and assign separate ports to sorting scratch. -/
def postPorts (p : SitePost.Port) : Port r expr :=
  if p = SitePost.blockPort then native r expr (.record .output) else
  if p = SitePost.addressPort then pub r expr ProcessorPublic.addressPort else
  if p = SitePost.incidentPort then pub r expr ProcessorPublic.incidentPort else
  if p = SitePost.widthPort then pub r expr ProcessorPublic.widthPort else
  if p = SitePost.slotsPort then pub r expr (.inl SiteSetup.slotsPort) else
  if p = SitePost.addressWidthPort then pub r expr ProcessorPublic.addressWidthPort else
  if p = SitePost.previousPort then cut r expr (.inr (.record .receive)) else
  if p = SitePost.sentPort then cut r expr (.inr (.record .send)) else .inr (.inr p)

private def cutPost (p : SiteCutBank.Port) : Option SitePost.Port :=
  if p = .inl ProcessorPublic.addressPort then some SitePost.addressPort else
  if p = .inl ProcessorPublic.incidentPort then some SitePost.incidentPort else
  if p = .inl ProcessorPublic.widthPort then some SitePost.widthPort else
  if p = .inl (.inl SiteSetup.slotsPort) then some SitePost.slotsPort else
  if p = .inl ProcessorPublic.addressWidthPort then some SitePost.addressWidthPort else
  if p = .inr (.record .receive) then some SitePost.previousPort else
  if p = .inr (.record .send) then some SitePost.sentPort else none

private def postView : Port r expr → Option SitePost.Port
  | .inl (.inl (.record .output)) => some SitePost.blockPort
  | .inl (.inr (.inl p)) => cutPost (.inl p)
  | .inr (.inl i) => cutPost (.inr i)
  | .inr (.inr p) => some p
  | _ => none

private theorem postView_post (p : SitePost.Port) : postView r expr (postPorts r expr p) = some p := by
  unfold postPorts
  repeat' first | split <;> rename_i he | subst p <;> rfl
  all_goals rfl

theorem postPorts_injective : Function.Injective (postPorts r expr) := by
  intro p q he
  have := congrArg (postView r expr) he
  simpa only [postView_post, Option.some.injEq] using this

private theorem postView_call (p : SiteProcessor.Port r k) :
    postView r expr (callPorts r expr p) =
      if p = .record .output then some SitePost.blockPort else none := by
  cases p with
  | isa i => cases i <;> rfl
  | credit i => cases i with
    | budget j => cases j <;> rfl
    | _ => rfl
  | test i => cases i with
    | word j => cases j <;> rfl
    | bit j => cases j <;> rfl
    | _ => rfl
  | record i => cases i with
    | field j => fin_cases j <;> rfl
    | _ => rfl
  | scratch i => rfl

theorem postPorts_eq_call_iff (j : SitePost.Port) (i : SiteProcessor.Port r k) :
    postPorts r expr j = callPorts r expr i ↔ j = SitePost.blockPort ∧ i = .record .output := by
  constructor
  · intro h
    have eq := congrArg (postView r expr) h
    rw [postView_post, postView_call] at eq
    split at eq <;> simp_all
  · rintro ⟨rfl,rfl⟩; rfl

theorem postPorts_ne_budget (j : SitePost.Port) : postPorts r expr j ≠ pub r expr ProcessorPublic.budgetPort := by
  intro h
  have he := congrArg (postView r expr) h
  rw [postView_post] at he
  have impossible : some j = none := he
  cases impossible

/-- A physical call replaces only the occupied input block of the sorter. -/
theorem installCall_post {portsInj : Function.Injective (callPorts r expr)}
    (base : Stacks (Port r expr)) (out : Stacks (SiteProcessor.Port r k)) :
    installStacks (callPorts r expr) base out ∘ postPorts r expr =
      Function.update (base ∘ postPorts r expr) SitePost.blockPort (out (.record .output)) := by
  funext j
  by_cases he : j = SitePost.blockPort
  · subst j; simp only [Function.update_self, Function.comp_apply]
    exact installStacks_at portsInj base out (.record .output)
  · rw [Function.update_of_ne he]
    exact installStacks_outside _ _ (fun i h => he ((postPorts_eq_call_iff r expr j i).mp h.symm).1)

/-- Run the complete local sorting and memory-checking pass on the processor’s connected ports. -/
def post (r : ℕ) (expr : Fin k → PublicExpr) : FiniteRoutine (Port r expr) :=
  SitePost.complete.onPorts (postPorts r expr)

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
