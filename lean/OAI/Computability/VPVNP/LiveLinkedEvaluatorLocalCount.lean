import OAI.Computability.VPVNP.LiveLocalGroupCount
import OAI.Computability.VPVNP.LiveLinkedEvaluatorPhysical
import OAI.Computability.VPVNP.LiveOutsideTailCount

/-!
# Local evaluator multiplicity from the physical header memory

Every noninitial evaluator group gathers its actual incoming cut. Its outgoing
case uses the header's raw field or the canonical last sentinel. For an empty
evaluator, the first router writes the already-accepting control state and
skips preparation. Both paths include the concrete header prefix in the cap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveEvaluatorEncoding LiveEvaluatorRAM LiveHeaderDescriptors LiveHeader
open ChainAssignments LiveChain LocalCount
open scoped Fin.CommRing

variable {G : PairStages.Group} {S H : ℕ} (W : Conditions G S H)
variable (adv : CutSchedule.Bits (sizes G).advice)
variable (fits : limit G < 2^G.w) (fit : GeometryFit G (radius G))
variable (layout : LiveEvaluatorTail.Layout G.evaluator.extra (radius G) G.w (sizes G).delta)
variable (init : Code G.evaluator.extra (radius G))
variable (cuts : AllCuts (sizes G).h (sizes G).delta) (i : Fin (2^(sizes G).h))
variable (mode : physicalTag cuts (halves (sizes G).h (.inr i)) = some .tail)
variable (pad : ∀ side, LiveHeaderProgram.Fields.ValidPadding (sizes G) cuts (halves (sizes G).h (.inr i)) .tail side)
variable (tr : Prepared W adv cuts (halves (sizes G).h (.inr i)) .tail)
variable (header : LiveHeaderProgram.Output (sizes G) (headerBase G) G.g.d W.word adv cuts
  (halves (sizes G).h (.inr i)) .tail (memory tr))

/-- The checked header reports fit the resource interface used by the native
evaluator suffix, at the same burst clock as every continuation. -/
theorem headerResources : OutsideTraces.Resources tr.logs (LiveHeaderSchedule.costBound (sizes G)+4) 11 G.clock := by
  refine ⟨tr.cost, fun r hr => by have := tr.probes r hr; omega, fun r hr => ?_⟩
  exact localSegment_event_bound ((runSegment_iff ..).mp tr.run).1 r hr

variable (call : max 11 (G.w+4) ≤ H)
variable (budget : LiveHeaderSchedule.costBound (sizes G)+4 + 2*OutsideTailCount.routeCost G.w (radius G) +
  OutsideTailCount.transitionCost (radius G) ≤ S*H)
include fits fit mode pad header call budget

/-- Full physical post-header count for every noninitial evaluator group. -/
theorem nonfirstPhysicalCount (nonfirst : 0 < i.val) :
    Nat.card (remaining tr) = tailCount G.evaluator layout init (liveCutEquiv (sizes G).h (sizes G).delta cuts).2 i := by
  obtain ⟨o⟩ := physicalOutput G header layout init mode fits (pad .right)
  obtain ⟨flag,raw,img,value⟩ := physicalIncoming G header layout init mode fits nonfirst (pad .left)
  let F := gatherFit G fits layout.symbolWidth false
  let frame := gatheredOutputFrame G (addresses G fits) F (memory tr) raw
  exact OutsideTailCount.nonfirstCount_capped G layout init _ i (memory tr) fit tr.tag flag F raw img
    (Or.inl (addresses G fits).leftStart) value (o.transport frame) tr.logs (headerResources W adv cuts i tr) (by simpa using call) budget

/-- With no evaluator rows the canonical initial code is the accepting halt.
No prefix-copy, skeleton or scatter stage is entered at the middle cut. -/
theorem emptyFirstPhysicalCount (first : i.val = 0) (empty : G.evaluator.extra = 0) (initEq : init = .accepted) :
    Nat.card (remaining tr) = tailCount G.evaluator layout init (liveCutEquiv (sizes G).h (sizes G).delta cuts).2 i := by
  obtain ⟨o⟩ := physicalOutput G header layout init mode fits (pad .right)
  have he := headerBelowOld G fits
  have hf := HeaderFlags.firstTail G.constants G.g G.lit (he.trans_lt (G.transitionPub 1).isLt) header
  change memory tr _ = (if 2^(sizes G).h+i.val+1 = 2^(sizes G).h+1 then 1 else 0) at hf
  rw [ite_eq_left (by omega)] at hf
  have hclk := fit.gatherClock
  rw [Nat.card_congr (putHandoff G false fit.prep.width (by omega) (memory tr) tr.tag hf _).symm]
  let m := putMemory G false (memory tr)
  have tag : G.tagged Stage.last m := by
    have hn : EvaluatorSentinel.destination G false = Stage.last := by simp [EvaluatorSentinel.destination,empty]
    unfold m putMemory EvaluatorSentinel.transferred
    rw [hn]; exact tagged_retag ..
  have old (c : Code G.evaluator.extra (radius G)) : LiveEvaluatorTail.boundary layout init
      (liveCutEquiv (sizes G).h (sizes G).delta cuts).2 i.castSucc = some c ↔ ConfigAt m (G.transitionPub 1) c := by
    have hi : i.castSucc = 0 := Fin.ext first
    rw [hi, LiveEvaluatorTail.boundary_zero, initEq, Option.some.injEq, eq_comm]
    exact (empty_initial_image G (memory tr) empty fit (fun j => header.fresh_after_limit _ (he.trans (Nat.le_add_right ..))) c).symm
  let o' := o.transport (putInitialFrame G (addresses G fits) (memory tr))
  have hp := OutsideTailStages.putRoute G false
  have hp' : OutsideTraces.Resources (putLogs G false) 8 4 (OutsideTailStages.instructionBound G) :=
    ⟨hp.cost,fun r hr => (putLogs_calls G false r hr).le,hp.work⟩
  have pre := (headerResources W adv cuts i tr).append hp'
  have hc := OutsideTailCount.lastCount_capped (S := S) (H := H) G layout init _ i m fit tag old o'
    (tr.logs++putLogs G false) pre (by simpa using call) ?budget
  · simpa only [List.append_assoc] using hc
  case budget =>
    have hk : 1 ≤ fieldWords (radius G) := by unfold fieldWords; omega
    have hlow := Nat.mul_le_mul_right (G.w+4) hk
    simp only [Nat.one_mul] at hlow
    unfold OutsideTailCount.routeCost at budget ⊢
    omega

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
