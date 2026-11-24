import OAI.Computability.VPVNP.LiveLinkedEvaluatorTransport
import OAI.Computability.VPVNP.LiveLinkedEvaluatorCut
import OAI.Computability.VPVNP.LivePhysicalRoutes
import OAI.Computability.VPVNP.LiveHeaderOutputFrame

/-!
# Evaluator inputs and outputs from the actual physical header

The live header parser supplies the mode, the two router flags, the raw cut
field and the zero-default outgoing endpoint. This proof reconstructs the
outgoing case at every evaluator group and the incoming field at every
noninitial group, without assuming well-formed configuration words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveConfigGather LiveEvaluatorEncoding LiveEvaluatorRAM LiveHeaderDescriptors
open ChainAssignments LiveHeader
open LiveHeaderSchedule (Sizes configBase)
open scoped Fin.CommRing

variable (G : PairStages.Group)
/-- The evaluated header dimensions used to recover the evaluator routes from the physical cut. -/
abbrev sizes := Header.sizes G.constants G.g
/-- The physical header workspace base for the current evaluator group. -/
abbrev headerBase := Header.base G.g
/-- The first address past the group's live-header buffers. -/
abbrev headerEnd := LiveHeaderSchedule.limit (sizes G) (headerBase G)

theorem headerBelowOld (fits : limit G < 2^G.w) : headerEnd G ≤ (G.transitionPub 1).val := by
  let old := (Layout.oldState G.constants).eval G.g
  have h : headerEnd G ≤ old := by change headerEnd G ≤ headerEnd G+21+G.constants.labels.eval G.g; omega
  have fit : old < 2^G.w := by
    change old+G.constants.configWords.eval G.g+G.constants.configWords.eval G.g+5+24+
      G.constants.prefixCapacity.eval G.g+G.constants.labels.eval G.g < 2^G.w at fits; omega
  have he : (G.transitionPub 1).val = old := Nat.mod_eq_of_lt fit
  rwa [he]

theorem physicalSource (fits : limit G < 2^G.w) (out : Bool) :
    (cutSource G out).val = configBase (sizes G) (headerBase G) (if out then Side.right else Side.left) := by
  have he := headerBelowOld G fits
  have hb := (G.transitionPub 1).isLt
  have left : configBase (sizes G) (headerBase G) .left ≤ headerEnd G := by
    change configBase (sizes G) (headerBase G) .left ≤ configBase (sizes G) (headerBase G) .left+
      (sizes G).config+(sizes G).config; omega
  have right : configBase (sizes G) (headerBase G) .right ≤ headerEnd G := Nat.le_add_right ..
  cases out with
  | false => exact Nat.mod_eq_of_lt (show configBase (sizes G) (headerBase G) .left < 2^G.w by omega)
  | true => exact Nat.mod_eq_of_lt (show configBase (sizes G) (headerBase G) .right < 2^G.w by omega)

variable {hw : 4 ≤ G.w} {advice : CutSchedule.Bits (sizes G).advice}
variable {cuts : AllCuts (sizes G).h (sizes G).delta} {i : Fin (2^(sizes G).h)} {m : Memory G.w}
variable (header : LiveHeaderProgram.Output (sizes G) (headerBase G) G.g.d hw advice cuts
  (halves (sizes G).h (.inr i)) .tail m)
variable (layout : LiveEvaluatorTail.Layout G.evaluator.extra (radius G) G.w (sizes G).delta)
variable (init : Code G.evaluator.extra (radius G))
variable (mode : physicalTag cuts (halves (sizes G).h (.inr i)) = some .tail)
include header mode

/-- The actual header supplies every outgoing constructor input. A last cut
uses the zero-default memory beyond the header allocation. -/
theorem physicalOutput (fits : limit G < 2^G.w)
    (pad : LiveHeaderProgram.Fields.ValidPadding (sizes G) cuts (halves (sizes G).h (.inr i)) .tail .right) :
    Nonempty (Output G m (LiveEvaluatorTail.boundary layout init (liveCutEquiv (sizes G).h (sizes G).delta cuts).2 i.succ)) := by
  let a := addresses G fits
  have he := headerBelowOld G fits
  have hf := HeaderFlags.last G.constants G.g G.lit (he.trans_lt (G.transitionPub 1).isLt) header
  change m _ = (if 2^(sizes G).h+i.val+1 = 2^((sizes G).h+1) then 1 else 0) at hf
  rw [pow_succ] at hf
  by_cases last : i.val+1 = 2^(sizes G).h
  · rw [ite_eq_left (by omega)] at hf
    refine ⟨.final hf (fun j => header.fresh_after_limit _ (by change headerEnd G ≤ _; have := a.oldEnd; omega))
      (Or.inl (by have := a.leftStart; have := a.rightStart; have := a.sourceEnd; have := a.oldEnd; omega)) ?_⟩
    have hi : i.succ = Fin.last (2^(sizes G).h) := Fin.ext last
    rw [hi, LiveEvaluatorTail.boundary_last]
  · have interior : i.val+1 < 2^(sizes G).h := by have := i.isLt; omega
    rw [ite_eq_right (by omega)] at hf
    obtain ⟨raw,img,value⟩ := header.tail_outgoing layout init rfl mode pad (physicalSource G fits true) interior
    exact ⟨.cut (gatherFit G fits layout.symbolWidth true) raw hf img
      (Or.inl (by have := a.leftStart; have := a.rightStart; change G.addr.val < (cutSource G true).val; omega))
      layout.stateWidth value⟩

/-- The incoming zero-flag case recovers its actual raw array from the left
incident cut. The semantic boundary includes its mode and padding tests. -/
theorem physicalIncoming (fits : limit G < 2^G.w) (nonfirst : 0 < i.val)
    (pad : LiveHeaderProgram.Fields.ValidPadding (sizes G) cuts (halves (sizes G).h (.inr i)) .tail .left) :
    m ((Router.firstTail.data G.g G.lit) 0).val = 0 ∧
    ∃ raw : Fin (k G*G.w) → Bool, ArrayBitImage m (cutSource G false) raw ∧
      LiveEvaluatorTail.boundary layout init (liveCutEquiv (sizes G).h (sizes G).delta cuts).2 i.castSucc =
        (format layout.symbolWidth layout.stateWidth).decode raw := by
  have he := headerBelowOld G fits
  have hf := HeaderFlags.firstTail G.constants G.g G.lit (he.trans_lt (G.transitionPub 1).isLt) header
  change m _ = (if 2^(sizes G).h+i.val+1 = 2^(sizes G).h+1 then 1 else 0) at hf
  rw [ite_eq_right (by omega)] at hf
  exact ⟨hf, header.tail_incoming layout init rfl mode pad (physicalSource G fits false) nonfirst⟩

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
