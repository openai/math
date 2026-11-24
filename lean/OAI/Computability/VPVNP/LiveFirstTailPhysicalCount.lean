import OAI.Computability.VPVNP.LiveFirstTailCount
import OAI.Computability.VPVNP.LiveFirstTailHeader
import OAI.Computability.VPVNP.LiveLinkedEvaluatorLocalCount

/-!
# The first evaluator group on the native distributed memory

At the midpoint the incoming exponent field is the final counter vector of
the pair half. The ordinal advice reindexes that vector into the evaluator's
formal input order. The live program packs the advice, copies its exact raw
prefix, generates the runtime fields, and scatters the exponent bits before
the first transition.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveEvaluatorEncoding LiveEvaluatorRAM LiveHeaderDescriptors LiveHeader
open ChainAssignments LiveChain LocalCount LiveEvaluatorAdviceBanks
open OutsideTailStages OutsideTailCount
open scoped Fin.CommRing

variable (G : Group)

/-- The evaluator starts on the raw prefix followed immediately by its
runtime fields in formal label order. -/
def midpointInitial (raw : List Bool)
    (perm : Equiv.Perm (Fin (FirstTailHeader.labelCount G)))
    (dense : Fin (FirstTailHeader.labelCount G) → ℕ) : Code G.evaluator.extra (radius G) :=
  LiveEvaluatorTail.initialCode (radius G) (UniversalMachine.initial G.evaluator
    (raw ++ EvaluatorProgramRawInput.runtime
      (fun a => Fin.ofNat (2^(FirstTailHeader.exponentWidth G)) (dense (perm.symm a)))))

/-- Count on the actual post-header memory for a nonempty evaluator at the
first tail group, under the cap on the entire physical group. -/
theorem nonemptyFirstPhysicalCount {S H padding : ℕ}
    (W : Conditions G S H) (adv : CutSchedule.Bits (sizes G).advice)
    (fits : limit G < 2^G.w) (fit : GeometryFit G (radius G))
    (expFit : 1+FirstTailHeader.labelCount G*FirstTailHeader.exponentWidth G ≤ (sizes G).delta)
    (layout : LiveEvaluatorTail.Layout G.evaluator.extra (radius G) G.w (sizes G).delta)
    (raw : List Bool) (perm : Equiv.Perm (Fin (FirstTailHeader.labelCount G)))
    (values : Fin (FirstTailHeader.labelCount G) → Word (Nat.clog 2 (FirstTailHeader.labelCount G)))
    (ordinal : ∀ a, (values a).val = (perm a).val)
    (capacity : G.w + G.constants.prefixCapacity.eval G.g +
      FirstTailHeader.labelCount G * Nat.clog 2 (FirstTailHeader.labelCount G) ≤ (sizes G).advice)
    (rawFits : raw.length ≤ G.constants.prefixCapacity.eval G.g)
    (literal : List.ofFn adv = distribution G.w (G.constants.prefixCapacity.eval G.g) raw values padding)
    (space : raw.length + (2*(FirstTailHeader.labelCount G*FirstTailHeader.exponentWidth G)+
      6*FirstTailHeader.exponentWidth G+4) ≤ radius G+1)
    (running : G.evaluator.extra ≠ 0)
    (cuts : AllCuts (sizes G).h (sizes G).delta) (i : Fin (2^(sizes G).h)) (first : i.val = 0)
    (mode : physicalTag cuts (halves (sizes G).h (.inr i)) = some .tail)
    (pad : LiveHeaderProgram.Fields.ValidPadding (sizes G) cuts (halves (sizes G).h (.inr i)) .tail .right)
    (tr : Prepared W adv cuts (halves (sizes G).h (.inr i)) .tail)
    (header : LiveHeaderProgram.Output (sizes G) (headerBase G) G.g.d W.word adv cuts
      (halves (sizes G).h (.inr i)) .tail (memory tr))
    (hcall : callBound G.w ≤ H)
    (budget : LiveHeaderSchedule.costBound (sizes G)+4+8+packWork (params G raw.length)+
      inputWork (params G raw.length)+routeCost G.w (radius G)+transitionCost (radius G) ≤ S*H) :
    Nat.card (remaining tr) = tailCount G.evaluator layout
      (midpointInitial G raw perm (fun a => (FirstTailHeader.middleWords G cuts expFit a).val))
      (liveCutEquiv (sizes G).h (sizes G).delta cuts).2 i := by
  have hi : i = 0 := Fin.ext first
  subst i
  let m := memory tr
  let u := putMemory G false m
  let dense := FirstTailHeader.middleWords G cuts expFit
  let formal := fun a => dense (perm.symm a)
  let init := midpointInitial G raw perm (fun a => (dense a).val)
  let c := G.constants
  let g := G.g
  let cp := Advice.copyBank c g
  have he := headerBelowOld G fits
  have flag := HeaderFlags.firstTail c g G.lit (he.trans_lt (G.transitionPub 1).isLt) header
  change m _ = (if 2^(sizes G).h+(0 : Fin (2^(sizes G).h)).val+1 = 2^(sizes G).h+1 then 1 else 0) at flag
  rw [Fin.val_zero,Nat.add_zero,ite_eq_left rfl] at flag
  obtain ⟨tag,copied,inc,ctrl,zero⟩ := FirstTailHeader.prepared G header expFit fits running
  have L := Advice.preparedLayout c g raw W.word fits capacity rawFits
  have rad : (cp 0).val = radius G := (addresses G fits).radiusWord
  have cfit : c.prefixCapacity.eval g < 2^G.w := by
    change (Layout.shadow c).eval g < _ at fits
    simp only [Layout.shadow,Layout.orderMap,Layout.packedPrefix,eval_add] at fits
    omega
  have hcap : ((Advice.fp c g) 1).val = c.prefixCapacity.eval g := Nat.mod_eq_of_lt cfit
  have hh := Advice.fourStages_budget c G.evaluator G.pair g G.lit u raw values adv L copied
    (by simpa only [hcap] using literal) fits (cap := G.clock) ((by decide : 130 ≤ 154).trans W.clock) tag
  rw [← G.program_eq] at hh
  have blank : ∀ j : Fin (fieldWords (radius G)), 0 < j.val → u ((cp 1).val+j.val) = 0 :=
    fun j hj => zero ⟨j.val,by change j.val < fieldWords (cp 0).val; rw [rad]; exact j.isLt⟩ hj
  obtain ⟨final,r⟩ := G.suffixRun_actual raw u values perm dense formal
    (fun j => by simp [formal]) ordinal L fits ((by decide : 94 ≤ 154).trans W.clock) running
    fit.prep.states space inc ctrl blank
  have rt := Advice.returning_append hh.1 r.returning
  have cw := Advice.costLimit_append hh.1 r.returning hh.2 r.cost
  have costEq := advice_work G raw u L
  rw [costEq] at cw
  have typed : ConfigAt final (G.transitionPub 1) init := by
    have cfg := r.config
    change ConfigAt final (G.transitionPub 1) (LiveEvaluatorTail.initialCode (cp 0).val
      (UniversalMachine.initial G.evaluator (raw ++ EvaluatorProgramRawInput.runtime formal))) at cfg
    rw [rad] at cfg
    have row (a : Fin (FirstTailHeader.labelCount G)) :
        Fin.ofNat (2^(FirstTailHeader.exponentWidth G)) (dense (perm.symm a)).val = formal a :=
      Fin.ext (Nat.mod_eq_of_lt (dense (perm.symm a)).isLt)
    simpa only [init,midpointInitial,funext row] using cfg
  have frame := initialOutputFrame G fits raw values L m final (fun x hx ho =>
    r.outside x hx (by
      change x < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+fieldWords (cp 0).val ≤ x
      rw [rad]; exact ho))
  obtain ⟨o⟩ := physicalOutput G header layout init mode fits pad
  exact countAfterInitialization G layout init _ 0 rfl m final fit tr.tag flag rt cw typed r.tag
    (o.transport frame) tr.logs (headerResources W adv cuts 0 tr) hcall (by
      simpa only [Nat.add_assoc,params,packWork,inputWork,LiveEvaluatorTailCost.Parameters.runtimeBits,
        LiveEvaluatorTailCost.Parameters.exponentBits] using budget)

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
