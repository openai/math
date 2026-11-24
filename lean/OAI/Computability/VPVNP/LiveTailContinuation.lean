import OAI.Computability.VPVNP.LiveFirstTailPhysicalCount
import OAI.Computability.VPVNP.LiveProgramAdviceCapacity

/-!
# Realizing the complete evaluator half of the live program

The same fixed native table handles the first, interior and last evaluator
groups. The distributed advice fixes the raw prefix and the permutation of the
label coordinates. This yields the specified local path multiplicity on every
physical cut assignment which passes its mode and padding checks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveEvaluatorEncoding LiveHeader LocalCount ChainAssignments
open OutsideTailStages OutsideTailCount
open scoped Fin.CommRing

variable (G : Group)

/-- Realization on the actual distributed advice and complete word-level
evaluator program. The two budgets bound an ordinary and an initial group,
respectively, and include all header, transfer and transition reports. -/
theorem tailContinuation {S H : ℕ} (W : Conditions G S H)
    (fits : limit G < 2^G.w) (fit : GeometryFit G (radius G))
    (expFit : 1+FirstTailHeader.labelCount G*FirstTailHeader.exponentWidth G ≤ (sizes G).delta)
    (layout : LiveEvaluatorTail.Layout G.evaluator.extra (radius G) G.w (sizes G).delta)
    (raw : List Bool) (perm : Equiv.Perm (Fin (FirstTailHeader.labelCount G)))
    (values : Fin (FirstTailHeader.labelCount G) → Word (Nat.clog 2 (FirstTailHeader.labelCount G)))
    (ordinal : ∀ a, (values a).val = (perm a).val)
    (capacity : G.w+G.constants.prefixCapacity.eval G.g +
      FirstTailHeader.labelCount G*Nat.clog 2 (FirstTailHeader.labelCount G) ≤ (sizes G).advice)
    (rawFits : raw.length ≤ G.constants.prefixCapacity.eval G.g)
    (space : G.evaluator.extra ≠ 0 → raw.length + (2*(FirstTailHeader.labelCount G*FirstTailHeader.exponentWidth G)+
      6*FirstTailHeader.exponentWidth G+4) ≤ radius G+1)
    (call : callBound G.w ≤ H)
    (ordinaryBudget : LiveHeaderSchedule.costBound (sizes G)+4+2*routeCost G.w (radius G)+transitionCost (radius G) ≤ S*H)
    (initialBudget : LiveHeaderSchedule.costBound (sizes G)+4+8+packWork (params G raw.length)+inputWork (params G raw.length)+
      routeCost G.w (radius G)+transitionCost (radius G) ≤ S*H) :
    TailContinuation W (Advice.adviceTape G.w (G.constants.prefixCapacity.eval G.g) (sizes G).advice raw values)
      expFit layout (midpointInitial G raw perm) := by
  let adv := Advice.adviceTape G.w (G.constants.prefixCapacity.eval G.g) (sizes G).advice raw values
  intro cuts i
  dsimp only
  intro mode pads tr out
  let middle := fun a => (FirstTailHeader.middleWords G cuts expFit a).val
  let init := midpointInitial G raw perm middle
  have hc : max 11 (G.w+4) ≤ H := by unfold callBound at call; omega
  by_cases first : i.val = 0
  · by_cases empty : G.evaluator.extra = 0
    · exact emptyFirstPhysicalCount W adv fits fit layout init cuts i mode pads tr out hc ordinaryBudget first empty
        (by simp [init, midpointInitial, LiveEvaluatorTail.initialCode, UniversalMachine.initial, empty])
    · exact nonemptyFirstPhysicalCount G W adv fits fit expFit layout raw perm values ordinal capacity rawFits
        (Advice.adviceTape_words _ _ _ _ _ rawFits capacity) (space empty) empty cuts i first mode (pads .right) tr out call initialBudget
  · exact nonfirstPhysicalCount W adv fits fit layout init cuts i mode pads tr out hc ordinaryBudget (by omega)

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
