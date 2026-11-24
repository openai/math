import OAI.Computability.VPVNP.LiveEvaluatorEncoding
import Mathlib.Data.ZMod.Defs

/-!
# External memory occupied by live evaluator configurations and scratch

One packed word stores the state, followed by the two consecutive
head-relative tape windows. The chosen transition occupies five separate
scratch words in target, first write, first move, second write, second move order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM

open BurstRAM LiveEvaluatorEncoding
open scoped Fin.CommRing

variable {w extra M : ℕ}

/-- The specified external memory contains the complete canonical code. -/
structure ConfigAt (m : Memory w) (base : Word w) (c : LiveEvaluatorEncoding.Code extra M) : Prop where
  state : (m base.val).val = c.stateWord.val
  first (i : Fin (2 * M + 1)) : (m (base + 1 + (i.val : Word w)).val).val = (c.firstCell i).val
  second (i : Fin (2 * M + 1)) :
    (m (base + 1 + ((2 * M + 1 : ℕ) : Word w) + (i.val : Word w)).val).val = (c.secondCell i).val

/-- The five words selected once at the start of this group. -/
structure ActionAt (m : Memory w) (base : Word w) (target : ℕ)
    (firstWrite firstMove secondWrite secondMove : UniversalMachine.Symbol) : Prop where
  targetVal : (m base.val).val = target
  firstWriteVal : (m (base + 1).val).val = firstWrite.val
  firstMoveVal : (m (base + 2).val).val = firstMove.val
  secondWriteVal : (m (base + 3).val).val = secondWrite.val
  secondMoveVal : (m (base + 4).val).val = secondMove.val

/-- Installing the words of the checked cut decoder gives the exact memory
image used by the native scan. -/
theorem configAt_of_words (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) {m : Memory w} {base : Word w}
    (c : LiveEvaluatorEncoding.Code extra M)
    (h : ∀ f, m (base + (f.val : Word w)).val = (format hw hs).words c f) :
    ConfigAt m base c := by
  constructor
  · have he := congrArg Fin.val (h (stateField M))
    simpa [stateField] using he.trans (words_state hw hs c)
  · intro i
    have he := congrArg Fin.val (h (firstField i))
    simpa [firstField, add_assoc] using he.trans (words_first hw hs c i)
  · intro i
    have he := congrArg Fin.val (h (secondField i))
    simpa [secondField, add_assoc] using he.trans (words_second hw hs c i)

end LiveEvaluatorRAM

end VPVNP
end Computability
end OAI
