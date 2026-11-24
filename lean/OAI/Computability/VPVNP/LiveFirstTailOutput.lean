import OAI.Computability.VPVNP.LiveLinkedEvaluatorTransport
import OAI.Computability.VPVNP.LiveProgramAdviceInputLayout

/-!
# Preserving the outgoing cut during midpoint initialization

The outgoing flag and distributed cut lie below the old configuration. The
new configuration lies between the old configuration and the advice frames.
Initialization of the old tape and the four advice stages therefore preserve
all three inputs to the outgoing router.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveEvaluatorEncoding LiveEvaluatorAdviceBanks
open scoped Fin.CommRing

variable (G : Group)

/-- The advice frame follows the five transition-scratch words. -/
theorem frameAfterScratch (fits : limit G < 2^G.w) :
    (Advice.fp G.constants G.g 3).val = (G.transitionPub 3).val + 5 := by
  let s := (Layout.transitionScratch G.constants).eval G.g
  have hf : s+5 < 2^G.w := by
    change (Layout.shadow G.constants).eval G.g < _ at fits
    simp only [Layout.shadow,Layout.orderMap,Layout.packedPrefix,Layout.adviceFrames,eval_add] at fits
    change s+5+24+_+_ < _ at fits
    omega
  change (s+5) % (2^G.w) = s % (2^G.w) + 5
  rw [Nat.mod_eq_of_lt hf,Nat.mod_eq_of_lt (by omega : s < 2^G.w)]

/-- Pointwise preservation on the two physical ranges surrounding the
incoming bank suffices for the outgoing router's complete input. -/
theorem frameOfRanges (fits : limit G < 2^G.w) (m m' : Memory G.w)
    (preserve : ∀ x : ℕ, G.addr.val < x → x < (Advice.fp G.constants G.g 3).val →
      (x < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+k G ≤ x) → m' x = m x) :
    OutputFrame G (radius G) m m' := by
  obtain ⟨l,r,e,flag,fl,o,n,s,rad,wc,kc⟩ := addresses G fits
  have hf := frameAfterScratch G fits
  refine ⟨preserve _ flag (by omega) (.inl (by omega)), ?_, ?_⟩
  · intro j
    have hj : j.val < k G * G.w := j.isLt
    exact preserve _ (by omega) (by omega) (.inl (by omega))
  · intro j
    have hj : j.val < k G := j.isLt
    exact preserve _ (by omega) (by omega) (.inr (by omega))

/-- Compose the control-word write, advice preparation, and the incoming
tape's writes. The outgoing cut is read from the original physical header. -/
theorem initialOutputFrame (fits : limit G < 2^G.w) (raw : List Bool)
    (values : Fin (G.constants.labels.eval G.g) → Word (Nat.clog 2 (G.constants.labels.eval G.g)))
    (L : PreparedLayout (Advice.lp G.constants G.g) (Advice.fp G.constants G.g)
      (Advice.op G.constants G.g) raw (G.constants.labels.eval G.g) (Nat.clog 2 (G.constants.labels.eval G.g)))
    (m final : Memory G.w)
    (outside : ∀ x : ℕ, x ≠ G.addr.val →
      (x < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+k G ≤ x) →
      final x = Advice.finalMemory G.constants G.g G.lit raw values (putMemory G false m) x) :
    OutputFrame G (radius G) m final := by
  let written := putMemory G false m
  have F₁ := putInitialFrame G (addresses G fits) m
  have F₂ : OutputFrame G (radius G) written final := by
    apply frameOfRanges G fits
    intro x above below ext
    exact (outside x (by omega) ext).trans
      (Advice.beforeFrame_preserved G.constants G.g G.lit raw values written L fits x above below)
  exact ⟨F₂.flag.trans F₁.flag,fun j => (F₂.field j).trans (F₁.field j),
    fun j => (F₂.bank j).trans (F₁.bank j)⟩

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
