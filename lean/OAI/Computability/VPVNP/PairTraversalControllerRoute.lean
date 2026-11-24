import OAI.Computability.VPVNP.PairTraversalControllerRead
import OAI.Computability.VPVNP.PairTraversalControllerCode

/-!
# Natural-number decisions of the traversal dispatcher

The finite-word tests choose the worker prescribed by the phase and the
current layer. The layer-end digit selects the reset instruction, and the
terminal phase-level selects acceptance.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM TraversalControllerInputs
open scoped Fin.CommRing

theorem Readback.route_eq {w : ℕ} {pub : Fin 11 → Word w} {m : Memory w} {L N p i : ℕ}
    {rs : Fin R → Word w} (h : Readback pub m L N p i rs) (hL : 0 < L)
    (phase : p ≤ 2 * L) (digit : i ≤ N) (fit : 2 * L * (N + 1) < 2 ^ w) :
    Native.route rs =
      if p < 2 * L then
        if i < (siteCount pub m (p % L)).val then
          if p < L then .role else if p % L = 0 then .leaf else .fiber
        else .reset
      else .accept := by
  have limitFit := (Nat.le_mul_of_pos_right (2 * L) (Nat.succ_pos N)).trans_lt fit
  have phaseFit := phase.trans_lt limitFit
  have layerFit : L < 2 ^ w := (Nat.le_mul_of_pos_left L (by decide : 0 < 2)).trans_lt limitFit
  have indexFit := (Nat.mod_lt p hL).trans layerFit
  have pitchFit := (Nat.le_mul_of_pos_left (N + 1) (Nat.mul_pos (by decide) hL)).trans_lt fit
  have siteFit := digit.trans_lt ((Nat.lt_succ_self N).trans pitchFit)
  simp only [Native.route, h.phase, h.twice, h.site, h.count, h.levels, h.index, h.zero,
    Fin.lt_def, Fin.ext_iff, Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt limitFit,
    Nat.mod_eq_of_lt phaseFit, Nat.mod_eq_of_lt siteFit, Nat.mod_eq_of_lt layerFit, Nat.mod_eq_of_lt indexFit]

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
