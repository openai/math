import OAI.Hierarchy.DescentChronologicalFee
import OAI.Hierarchy.DescentPrivateOwnerRows
import OAI.Computability.VPVNP.RAMExecution
import Mathlib.Data.Fin.Basic

namespace OAI
/-! # Holding the exact issued-path private charge in an actual CPU word -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}

def Path.Held (path : Path start source) (a : ℕ) (m : Memory bw) : Prop := m a=(path.privateCharge:Word bw)

theorem Path.Held.seed (a : ℕ) (m : Memory bw) (zero : m a=0) :
    (Path.here (start:=start)).Held a m := by simpa [Path.Held,Path.privateCharge] using zero

theorem Path.Held.keep {path : Path start source} {a b : ℕ} {m out : Memory bw} (h : path.Held a m)
    (kept : out b=m a) : path.Held b out := kept.trans h

theorem Path.Held.ordinary {path : Path start source} {he : 0≤ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T c n target) {a b : ℕ} {m out : Memory bw}
    (old : path.Held a m) (written : out b=m a+(ordinaryFee ticket:Word bw)) :
    (path.ordinary ticket).Held b out := by
  change out b=((path.privateCharge+ordinaryFee ticket:ℕ):Word bw)
  rw [Nat.cast_add,written,old]

/-- No reset cable is absorbed: the retained normalized bank split and its named
output permute and subdivide the earlier cables. -/
theorem Path.Held.reset {path : Path start source} {n h C f g cut tail : ℕ}
    {ctl : ResetRates G S k D n h C f g cut tail} (closed : ClosedReset source ctl)
    {a b : ℕ} {m out : Memory bw} (old : path.Held a m) (frame : out b=m a) :
    (path.reset closed).Held b out := by
  simpa [Path.Held,Path.privateCharge,reset_reblock_fee] using frame.trans old

end
end Hierarchy.DescentSixParty.Chronology

end OAI
