import OAI.Computability.VPVNP.RAMExecution
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # The two native control words of the chronological allocator loop -/

namespace Hierarchy.ProbeStage.Native.CompactLoop
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

def cursor (h : ℕ) := 2^h+6
def limit (h : ℕ) := 2^h+7

def cells {w : ℕ} (h j : ℕ) (m : Memory w) : Memory w :=
  Function.update (Function.update m (cursor h) (j:Word w)) (limit h) ((2^h:ℕ):Word w)

end Hierarchy.ProbeStage.Native.CompactLoop

end OAI
