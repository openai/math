import OAI.ThreeFlat.RAM.TickSeedTail
import OAI.ThreeFlat.RAM.TickShape
import OAI.ThreeFlat.RAM.HistoryFieldSeed
import OAI.ThreeFlat.RAM.HistoryInterpreter

namespace OAI
/-! # One native terminal bank for every padded group slot of common dimensions -/

noncomputable section
namespace ThreeFlat.RAM.TickWeightedBank

open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Contraction HistoryFactors TickSeedTail
open BitNetwork

open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {p H J w k pc r : ℕ}

def seed (fit : Fits (shape F p H J) w) :=
  HistoryFieldSeed.fieldExpr (K:=k) (codec (shape F p H J) fit) (mulBase p H J)

/-- The source arm of this ROM is independent of the history, cell list or
coefficient IDs. Only the common dimensions and scratch bases occur in its
text and seven public operands. -/
def emit (fit : Fits (shape F p H J) w) («meta» lut : ℕ)
    (P : Fin (count (seed (k:=k) fit)) ↪ Fin pc)
    (genR : Fin (4+(seed (k:=k) fit).binds) ↪ Fin r) (R : Fin 36 ↪ Fin r) (K : Fin 7 → Fin k) :=
  TickSeedTail.emit (seed fit) (mulBase p H J : Word w) (footprint (shape F p H J) : Word w)
    (interpreter p H J «meta» lut fit) P genR R K

end ThreeFlat.RAM.TickWeightedBank

end
end OAI
