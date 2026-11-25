import OAI.ThreeFlat.Diagonal.TickChronology
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Native tick storage parameters and four public clock words -/

namespace ThreeFlat.RAM.TickActiveROM

structure Layout where
  bits : ℕ
  teams : ℕ
  capacity : ℕ
  oldAux : ℕ
  newAux : ℕ
  oldChunk : ℕ
  newChunk : ℕ
  zero : ℕ
  control : ℕ
  clockWords : ℕ
  bounds : ℕ
  auxRequest : ℕ
  chunkRequest : ℕ
  intervalTable : ℕ
  intervalCount : ℕ
  intervalMap : ℕ
  groupCounts : ℕ
  metadata : ℕ
  lut : ℕ

end ThreeFlat.RAM.TickActiveROM

namespace ThreeFlat.RAM.TickClockWords
open Diagonal.TickChronology

def values (c : Clock) (a q team t : ℕ) : Fin 4 → ℕ :=
  ![c.group t, c.offset t, (t%c.chunks)*a, (c.offset t-(c.chunks+1))*q+team]

end ThreeFlat.RAM.TickClockWords

end OAI
