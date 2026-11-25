import OAI.ThreeFlat.RAM.TickMemoryLayout
import OAI.ThreeFlat.RAM.TickShape
import OAI.ThreeFlat.RAM.ContractionLookup

namespace OAI
namespace ThreeFlat.RAM.TickActiveROM

open Computability.VPVNP.BurstRAM BitLayout Contraction
open scoped Fin.CommRing
variable {F : Type*} [Field F] [Fintype F] {p H J w : ℕ}

structure WordBounds (B : Layout) (fit : Fits (TickWeightedBank.shape F p H J) w) : Prop where
  width : 64 ≤ 2^w
  ctrl : B.control+4 ≤ B.clockWords
  clk : B.clockWords+4 ≤ B.bounds
  bounds : B.bounds+4 ≤ B.auxRequest
  requests : B.auxRequest+8*B.bits < 2^w
  oldAux : B.oldAux+B.bits ≤ B.bounds
  newAux : B.newAux+B.bits ≤ B.bounds
  oldChunk : B.oldChunk+B.bits ≤ B.bounds
  newChunk : B.newChunk+B.bits ≤ B.bounds
  metadata : footprint (TickWeightedBank.shape F p H J) ≤ B.metadata
  lut : footprint (TickWeightedBank.shape F p H J) ≤ B.lut
  «meta» : B.metadata+4*J ≤ 2^w
  low : footprint (TickWeightedBank.shape F p H J) < 2^w

theorem WordBounds.pinAddr {B : Layout} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (h : WordBounds B fit) (base : ℕ) (endAt : base+B.bits ≤ B.bounds) (i : Fin B.bits) :
    ((base : Word w)+(i.val : Word w)).val = base+i.val := by
  have a := h.bounds
  have b := h.requests
  have t := i.isLt
  rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega)]


end ThreeFlat.RAM.TickActiveROM

end OAI
