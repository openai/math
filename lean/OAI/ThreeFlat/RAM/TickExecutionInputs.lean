import OAI.ThreeFlat.RAM.TickWordBounds
import OAI.ThreeFlat.RAM.TickActiveTransfer
import OAI.ThreeFlat.RAM.TickBoundReads

namespace OAI
/-! # Data produced by the deterministic chronology and the selected slot -/

noncomputable section
namespace ThreeFlat.RAM.TickActiveROM
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorScan TickFuel Diagonal.TickChronology
open Contraction BitLayout HistoryFactors
open Diagonal.TickGroupIntervals (Interval)
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {p H J w : ℕ}

/-- Packed group intervals and the selected factor network, decoded from one H
proposal. All function fields here are finite tables or bit vectors. -/
structure CellInput (B : Layout) (clock : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w) where
  count : ℕ
  pairSpace : 1+B.capacity+2*count ≤ B.bits
  intervals : List Interval
  lo : ℕ
  group : ℕ
  before : ℕ → Bool
  after : ℕ → Bool
  net : BitNetwork F p
  lib : Library net
  hidden : net.internal=H
  cells : net.cells=J
  lutSpace : B.lut+8*lib.count ≤ 2^w

def CellInput.aux {B : Layout} {clock : Clock} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (x : CellInput B clock fit) := TickPairHeader.layout B.capacity x.count x.pairSpace

def CellInput.weight {B : Layout} {clock : Clock} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (x : CellInput B clock fit) (ph : Phase) (oa na oc nc : Fin B.bits → Bool) (pin : Fin p → Bool) : F :=
  if x.aux.accepts ph true oa na then
    if ph=.scan then (if TickChunkCheck.valid true (TickGroupScanBank.layout B.scan x.lo x.group)
      x.intervals x.before x.after (chunkView B x.lo x.group oc) (chunkView B x.lo x.group nc) then 1 else 0)
    else if oc=nc then (if ph=.evaluate then x.net.eval pin else 1) else 0
  else 0

def CellInput.filled {B : Layout} {clock : Clock} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (x : CellInput B clock fit) (ph : Phase) (out : Memory w) : Memory w :=
  fillSegment B.auxRequest (8*B.bits) (TickRequestStream.dataWord B.auxRequest (x.aux.rule ph true))
    (boundsMemory B clock out)

/-- The global replay returns the numbers of pairs, interval table, and root
directories. The preserved boundary arrays are the actual old/new tensor pins.
At this interface every one of these premises is a statement about words. -/
structure NavOutput {B : Layout} {clock : Clock} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (x : CellInput B clock fit) (ph : Phase) (oa na oc nc : Fin B.bits → Bool)
    (slotInput : Memory w → Prop) (out : Memory w) : Prop where
  count : TickPairHeader.selected out B.clockWords B.groupCounts clock.groups = (x.count : Word w)
  phase : out (B.control+2) = (ph.tag : Word w)
  marker : out (B.control+3) = 1
  oldAux : ∀ i : Fin B.bits, out (B.oldAux+i.val) = TickBitRelation.bitWord w (oa i)
  newAux : ∀ i : Fin B.bits, out (B.newAux+i.val) = TickBitRelation.bitWord w (na i)
  oldChunk : ∀ i : Fin B.bits, out (B.oldChunk+i.val) = TickBitRelation.bitWord w (oc i)
  newChunk : ∀ i : Fin B.bits, out (B.newChunk+i.val) = TickBitRelation.bitWord w (nc i)
  scanInputs : ph=.scan → TickGroupScanBank.ScanInputs w B.scan x.intervals x.lo x.group (x.filled ph out)
    x.before x.after (chunkView B x.lo x.group oc) (chunkView B x.lo x.group nc)
  evalInputs : ph=.evaluate → slotInput (x.filled ph out)

theorem WordBounds.safe_header {B : Layout} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (h : WordBounds B fit) (i : Fin 4) : (B.header w i).val < B.auxRequest := by
  have a := h.ctrl
  have b := h.clk
  have c := h.bounds
  have d := h.requests
  fin_cases i
  · change ((B.control+2 : ℕ) : Word w).val < _
    rw [Fin.val_cast_of_lt (by omega)]
    omega
  · change ((B.control+3 : ℕ) : Word w).val < _
    rw [Fin.val_cast_of_lt (by omega)]
    omega
  · change (B.bounds : Word w).val < _
    rw [Fin.val_cast_of_lt (by omega)]
    omega
  · change ((B.bounds+1 : ℕ) : Word w).val < _
    rw [Fin.val_cast_of_lt (by omega)]
    omega


end ThreeFlat.RAM.TickActiveROM

end
end OAI
