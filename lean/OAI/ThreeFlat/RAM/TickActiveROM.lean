import OAI.ThreeFlat.RAM.TickMemoryLayout
import OAI.ThreeFlat.RAM.TickClockWriter
import OAI.ThreeFlat.RAM.TickPairHeader
import OAI.ThreeFlat.RAM.TickHistoryCore
import OAI.ThreeFlat.RAM.TickGroupScanROM
import OAI.ThreeFlat.RAM.TickWeightedROM

namespace OAI
/-! # Linking the shared physical guards, group scan and weighted slot evaluator -/

noncomputable section
namespace ThreeFlat.RAM.TickActiveROM

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorExpr Diagonal.TickChronology
open Contraction BitLayout
open scoped Fin.CommRing

def Layout.regions (A : Layout) : TickIdentity.Regions := ⟨A.oldAux,A.newAux,A.zero,A.oldChunk,A.newChunk⟩

def Layout.scan (A : Layout) : TickGroupScanBank.Plan where
  table := A.intervalTable
  countAddr := A.intervalCount
  chunkAddr := A.clockWords+2
  groupAddr := A.clockWords
  mapBase := A.intervalMap
  bits := A.bits
  reqStart := A.chunkRequest
  oldPtr := A.bounds+2
  newPtr := A.bounds+3
  old := A.oldChunk
  new := A.newChunk

def range (w base : ℕ) (i : Fin 4) : Word w := (base+i.val : ℕ)
def Layout.header (w : ℕ) (A : Layout) : Fin 4 → Word w :=
  ![(A.control+2 : ℕ),(A.control+3 : ℕ),(A.bounds : Word w),(A.bounds+1 : ℕ)]

def Layout.aux (w k : ℕ) (A : Layout) := TickRequestStream.program A.auxRequest
  (TickAuxRequestGen.row (w:=w) (k:=k) (A.header w))

def Layout.clock (w k : ℕ) (A : Layout) (c : Clock) := TickClockWriter.expr (w:=w) (k:=k)
  c A.bits A.teams A.clockWords (A.control : Word w) (A.control+1 : ℕ)


variable {F : Type*} [Field F] [Fintype F] {p H J w k n m nr mr r pc : ℕ}
variable (A : Layout) (c : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)

inductive Label (w k nav prep : ℕ) (core scan weight clock : Type) where
  | control (x : core)
  | writeClock (x : clock)
  | navigate (x : Fin nav)
  | bound (x : Fin 22)
  | readChunk (x : scan)
  | prepare (x : Fin prep)
  | run (x : weight)
  deriving DecidableEq, Fintype

abbrev Labels := Label w k n m (TickHistoryCore.Labels (A.aux w k)) (TickGroupScanBank.Labels w k A.scan)
    (Fin (TickSeedTail.count (TickWeightedBank.seed (F:=F) (p:=p) (H:=H) (J:=J) (k:=k) fit))) (Fin ((A.clock w k c).labels+6))

def inside {α β : Type*} {s : ℕ} (P : β ↪ Fin s) (f : α → β) (inject : Function.Injective f) :
    α ↪ Fin s := ⟨fun i => P (f i), fun _ _ h => inject (P.injective h)⟩

section
attribute [local irreducible] Layout.aux Layout.clock Layout.scan TickGroupScanBank.expr TickWeightedBank.seed
set_option maxHeartbeats 800000 in
structure Registers (A : Layout) (c : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)
    (nr mr r k : ℕ) where
  control : Fin 5 ↪ Fin r
  generator : Fin (4+(A.aux w k).binds) ↪ Fin r
  compare : Fin 37 ↪ Fin r
  test : Fin 2 ↪ Fin r
  chunks : Fin 7 ↪ Fin r
  clock : Fin (4+(A.clock w k c).binds) ↪ Fin r
  scan : Fin 15 ↪ Fin r
  scanGen : Fin (4+(TickGroupScanBank.expr w k A.scan).binds) ↪ Fin r
  navigator : Fin nr ↪ Fin r
  slot : Fin mr ↪ Fin r
  field : Fin (4+(TickWeightedBank.seed (F:=F) (p:=p) (H:=H) (J:=J) (k:=k) fit).binds) ↪ Fin r
  eval : Fin 36 ↪ Fin r

end

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
/-- The compressor navigator decodes the canonical proposal, checks its
admission, and writes the group counters and original interval records.
The slot-preparation block writes the selected padded records. Their return
addresses are installed by this finite ROM. -/
def emit (nav : Block w n nr k) (prep : Block w m mr k)
    (P : Labels (n:=n) (m:=m) (k:=k) A c fit ↪ Fin pc) (R : Registers A c fit nr mr r k)
    (evalPublic : Fin 7 → Fin k) :
    Labels (n:=n) (m:=m) (k:=k) A c fit → Instr w pc r k :=
  let core := inside P .control (fun _ _ h => by cases h; rfl)
  let plan := A.scan
  let scan := inside P .readChunk (fun _ _ h => by cases h; rfl)
  let clockLoc := inside P .writeClock (fun _ _ h => by cases h; rfl)
  let field := inside P .run (fun _ _ h => by cases h; rfl)
  let nv := inside P .navigate (fun _ _ h => by cases h; rfl)
  let ev := inside P .prepare (fun _ _ h => by cases h; rfl)
  let aux := A.aux w k
  let e := A.clock w k c
  let weighted := TickWeightedBank.seed (F:=F) (p:=p) (H:=H) (J:=J) (k:=k) fit
  let init := TickGenerateTable.driver e clockLoc 0
  let run := TickGenerateTable.driver weighted (TickSeedTail.genPC weighted field) 0
  fun label => match label with
  | .control i => TickHistoryCore.emit A.bits A.auxRequest A.regions (range w A.control)
      (A.header w) core R.control R.generator R.compare R.test R.chunks init
      (TickGroupScanBank.boot plan scan 0) (ev prep.first) i
  | .writeClock i => TickGenerateTable.emit e (A.clockWords : Word w) (A.clockWords+4 : ℕ)
      clockLoc R.clock (nv nav.first) i
  | .navigate i => nav.emit nv R.navigator id (P (.bound 0)) i
  | .bound i => TickPairHeader.emit (fun j => P (.bound j)) R.control (range w A.bounds)
      A.clockWords A.groupCounts c.groups (1+A.capacity : ℕ) A.oldAux (TickHistoryCore.resumeAux aux core) i
  | .readChunk i => TickGroupScanBank.emit plan scan R.scan R.scanGen R.compare
      (TickHistoryCore.returned aux core) i
  | .prepare i => prep.emit ev R.slot id run i
  | .run i => TickWeightedBank.emit fit A.metadata A.lut field R.field R.eval evalPublic i


end ThreeFlat.RAM.TickActiveROM

end
end OAI
