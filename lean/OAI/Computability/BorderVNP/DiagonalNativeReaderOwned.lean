import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderWriters

/-! # Retained reader fields on the genuine pin, schedule and cube-owned returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP.BurstRAM RoutingISA RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Pins CellMacro.Generator
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} {gen : Fragment IO}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {regs : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {live : Fin d → Bool} {ext : Exterior R r link → Bool} {u : Fin (R+1)}
    (B : BootedPinStart gen G pub regs args live ext u)

/-- The actual pin choice changes precisely the two input arrays. The startup
control and advice words still contain the snapshot of the copied packet. -/
theorem BootedPinStart.readerAtPin (A : StartupArena) (entries count : ℕ)
    (old : entries*w ≤ A.copied) (row : (args u).ibase=A.ibase) (col : (args u).hbase=A.hbase)
    (bits : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool) :
    ReaderKept A entries count B.memory (B.pins bits).val.2.2 (B.pins bits).val.2.2 := by
  rw [(B.outputs bits).2.2.2.2]
  exact ReaderKept.of_prepared A _ (extendGuess bits) B.memory entries count old row col

/-- The geometry profile may have been decoded by a separately enumerated
public run. Its real deterministic boot has the same memory as the pin
dictionary's boot, so its preserved low addresses refer to the actual chosen
pin on this positive execution. -/
theorem BootedPinStart.readerAfterProfile (A : StartupArena) (entries count : ℕ)
    (packet : entries*w ≤ A.copied) (index : count ≤ A.count)
    (row : (args u).ibase=A.ibase) (col : (args u).hbase=A.hbase)
    (bits : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    (out saved : Memory w) (bank : Bank w) (trace : List (TeamRAM.Event w))
    (boot : Runs (pub u) (TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)) JointHeader.bootHeader
      (regs u) (processorMemory (G.processorFields u live ext (args u).ibase (args u).hbase (args u).starbase) w)
      trace bank saved)
    (image : let L := G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
      ∀ i<A.next, out i=Pins.preparedMemory L (Pins.extendGuess bits) saved L.count i) :
    ReaderKept A entries count B.memory (B.pins bits).val.2.2 out := by
  have same := (B.boot.unique_of_deterministic (by decide) boot).2.2
  apply (B.readerAtPin A entries count packet row col bits).advance
  intro i hi
  rw [(B.outputs bits).2.2.2.2,same]
  exact image i (hi.below packet index)

open SignedTaskArena

/-- The real packet boot initializes the header seed for this physical team.
The actual combined extension may contain all geometry, routing, cube and
task controls; the subtotal reader uses their specified address range. -/
theorem BootedPinStart.taskHeader (l : SignedTaskArena.Layout) (A : StartupArena)
    {reserve axes groups cap width : ℕ} (fields : JointHeader.PositiveFields reserve axes groups cap l.cube.teams l.dim width)
    (ref : ReferencePacket w d) (old : Fin 81 → Word w) (D : Packing.Directory.Layout)
    (origin edges cells fresh profile gates outputs geomWidth off ell : ℕ)
    (literal : ref.extension=PackedHistoryCircuit.signedProfileExtension l old D origin edges cells
      (rawAddress A reserve axes groups cap) u.val width fresh profile gates outputs geomWidth off ell)
    (boot : JointHeader.BootHeaderState (G.processorFields u live ext (args u).ibase (args u).hbase (args u).starbase)
      (G.transferFrame u (args u).header (args u).dst) (args u).advice ref (pub u) fields.bits B.out B.memory)
    (dst : (args u).dst=A.broadcastBase) (size : A.header=JointHeader.PositiveFields.width
      reserve axes groups cap l.cube.teams l.dim width)
    (side : l.cube.teams=R+1) (placement : A.next ≤ l.cube.header.header)
    {gateInputs guessed circuit : ℕ} (room : l.endAddress w gateInputs guessed circuit<2^w)
    (teamFit : R+1<2^w) (widthFit : width≤w) (wpos : 0<w) :
    HeaderSeed l fields (pub u) (rawAddress A reserve axes groups cap) u.val B.memory := by
  obtain ⟨_,_,_,_,dimFit,localFit,rawFit⟩ := finishSeedRoom l A size placement room
  apply headerSeed_boot l fields (pub u) (rawAddress A reserve axes groups cap) u.val old D origin edges cells
    fresh profile gates outputs geomWidth off ell _ literal boot dimFit localFit rawFit (by simpa only [side] using teamFit)
    (by simpa only [side] using u.isLt) widthFit wpos
  change A.broadcastBase+1+reserve+Cube.DeclarationBits.length axes groups cap =
    (args u).dst+1+reserve+Cube.DeclarationBits.length axes groups cap
  rw [dst]

/-- The chosen physical profile also retains the arbitrary subtotal
broadcast and its descriptor fields. This holds before any team checks
its own claimed row. -/
theorem BootedPinStart.headerAfterProfile (l : SignedTaskArena.Layout) (A : StartupArena)
    {reserve axes groups cap width : ℕ} (fields : JointHeader.PositiveFields reserve axes groups cap l.cube.teams l.dim width)
    (row : (args u).ibase=A.ibase) (col : (args u).hbase=A.hbase) (frame : (pub u 0).val=A.frame)
    (size : A.header=JointHeader.PositiveFields.width reserve axes groups cap l.cube.teams l.dim width)
    (bits : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    (out saved : Memory w) (bank : Bank w) (trace : List (TeamRAM.Event w))
    (boot : Runs (pub u) (TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)) JointHeader.bootHeader
      (regs u) (processorMemory (G.processorFields u live ext (args u).ibase (args u).hbase (args u).starbase) w)
      trace bank saved)
    (image : let L := G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
      ∀ i<A.next, out i=Pins.preparedMemory L (Pins.extendGuess bits) saved L.count i)
    (initial : HeaderSeed l fields (pub u) (rawAddress A reserve axes groups cap) u.val B.memory) :
    HeaderSeed l fields (pub u) (rawAddress A reserve axes groups cap) u.val out := by
  let L := G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
  have pinSeed := HeaderSeed.afterPins l A fields (pins := L) (Pins.extendGuess bits) initial frame row col size
  apply pinSeed.transfer
  intro x hx
  have low := seedRead_before_pins l A size (frame ▸ hx)
  have top := (rawAddress_room l A size).2.2
  have same := (B.boot.unique_of_deterministic (by decide) boot).2.2
  rw [same]
  exact image x (low.trans_le top)

end TeamContraction.ProcessorSlots

namespace RoutingISA

open VPVNP.BurstRAM Evaluator TeamContraction TeamContraction.ProcessorSlots BorderVNP.Cube
open BorderVNP.Cube.Physical Transmission

variable {w entries count : ℕ} {A : StartupArena} {boot pinMem : Memory w}

/-- The seven-column delivery publisher shares its actual base with the
end of the boot storage. It changes an ordinary control at field nine.
The selected reader controls and both pin banks lie outside those writes. -/
theorem ReaderKept.directoryPublished {origin edges cells descriptions desc gap : ℕ}
    {before placed : Memory w} (packed : ReaderKept A entries count boot pinMem before)
    (rows : List Packing.Directory.Row)
    (image : (Packing.RoutingOutputs.privateLayout A.frame origin edges cells descriptions desc gap).Image
      (readings before) descriptions (readings placed)) (room : A.next ≤ origin)
    (packet : entries*w ≤ A.copied) (index : count ≤ A.count) :
    ReaderKept A entries count boot pinMem (Packing.Directory.ISA.publish placed A.frame A.next rows) := by
  apply packed.advance
  intro k hk
  exact PackedHistoryCircuit.directoryPublished_low rows image room k (hk.below packet index)
    (hk.ne_field (k:=9) (by decide) (by decide))

/-- Read the actual data-writer output. All low reader fields survive its
published rows and count, even when the report that follows will be rejected. -/
theorem ReaderKept.sharedInput {R : ℕ} (ar : CubeArena.Layout) {D : Packing.Directory.Layout}
    {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)} {pins : Pins.Layout} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s t : Bank w} {m mt : Memory w} {es}
    (H : WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) pub mac s m es t mt)
    (cert : ReturnedWriters ar D pp lp owner decl group pins H)
    (keep : ReaderKept A entries count boot pinMem m) (frame : (pub 0).val=A.frame)
    (position : A.next ≤ ar.header.header) (packet : entries*w ≤ A.copied) (index : count ≤ A.count) :
    ReaderKept A entries count boot pinMem H.sharedInput := by
  apply keep.advance
  intro x hx
  have primary := (hx.below packet index).trans_le position
  have ne : x ≠ (pub 0).val+13 := frame ▸ hx.ne_field (by decide) (by decide)
  have data : x < (DataWriter.layout (readings pub) (readings H.dataInput)).output :=
    cert.emission.demand.records ▸ primary.trans_le (secondary_le_records ar)
  rw [H.dataImage cert.emission.demand.ready,DataWriter.publish,Function.update_of_ne ne,
    Packing.Directory.ISA.putWords_outside _ _ _ _ (.inl data)]
  exact cert.low x primary

/-- From the physical private placement to the writer whose submitted rows
are checked across the teams. The same pin and geometry snapshot survives
both native publications. -/
theorem ReaderKept.atSharedWriter {R origin edgeCap cellCap descriptions desc gap : ℕ}
    (ar : CubeArena.Layout) {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)} {pins : Pins.Layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s t : Bank w} {geometry placed mt : Memory w} {es}
    (directory : List Packing.Directory.Row)
    (output : (Packing.RoutingOutputs.privateLayout A.frame origin edgeCap cellCap descriptions desc gap).Image
      (readings geometry) descriptions (readings placed))
    (H : WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) pub mac s
      (Packing.Directory.ISA.publish placed A.frame A.next directory) es t mt)
    (writer : ReturnedWriters ar D pp lp owner decl group pins H)
    (source : ReaderKept A entries count boot pinMem geometry) (frame : (pub 0).val=A.frame)
    (room : A.next ≤ origin) (position : A.next ≤ ar.header.header)
    (packet : entries*w ≤ A.copied) (index : count ≤ A.count) :
    ReaderKept A entries count boot pinMem H.sharedInput :=
  (source.directoryPublished directory output room packet index).sharedInput ar H writer frame position packet index

/-- The same public placement carries the copied subtotal array, wire
dimensions and descriptor pointers into the real scheduler; the single
changed frame word is the delivery count. -/
theorem SignedTaskArena.HeaderSeed.directoryPublished {w reserve axes groups cap width team : ℕ}
    {pub : Arg → Word w} {a : SignedTaskArena.Layout} {A : StartupArena}
    (p : TeamContraction.JointHeader.PositiveFields reserve axes groups cap a.cube.teams a.dim width)
    {origin edgeCap cellCap descriptions desc gap : ℕ} {before placed : Memory w}
    (seed : SignedTaskArena.HeaderSeed a p pub (SignedTaskArena.rawAddress A reserve axes groups cap) team before)
    (frame : (pub 0).val=A.frame) (size : A.header=TeamContraction.JointHeader.PositiveFields.width
      reserve axes groups cap a.cube.teams a.dim width)
    (directory : List Packing.Directory.Row)
    (output : (Packing.RoutingOutputs.privateLayout A.frame origin edgeCap cellCap descriptions desc gap).Image
      (readings before) descriptions (readings placed)) (room : A.next ≤ origin) :
    SignedTaskArena.HeaderSeed a p pub (SignedTaskArena.rawAddress A reserve axes groups cap) team
      (Packing.Directory.ISA.publish placed A.frame A.next directory) := by
  apply seed.transfer
  intro x hx
  rw [frame] at hx
  obtain ⟨low,_,upper⟩ := SignedTaskArena.rawAddress_room a A size
  exact PackedHistoryCircuit.directoryPublished_low directory output room x
    ((SignedTaskArena.seedRead_before_pins a A size hx).trans_le upper)
    (SignedTaskArena.headerSeedRead_other hx low (j:=9) (by decide) (by decide))

end RoutingISA

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator ProcessorSlots

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)} (sa : SignedTaskArena.Layout)
    {decl : LengthDeclaration sa.cube.n sa.cube.header.d} {group : Fin sa.cube.header.d → Fin (R+1)}
    {F : TeamRows.Returns (Fin (R+1)) sa.cube w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
      Fin sa.cube.header.d → Fin (R+1)} {template : Frame} {rows : ℕ}

/-- A joint routing receipt from the same exterior, followed by the actual
owned traversal, transports the complete reader snapshot into its returning RAM. -/
theorem SharedWriters.returned_reader (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) sa.cube.header.blocks sa.cube.K sa.cube.h decl group)
    (handoff : OwnedHandoff f g src sa.cube decl group template sa.id rows F)
    {q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners}
    (receipt : ObservedOwned sa.cube decl group F owners (f.receivedRows g group) q)
    {A : StartupArena} {entries count : ℕ} {boot pinMem : Memory w}
    (u : Fin (R+1)) (prior : Memory w) (source : src u=readings prior)
    (keep : ReaderKept A entries count boot pinMem prior) (frame : (F.pub u 0).val=A.frame)
    (position : A.next ≤ sa.cube.header.header) (packet : entries*w ≤ A.copied) (index : count ≤ A.count) :
    ReaderKept A entries count boot pinMem (F.output u) := by
  apply keep.advance
  intro x hx
  have low := (hx.below packet index).trans_le position
  exact Fin.ext ((writer.returned_header_word sa symbols handoff receipt u x low
    (frame ▸ hx.ne_field (k := 13) (by decide) (by decide))
    (frame ▸ hx.ne_field (k := 46) (by decide) (by decide))).trans (congrFun source x))

open CellMacro.Generator RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Pins JointHeader SignedTaskArena

/-- Starting at one actual substituted pin, the physical profile, private
placement, two public row writers, common routing and owned traversals
preserve both the copied receipt inputs. The same geometry memory and
returned writer supply both conclusions on this execution. -/
theorem SharedWriters.boot_to_owned {gen : Fragment IO} (args : Fin (R+1) → UnitAddresses)
    (reg : Fin (R+1) → Bank w) (u : Fin (R+1))
    (B : BootedPinStart gen G F.pub reg args pin ext u)
    {res side blocks hdrCap digits : ℕ} (A : StartupArena)
    (p : PositiveFields res side blocks hdrCap sa.cube.teams sa.dim digits)
    (sub : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    {entries indices : ℕ} (packet : entries*w ≤ A.copied) (index : indices ≤ A.count)
    (posI : (args u).ibase=A.ibase) (posH : (args u).hbase=A.hbase) (frame : (F.pub u 0).val=A.frame)
    (size : A.header=PositiveFields.width res side blocks hdrCap sa.cube.teams sa.dim digits)
    (seed : HeaderSeed sa p (F.pub u) (rawAddress A res side blocks hdrCap) u.val B.memory)
    (out saved : Memory w) (bank : Bank w) (trace : List (TeamRAM.Event w))
    (boot : Runs (F.pub u) (TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)) bootHeader
      (reg u) (processorMemory (G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase) w) trace bank saved)
    (image : let L₀ := G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
      ∀ j<A.next,out j=Pins.preparedMemory L₀ (Pins.extendGuess sub) saved L₀.count j)
    {dest edgeCap cellCap desc gap : ℕ} (directory : List Packing.Directory.Row) (placed : Memory w)
    (placement : (Packing.RoutingOutputs.privateLayout A.frame dest edgeCap cellCap D.entries desc gap).Image
      (readings out) D.entries (readings placed)) (placedAbove : A.next ≤ dest)
    {mac : TeamOpcode.Macros w 8} {s z : Bank w} {after : Memory w} {es}
    (schedule : WriterHistory sa.cube.n (Tally.selectorWidth sa.cube.n sa.cube.K sa.cube.h) (F.pub u) mac s
      (Packing.Directory.ISA.publish placed A.frame A.next directory) es z after)
    (schedOutput : ReturnedWriters sa.cube D pp lp owner decl group (pins u) schedule)
    (readerBase : A.next ≤ sa.cube.header.header) (source : src u=readings schedule.sharedInput)
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) sa.cube.header.blocks sa.cube.K sa.cube.h decl group)
    (handoff : OwnedHandoff f g src sa.cube decl group template sa.id rows F)
    {q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners}
    (receipt : ObservedOwned sa.cube decl group F owners (f.receivedRows g group) q) :
    ReaderKept A entries indices B.memory (B.pins sub).val.2.2 (F.output u) ∧
      HeaderSeed sa p (F.pub u) (rawAddress A res side blocks hdrCap) u.val (F.output u) := by
  have initialReader := B.readerAfterProfile A entries indices packet index posI posH sub out saved bank trace boot image
  have initialHeader := B.headerAfterProfile sa A p posI posH frame size sub out saved bank trace boot image seed
  have reader := initialReader.atSharedWriter sa.cube directory placement schedule schedOutput frame placedAbove readerBase packet index
  have written := HeaderSeed.directoryPublished p initialHeader frame size directory placement placedAbove
  have header := HeaderSeed.sharedInput sa A p u.val frame size schedule schedOutput written readerBase
  exact ⟨writer.returned_reader sa symbols handoff receipt u schedule.sharedInput source reader frame readerBase packet index,
    writer.returned_header_seed sa A p symbols handoff receipt u schedule.sharedInput frame size readerBase header
      (fun j _ => congrFun source j)⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
