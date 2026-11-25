import OAI.Computability.BorderVNP.DiagonalOriginalOwnedLow
import OAI.Computability.BorderVNP.DiagonalPublishedControlReadback
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership

/-! # Reading the original frozen publication and boot from the reached source cut -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator ProcessorSlots

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    (sa : SignedTaskArena.Layout)
    {decl : LengthDeclaration sa.cube.n sa.cube.header.d} {group : Fin sa.cube.header.d → Fin (R+1)}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
      Fin sa.cube.header.d → Fin (R+1)} {template : Frame} {rows : ℕ}

open CellMacro.Generator RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Pins JointHeader SignedTaskArena
open PackedHistoryCircuit

variable {pub : Fin (R+1) → Arg → Word w}
  {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
  (B : (u : Fin (R+1)) → BootedPinStart SparseExterior.driver G pub reg args pin ext u)
  (active : (u : Fin (R+1)) → (B u).start.Prefix sa.id) (u : Fin (R+1))
local notation3 (prettyPrint := false) "history" => PinStart.ownedVisits (ar:=sa.cube) (fun t => (B t).start) active
local notation3 (prettyPrint := false) "V" => PinStart.visits sa.id (fun t => (B t).start) (active u)
local notation3 (prettyPrint := false) "afterPin" => ((B u).pins (active u).1).val.2
set_option maxRecDepth 7500
set_option maxHeartbeats 2200000


variable {exteriorHeader : List Bool}
    {publicAt : HeaderExterior L exteriorHeader → Fin (R+1) → Arg → Word w}
    {macAt : HeaderExterior L exteriorHeader → Fin (R+1) → TeamOpcode.Macros w 8}
    {regsAt : HeaderExterior L exteriorHeader → Fin (R+1) → Bank w}
    {memAt : HeaderExterior L exteriorHeader → Fin (R+1) → Memory w}
    (F : PreparationFrame G L sa.cube decl exteriorHeader pin publicAt macAt regsAt memAt)


open Crossing BorderVNP.Packing BorderVNP.Packing.RoutingOutputs RoutingISA.LocalRow

local notation3 (prettyPrint := false) "machine" => install SparseExterior.driver n (B u).start.routines

/-- Recover the source reader and subtotal from the original geometry
residence and directory return. The same return also contains all signed
boot-pointer fields consumed by the selected writer. -/
theorem PreparationFrame.ReturnedOwnershipAt.publishedBanks
    {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners}
    (origin : HeaderExterior L exteriorHeader)
    (atOwned : F.ReturnedOwnershipAt sa origin ext template rows v history)
    (A : StartupArena) {entries indices res side blocks hdrCap digits : ℕ}
    (p : PositiveFields res side blocks hdrCap sa.cube.teams sa.dim digits)
    (copies : entries*w≤A.copied) (index : indices≤A.count)
    (posI : (args u).ibase=A.ibase) (posH : (args u).hbase=A.hbase) (frame : (pub u 0).val=A.frame)
    (size : A.header=PositiveFields.width res side blocks hdrCap sa.cube.teams sa.dim digits)
    (seed : HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (B u).memory)
    (index₀ : Fin A.teams) (slot : ℕ) (reference : ReferencePacket w d) (copy : BroadcastFrame)
    (advice : AdviceLayout) (fields : Pins.ProcessorFields (A.operands index₀ slot reference).layout)
    (header : List Bool)
    (sameLayout : (A.operands index₀ slot reference).layout =
      G.pinLayout u (args u).ibase (args u).hbase (args u).starbase)
    {geo : Memory w}
    (resident : BootResidence (F:=fields) A index₀ slot reference copy advice (pub u)
      (install SparseExterior.driver n (B u).start.routines)
      header (processorMemory (G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase) w)
      (reg u) (active u).1 geo)
    (dest gap : ℕ) (above : A.next ≤ dest) (secondary : A.next ≤ sa.cube.header.header)
    {D ports : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin sa.cube.cells) (edgeID : N.Edge ↪ Fin sa.cube.cables)
    (portID : P ↪ Fin ports) (original : Fin F.dataDir.entries → N.Site)
    (live : (Fin F.dataDir.teams × Fin F.dataDir.sites) ↪ P) (preRegs : Bank w) (usedPin profCost : ℕ)
    (sources : PublishedPin sa F.dataDir N cell edgeID portID original live A index₀ slot reference dest gap copy header
      fields (pub u) machine (active u).1 afterPin.1 afterPin.2 preRegs geo usedPin profCost)
    (epoch : Returns epochPlacement (pub u) machine afterPin.1 afterPin.2)
    (published : Returns Directory.ISA.program (pub u) machine epoch.val.2.1 epoch.val.2.2)
    {s z : Bank w} {after : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory sa.cube.n (Tally.selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub u) machine s
      published.val.2.2 es z after)
    (written : ReturnedWriters sa.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner decl F.group
      (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)) W)
    (source : F.source origin u=readings W.sharedInput) :
    (ReaderKept A entries indices (B u).memory afterPin.2 (V).owned.val.2.2 ∧
      HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (V).owned.val.2.2) ∧
      BootPins (pub u) copy reference.extension header published.val.2.2 := by
  have image := PublishedPin.actual_readback sa F.dataDir N cell edgeID portID original live A index₀ slot reference
    dest gap copy header fields (pub u) machine (active u).1 afterPin.1 afterPin.2 preRegs geo usedPin profCost
    sources epoch published
  have low := BootedPinStart.protected_low_after_residence B u A index₀ slot reference copy advice fields
    header sameLayout (active u).1 resident
  obtain ⟨_,_,writer,_,handoff,observed⟩ := atOwned
  let mid := epoch.val.2.2
  let layout := privateLayout A.frame dest sa.cube.cables sa.cube.cells F.dataDir.entries F.dataDir.description gap
  let tables := bases dest sa.cube.cables sa.cube.cells F.dataDir.entries
  let issued := F.dataDir.directory (Directory.ISA.placement (readings mid) layout.raw)
    (Directory.ISA.placement (readings mid) tables.livePairs)
  have native {initial : Memory w} (produced : initial=Directory.ISA.publish mid A.frame A.next issued)
      (writ : WriterHistory sa.cube.n (Tally.selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub u)
        machine s initial es z after)
      (ok : ReturnedWriters sa.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner decl F.group
        (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)) writ)
      (start : F.source origin u=readings writ.sharedInput) :
      ReaderKept A entries indices (B u).memory afterPin.2 (V).owned.val.2.2 ∧
        HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (V).owned.val.2.2 := by
    subst initial
    exact writer.banks_on_original_low sa B active u (F.frame origin) handoff observed A p copies index
      posI posH frame size seed low above issued mid image.2.1 writ ok start secondary
  exact ⟨native image.1 W written source,image.2.2.2⟩

/-- Original signed setup for interpreting each independently observed
published pin at the indicated destination. -/
abbrev BootedPinStart.PublishedSourceReadback (A : StartupArena)
    {res side blocks cap digits : ℕ} (p : PositiveFields res side blocks cap sa.cube.teams sa.dim digits)
    (dest entries indices : ℕ) : Prop :=
  ∀ {wire : WireLayout (R+1) r link} {hdr : List Bool} {len : LengthDeclaration sa.cube.n sa.cube.header.d}
    {p₀ : HeaderExterior wire hdr → Fin (R+1) → Arg → Word w}
    {op₀ : HeaderExterior wire hdr → Fin (R+1) → TeamOpcode.Macros w 8}
    {r₀ : HeaderExterior wire hdr → Fin (R+1) → Bank w}
    {m₀ : HeaderExterior wire hdr → Fin (R+1) → Memory w}
    {who : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
      Fin sa.cube.header.d → Fin (R+1)}
    (frame : PreparationFrame G wire sa.cube len hdr pin p₀ op₀ r₀ m₀) (origin : HeaderExterior wire hdr)
    {proto : Frame} {amount : ℕ} {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) who},
    frame.ReturnedOwnershipAt sa origin ext proto amount v history →
  ∀ (index₀ : Fin A.teams) (slot : ℕ) (reference : ReferencePacket w d) (copy : BroadcastFrame)
    (advice : AdviceLayout) (fields : Pins.ProcessorFields (A.operands index₀ slot reference).layout)
    (header : List Bool)
    (_sameLayout : (A.operands index₀ slot reference).layout =
      G.pinLayout u (args u).ibase (args u).hbase (args u).starbase)
    {geo : Memory w}
    (_resident : BootResidence (F:=fields) A index₀ slot reference copy advice (pub u)
      (install SparseExterior.driver n (B u).start.routines)
      header (processorMemory (G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase) w)
      (reg u) (active u).1 geo)
    (gap : ℕ)
    {D ports : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin sa.cube.cells) (edgeID : N.Edge ↪ Fin sa.cube.cables)
    (portID : P ↪ Fin ports) (original : Fin frame.dataDir.entries → N.Site)
    (live : (Fin frame.dataDir.teams × Fin frame.dataDir.sites) ↪ P) (preRegs : Bank w) (usedPin profCost : ℕ)
    (_sources : PublishedPin sa frame.dataDir N cell edgeID portID original live A index₀ slot reference dest gap copy header
      fields (pub u) machine (active u).1 afterPin.1 afterPin.2 preRegs geo usedPin profCost)
    (epoch : Returns epochPlacement (pub u) machine afterPin.1 afterPin.2)
    (published : Returns Directory.ISA.program (pub u) machine epoch.val.2.1 epoch.val.2.2)
    {s z : Bank w} {after : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory sa.cube.n (Tally.selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub u) machine s
      published.val.2.2 es z after)
    (_written : ReturnedWriters sa.cube frame.dataDir frame.privatePlacement frame.livePlacement frame.cellOwner len frame.group
      (G.pinLayout u (frame.inputBase u) (frame.columnBase u) (frame.referenceBase u)) W)
    (_source : frame.source origin u=readings W.sharedInput),
    (ReaderKept A entries indices (B u).memory afterPin.2 (V).owned.val.2.2 ∧
      HeaderSeed sa p (pub u) (rawAddress A res side blocks cap) u.val (V).owned.val.2.2) ∧
      BootPins (pub u) copy reference.extension header published.val.2.2

/-- The genuine stored header and boot bounds give a readback on every
actual published route. Its full geometry is represented by the boot residence
carried along that execution. -/
theorem BootedPinStart.publishedReadbackFromBoot (A : StartupArena) {res side blocks hdrCap digits : ℕ}
    (p : PositiveFields res side blocks hdrCap sa.cube.teams sa.dim digits) (dest entries indices : ℕ)
    (copies : entries*w≤A.copied) (index : indices≤A.count)
    (posI : (args u).ibase=A.ibase) (posH : (args u).hbase=A.hbase) (frame : (pub u 0).val=A.frame)
    (size : A.header=PositiveFields.width res side blocks hdrCap sa.cube.teams sa.dim digits)
    (seed : HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (B u).memory)
    (above : A.next ≤ dest) (secondary : A.next ≤ sa.cube.header.header) :
    BootedPinStart.PublishedSourceReadback sa B active u A p dest entries indices := by
  intro wire hdr len p₀ op₀ r₀ m₀ who F origin proto amount v atOwned index₀ slot reference copy advice
    fields header sameLayout geo resident gap D ports P inst bits N cell edge port original live preRegs usedPin
    profCost sources epoch published s z after es W written source
  exact PreparationFrame.ReturnedOwnershipAt.publishedBanks sa B active u F origin atOwned A p copies index posI
    posH frame size seed index₀ slot reference copy advice fields header sameLayout resident dest gap above secondary
    N cell edge port original live preRegs usedPin profCost sources epoch published W written source

end TeamContraction

end BorderVNP
end Computability
end OAI
