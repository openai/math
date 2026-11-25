import OAI.Computability.BorderVNP.DiagonalPublishedOriginalCut
import OAI.Computability.BorderVNP.DiagonalSourceLookupWords

/-! # Simultaneous owned header, reader and source lookup on the selected public return -/

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

/-- All protected post operands use one selected preparation frame, its own
replayed origin and the identical emitted writer. The lookup is valid for
every subsequent gadget count on the actual local team. -/
theorem PreparationFrame.ReturnedOwnershipAt.postInputs
    {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners}
    (origin : HeaderExterior L exteriorHeader)
    (owned : F.ReturnedOwnershipAt sa origin ext template rows v history)
    (A : StartupArena) {res side blocks hdrCap digits : ℕ}
    (p : PositiveFields res side blocks hdrCap sa.cube.teams sa.dim digits)
    (dest entries indices : ℕ)
    (read : BootedPinStart.PublishedSourceReadback sa B active u A p dest entries indices)
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
    (gap : ℕ)
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
    (source : F.source origin u=readings W.sharedInput)
    (base : Fin 81 → Word w) (area cables cells raw team subtotal fresh slots gates outputs width off ell : ℕ)
    (literal : reference.extension=signedProfileExtension sa base F.dataDir area cables cells raw team subtotal
      fresh slots gates outputs width off ell)
    (room : sa.after.packed≤2^w) (head : (pub u 0).val+112 ≤ sa.cube.header.header) :
    (ReaderKept A entries indices (B u).memory afterPin.2 (V).owned.val.2.2 ∧
      HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (V).owned.val.2.2) ∧
      ∀ count, LookupPointers (sa.lookupFrame count) sa.after.ids (pub u 0).val (F.source origin u) := by
  obtain ⟨before,publishedBoot⟩ := read F origin owned index₀ slot reference copy advice fields header sameLayout
    resident gap N cell edgeID portID original live preRegs usedPin profCost sources epoch published W written source
  rw [literal] at publishedBoot
  refine ⟨before,fun count => ?_⟩
  rw [source]
  exact written.signed_lookup sa W base area cables cells raw team subtotal fresh slots gates outputs width off ell count
    publishedBoot room head

end TeamContraction

end BorderVNP
end Computability
end OAI
