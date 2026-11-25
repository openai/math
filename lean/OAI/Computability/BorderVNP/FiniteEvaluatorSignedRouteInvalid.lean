import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteReject
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteSplit

/-! # Rejection of a malformed received row family by the finite field evaluator

The header parser, minimum check and shared writer all refer to the advertised
declaration, before any assignment has been recovered. If the constant installers
and owned traversals subsequently return on every team, their chronological tapes
and physical row banks recover one assignment with those exact received words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open BorderVNP.Cube BorderVNP.Cube.Physical RoutingISA VPVNP.BurstRAM

/-- The actual parser and subsequent first-minimum return, together with the
locations, fitted arithmetic and decoded lengths of the advertised declaration. -/
structure DeclarationReturn {n d w : ℕ} (decl : LengthDeclaration n d) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) where
  /-- Physical locations and widths read by the declaration parser. -/
  layout : HeaderDecode.Layout
  /-- Registers immediately before decoding the copied public declaration. -/
  regs : Bank w
  /-- Shared memory after the static header was installed. -/
  input : Memory w
  /-- The decoder trace and its returned registers and shared RAM. -/
  decoded : Evaluator.Returns HeaderDecode.program pub mac regs input
  /-- The minimum check starts at the endpoint of this same decoder trace. -/
  minimum : Evaluator.Returns CubeLengths.minimum pub mac decoded.val.2.1 decoded.val.2.2
  fits : HeaderDecode.Fits layout w
  atFrame : HeaderDecode.AtFrame layout (readings pub) (readings input)
  primary : readings pub 0+63 < 2^w
  header : layout.header+12 < 2^w
  totalsRoom : layout.totals+layout.a ≤ 2^w
  separate : layout.dense+layout.entries ≤ layout.totals ∨ layout.totals+layout.a ≤ layout.dense
  sumRoom : layout.d*layout.d*layout.cap < 2^w
  radix : layout.d=d
  axes : layout.a=n+1
  bounds : CubeLengths.Fits w (readings pub) (readings decoded.val.2.2)
  claimed : (CubeLengths.layout (readings pub) (readings decoded.val.2.2)).claimed=layout.dense
  totals : (CubeLengths.layout (readings pub) (readings decoded.val.2.2)).totals=layout.totals
  coordinates : (CubeLengths.layout (readings pub) (readings decoded.val.2.2)).coordinates=layout.a
  chosen : (CubeLengths.layout (readings pub) (readings decoded.val.2.2)).chosen=decl.1.val
  stored : CubeLengths.StoredRows (readings decoded.val.2.2) layout.dense decl.2

end FiniteEvaluator

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter DiagonalTallyPacketEmit FiniteEvaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin sendStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}

/-- Source operands of the shared writer and field installer. Their addresses
and word bounds are independent of a subsequent all-team owned return. -/
structure SharedCubeSource (delivery : ReturnedDelivery G pin ext wire dir pp lp owner origin sendStride H pins)
    (g : SharedRows.Layout) (src : Fin (R+1) → ℕ → ℕ) (ar : CubeArena.Layout)
    (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    {F : Type*} [Fintype F] (table : TableEntry ar.n ar.b ar.h ar.K ar.s → F) where
  /-- Reference team whose common row metadata the writer uses. -/
  anchor : Fin (R+1)
  /-- Placement of the field table, recipes, literals and result operands. -/
  template : Frame
  /-- Number of records in the public transmission table. -/
  count : ℕ
  symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group
  banks : g.banks=ar.pairBase
  spacing : g.stride=ar.pairStride
  room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0)
  tab : ∀ u, delivery.table=ar.table (readings (H u).pub 0) count
  frame : ∀ u, g.frame=readings (H u).pub 0
  scanner : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
    (readings (H u).pub) (src u) decl.2
  wide : CubeDeck.minimumWidth F ar.n ar.b ar.h ar.K ar.s ≤ w
  deck : CubeConstants.arenaEnd ar.stop (CubeDeck.entry table)<2^w
  fields : ∀ u, CubeConstants.Fields (CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s)
    (readings (H u).pub 0) (CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s) (src u)

end TeamContraction

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open FiniteEvaluator RoutingISA RoutingISA.Transmission TeamContraction Routing
open VPVNP VPVNP.BurstRAM Diagonal.Layout
open scoped BigOperators Classical

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R header profile cells cables maxRows stride : ℕ)
variable (decl : LengthDeclaration L.dimension L.alphabet) (group : Fin L.alphabet → Fin (R+1))
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable {r t d link inner n : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin sendStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {delivery : ReturnedDelivery G pin ext wire dir pp lp owner origin sendStride H pins}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
local notation "ar" => planArena L R header profile cells cables maxRows stride
local notation "pub" => fun u : Fin (R+1) => TeamHistory.pub (H u)
local notation "regs" => fun u : Fin (R+1) => Prod.fst (Prod.snd (Subtype.val (TeamHistory.history (H u))))
local notation "ram" => fun u : Fin (R+1) => Prod.snd (Prod.snd (Subtype.val (TeamHistory.history (H u))))
local notation "seen" => ReturnedDelivery.receivedRows delivery g group

variable (writer : SharedWriters delivery g src) (source : SharedCubeSource delivery g src (planArena L R header profile cells cables maxRows stride) decl group table)
variable (check : DeclarationReturn decl (H source.anchor).pub (H source.anchor).macros)
variable (scheduled : group = declaredTeam (planArena L R header profile cells cables maxRows stride) decl L.label V.recv V.dataWidth R) (alternatives : 1 ≤ L.alternatives)

include writer source check scheduled alternatives in
/-- Every jointly returning field-deck installer and owned traversal recovers a
unique routed assignment on its actual split memory and chronological events. -/
theorem observed_of_route_returns {mc : Fin (R+1) → TeamOpcode.Macros w 8} (model : ∀ u, (H u).macros=mc u)
    (paths : ∀ u, Evaluator.Returns (CubeTriple.installGroups table) ((pub) u) (mc u) ((regs) u) ((ram) u)) :
    ∃! q, ObservedOwned ar decl group (CubeTriple.splitTeams ar table paths) (V.owners R) seen q := by
  have handoff := writer.splitHandoff ar decl group table source.template source.count paths model
    source.banks source.spacing source.room source.tab source.frame source.scanner source.wide source.deck source.fields
  have room := source.room source.anchor
  have blocks := Nat.pos_of_mul_pos_right room.payload
  have before := room.primary
  have space := LocalRow.space_of_arena ar w (readings (H source.anchor).pub 0) room.axes room.alphabet blocks
    (by omega) room.stopFit room.fixedFit room.positive
  exact (writer.recover_owned_family ar decl L.label V.recv V.dataWidth group (CubeTriple.splitTeams ar table paths)
    scheduled source.symbols handoff alternatives space.2.1.le space.2.2 check.layout check.decoded.property check.minimum.property
    check.fits check.atFrame check.primary check.header check.totalsRoom check.separate check.sumRoom check.radix check.axes
    check.bounds check.claimed check.totals check.coordinates check.chosen (check.claimed.symm ▸ check.stored)).1

include writer source check scheduled alternatives in
/-- Joint returns force membership of the literal delivered declaration and common
word lists in the range of the field network's received-word map. -/
theorem received_of_route_returns {mc : Fin (R+1) → TeamOpcode.Macros w 8} (model : ∀ u, (H u).macros=mc u)
    (paths : ∀ u, Evaluator.Returns (CubeTriple.installGroups table) ((pub) u) (mc u) ((regs) u) ((ram) u)) :
    (decl,seen) ∈ Set.range (V.receivedWords R) := by
  obtain ⟨q,obs,_⟩ := V.observed_of_route_returns R header profile cells cables maxRows stride decl group table
    writer source check scheduled alternatives model paths
  exact V.observed_received R header profile cells cables maxRows stride decl group seen _ obs

variable (length : ℕ) (codec : Cells.Codec) (prep : RoutingISA.Code)
variable (ticks : Fin (R+1) → ℕ) (burst clock : ℕ)
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock length
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "assembled" => Code.seq (openCells table) (Code.seq prep privateReturns)

include writer source check scheduled alternatives in
/-- A physical route whose received pair is absent contributes zero to the
all-team product for every residual clock and private preparation program. -/
theorem malformed_route_zero (model : ∀ u, (H u).macros=mac) (invalid : (decl,seen) ∉ Set.range (V.receivedWords R)) :
    (∏ u, boundedWeight ((pub) u) lib ret fuel assembled ((regs) u) ((ram) u) (ticks u) burst clock)=0 := by
  apply V.invalid_received_zero R header profile cells cables maxRows stride decl group seen table length codec prep
    pub regs ram ticks burst clock _ invalid
  intro paths
  obtain ⟨q,obs,_⟩ := V.observed_of_route_returns R header profile cells cables maxRows stride decl group table
    writer source check scheduled alternatives model paths
  exact ⟨_,q,obs⟩

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
