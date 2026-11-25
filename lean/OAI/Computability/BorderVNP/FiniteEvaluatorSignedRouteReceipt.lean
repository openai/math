import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteProduct

/-! # Physical input to a signed finite-field route and its exact path sum

The common returned delivery, all per-team pointers and program bounds are
recorded at the same decoded raw assignment. The conclusion derives the
distributed private fiber and the residual program weight from that evidence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open BorderVNP.Cube.TeamRows FiniteEvaluator RoutingISA RoutingISA.Transmission TeamContraction Routing
open VPVNP VPVNP.BurstRAM Diagonal.Layout DiagonalTallyPacketEmit
open scoped BigOperators Classical

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F}
variable {S : FieldSiteDirectory N T}

/-- A single reached routing branch and the shared, checked operands for its
native cube and private finite-field continuation. -/
structure SignedRouteReceipt (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (codec : Cells.Codec := .dense) where
  /-- Word width of this actual machine. -/
  w : ℕ
  /-- Address of the secondary cube header. -/
  header : ℕ
  /-- Length of the geometry profile before the cube declaration. -/
  profile : ℕ
  /-- Number of receiving cells in the common arena. -/
  cells : ℕ
  /-- Number of public cable slots. -/
  cables : ℕ
  /-- Reserved capacity of the transmission row arrays. -/
  maxRows : ℕ
  /-- Word capacity of each physical receiving-cell bank. -/
  stride : ℕ
  /-- The field deck installed by all participating teams. -/
  table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F
  /-- Report, fragment, geometry and scratch dimensions in the signed task allocation. -/
  params : SignedTaskArena.Parameters
  /-- Number of processors in each team. -/
  r : ℕ
  /-- Number of literal bits following the common validator program at each site. -/
  t : ℕ
  /-- Number of pinned Boolean inputs. -/
  d : ℕ
  /-- Number of exterior bits per processor and partner block. -/
  link : ℕ
  /-- Number of processor slots for interior wires. -/
  inner : ℕ
  /-- Common processor tape length, including padding. -/
  n : ℕ
  /-- Index type of the internal wires on a team. -/
  Edge : Type
  /-- Placement of program, literal, exterior and internal wire slots. -/
  G : Wiring R r t d link inner n Edge
  /-- Values of the pinned input bits. -/
  pin : Fin d → Bool
  /-- Common exterior Boolean wire assignment. -/
  ext : Exterior R r link → Bool
  /-- Layout of the two transmission legs and the shared prefix. -/
  wire : WireLayout (R+1) r link
  /-- The private and live rows decoded by the native demand producer. -/
  dir : Packing.Directory.Layout
  /-- Private-row placement as a cell number and relative word offset. -/
  pp : ℕ → ℕ × ℕ
  /-- Live-row placement as a cell number and relative word offset. -/
  lp : ℕ → ℕ × ℕ
  /-- The team assigned to a receiving cell. -/
  owner : ℕ → Fin (R+1)
  /-- Start of the destination banks of the completed delivery. -/
  origin : ℕ
  /-- Width between consecutive banks of that delivery. -/
  sendStride : ℕ
  /-- The complete native histories and pin layouts at the routing return. -/
  H : Fin (R+1) → TeamHistory w
  /-- Each team's prepared pin layout. -/
  pins : Fin (R+1) → Pins.Layout
  /-- Actual returned histories for the physical routing table. -/
  delivery : ReturnedDelivery G pin ext wire dir pp lp owner origin sendStride H pins
  /-- Layout used by the common-row writer. -/
  g : SharedRows.Layout
  /-- Word memories from which the teams wrote their common rows. -/
  src : Fin (R+1) → ℕ → ℕ
  /-- Team whose reference words identify the transmitted symbols. -/
  anchor : Fin (R+1)
  /-- Number of populated transmission records. -/
  count : ℕ
  /-- Each team's pointer to the geometry offset table. -/
  offsets : Fin (R+1) → ℕ
  /-- Each team's pointer to its signed task controls. -/
  control : Fin (R+1) → ℕ
  /-- Input length determining the installed macro interpreter clock. -/
  length : ℕ
  /-- Native instruction budget of each team. -/
  ticks : Fin (R+1) → ℕ
  /-- Maximum number of addressed words in one native call burst. -/
  burst : ℕ
  /-- Maximum number of private Boolean choices at any instruction in a bounded trace. -/
  clock : ℕ
  /-- Source evidence of the two actual native writers and the common transmitted symbols. -/
  writer : SharedWriters delivery g src
  symbols : SymbolFrame g (src anchor) L.blocks L.alternatives L.copies
    (Assignment.Routed.trueDeclaration L.bitWidth L.supply raw.1.1) (V.owners R raw.1.1)
  emits : sharedWords (Assignment.Routed.trueDeclaration L.bitWidth L.supply raw.1.1)
    (Assignment.Routed.physicalShared (V.owners R) raw.1) = delivery.receivedRows g (V.owners R raw.1.1)
  /-- Group streams, public directory and scanner words in the actual signed arena. -/
  banks : g.banks=(planArena L R header profile cells cables maxRows stride).pairBase
  spacing : g.stride=(planArena L R header profile cells cables maxRows stride).pairStride
  tab : ∀ u, delivery.table=(planArena L R header profile cells cables maxRows stride).table (readings (H u).pub 0) count
  frame : ∀ u, g.frame=readings (H u).pub 0
  room : ∀ u, (planArena L R header profile cells cables maxRows stride).ReplayRoom w (readings (H u).pub 0)
  scanner : ∀ u, (planArena L R header profile cells cables maxRows stride).ScannerWords (readings (H u).pub 0) u.val
    (chosen L.bitWidth L.supply raw.1.1).val (Fin.val ∘ V.owners R raw.1.1) (readings (H u).pub) (src u)
    (Assignment.Routed.trueDeclaration L.bitWidth L.supply raw.1.1).2
  /-- Published lookup pointers and four field-deck words in each reached memory. -/
  pointers : let sa := signedPlanArena L R header profile cells cables maxRows stride table params
    ∀ u, LookupPointers (sa.lookupFrame (V.teamPairs R raw u).length) sa.after.ids (readings (H u).pub 0) (src u)
  fields : let sa := signedPlanArena L R header profile cells cables maxRows stride table params
    let fresh := (planArena L R header profile cells cables maxRows stride).stop
    ∀ u, let f := sa.lookupFrame (V.teamPairs R raw u).length
      CubeConstants.Fields (CubeConstants.inArena f fresh L.dimension L.bitWidth L.copies L.alternatives L.supply)
        (readings (H u).pub 0) (CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply) (src u)
  /-- Physical address, actual count and bit-width limits of the lookup. -/
  wide : CubeDeck.minimumWidth F L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ w
  word : (signedPlanArena L R header profile cells cables maxRows stride table params).after.packed ≤ 2^w
  reportCap : ∀ u, (V.teamPairs R raw u).length ≤ params.report.vertices
  digits : argumentWidth L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ params.report.cubeWidth
  /-- Every path uses the public packet's fixed field table. -/
  fixed : ∀ p, L.table p=table
  /-- The chosen codec and native clock install the executed team macros. -/
  model : ∀ u, (H u).macros=TeamSiteEvents.macros (w:=w) (Cells.library F codec) (CompactMachine.nativeClock length)
  /-- The whole installation and owned-group prefix fits its team's clock. -/
  roomTicks : ∀ u, (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride
    (fun j => (H j).pub) u ≤ ticks u
  choice : 1 ≤ clock

namespace SignedRouteReceipt

variable {V : FieldRawLayout L S} {R : ℕ} {raw : V.Raw R} {codec : Cells.Codec}
variable (a : SignedRouteReceipt V R raw codec)

/-- Cube header and receiving bank layout of the actual routing history. -/
noncomputable abbrev arena := planArena L R a.header a.profile a.cells a.cables a.maxRows a.stride

/-- Complete signed allocation, including the fragment and report regions. -/
noncomputable abbrev signedArena := signedPlanArena L R a.header a.profile a.cells a.cables a.maxRows a.stride a.table a.params

/-- Public argument words, by team. -/
abbrev pub (u : Fin (R+1)) := (a.H u).pub

/-- Registers reached on the actual native route, by team. -/
abbrev regs (u : Fin (R+1)) := (a.H u).history.val.2.1

/-- Memory reached on the actual native route, by team. -/
abbrev original (u : Fin (R+1)) := (a.H u).history.val.2.2

/-- The installed macros for this route's true cell decoder and length. -/
noncomputable abbrev macros := TeamSiteEvents.macros (w:=a.w) (Cells.library F codec) (CompactMachine.nativeClock a.length)

/-- Lookup operands indexed by the actual distributed private choice. -/
noncomputable abbrev inputs (f : CubeTriple.Fiber raw.1.2) (u : Fin (R+1)) :=
  V.signedInputs R (V.withPrivate R raw f) u a.header a.profile a.cells a.cables a.maxRows a.stride a.table a.params

local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "group" => V.owners R (Sigma.fst (Prod.fst raw))
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply (Sigma.fst (Prod.fst raw)) axis group
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock a.length

set_option maxHeartbeats 1800000 in
/-- The real installer and owned-group returns form exactly the private fiber.
The product of bounded machine sums uses those same histories, with each
prefix's actual cost subtracted before the private continuation. -/
noncomputable abbrev Product (prep : Code) : Prop :=
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ ((u : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups a.table)
        (a.pub u) a.macros (a.regs u) (a.original u)),
      ((∀ f, let next := V.withPrivate R raw f
        (∀ u, let out := E f u
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 u).val) out.val.1.length ∧
            traceCost out.val.1 ≤ (CubeDeck.install a.table).slots+
              V.ownedTicks R raw a.header a.profile a.cells a.cables a.maxRows a.stride a.pub u ∧
            CubePacket.Prepared (a.inputs f u) (a.pub u) out.val.2.2 ∧
            CubePacket.Sources (a.inputs f u) (a.signedArena.tasks u.val (readings (a.pub u) 0) (a.offsets u) (a.control u)) ∧
            ∀ x, group (x.row axis).1=u →
              (V.bankData R next a.arena.header.packetBase a.arena.singleBank).Holds out.val.2.2 x) ∧
          (∏ u, ∏ i, (a.inputs f u).scalar i)=cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2) ∧
      (∏ u, boundedWeight (a.pub u) lib ret fuel (.seq (openCells a.table) (.seq prep privateReturns)) (a.regs u) (a.original u) (a.ticks u) a.burst a.clock) =
        ∑ f : CubeTriple.Fiber raw.1.2, ∏ u, let z := E f u
          boundedWeight (a.pub u) lib ret fuel (OwnedContinuation.codeFor prep) z.val.2.1 z.val.2.2
            (a.ticks u-traceCost z.val.1) a.burst a.clock)

set_option maxHeartbeats 1800000 in
/-- Split the native installation and group program from an arbitrary actual
private task stage, retaining the precise residual budgets. -/
theorem product_stage (prep : Code) : a.Product prep :=
  V.signed_route_product_stage (prep:=prep) (codec:=codec) R raw a.header a.profile a.cells a.cables a.maxRows a.stride a.table a.params
    a.length a.ticks a.burst a.clock a.writer a.symbols a.emits a.count a.offsets a.control
    a.banks a.spacing a.tab a.frame a.room a.scanner a.pointers a.fields a.wide a.word a.reportCap a.digits
    a.fixed a.model a.roomTicks a.choice

/-- The signed product for the finite evaluator's standard task preparation. -/
theorem product : a.Product prepareTasks := a.product_stage prepareTasks

end SignedRouteReceipt

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
