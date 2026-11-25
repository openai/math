import OAI.Computability.BorderVNP.DiagonalFrozenControlSources
import OAI.Computability.BorderVNP.FiniteEvaluatorPhysicalControlReturns
import OAI.Computability.BorderVNP.FiniteEvaluatorReportPublishedWidths
import OAI.Computability.BorderVNP.DiagonalPinnedGuards

/-! # Checking physical endpoint padding after the frozen signed packet is read -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube Physical Scatter TeamRows DiagonalTallyPacketEmit FiniteEvaluator Evaluator
open BorderVNP.Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open NativeIntervals HostAddress VPVNP.MotifBase Diagonal.ExternalSew
open BottomReports BundleSort Diagonal.ExternalSew.FieldExport

/-- The state supplied to a team's first control scan after its real
owned return. Its immutable low words still come from the entered directory. -/
structure FrozenControlEntry (task : SignedTaskArena.Layout) (prog : OpenSuffix.Inputs)
    (base actual control offsets w : ℕ) (supplied : Fin task.cube.cells → ℕ) (entry output : ℕ → ℕ) : Prop where
  frame : actual=base
  frameEnd : base+112≤control
  ready : OpenSuffix.Ready prog actual output w
  placement : OpenSuffix.Placement prog task.cube task.before base output
  retained : CubeAllocation.HostRetention task.cube base entry entry output
  controlWord : output (base+92)=control
  controls : ∀ j : Fin 37, output (control+j.val)=task.controls j.val
  receive : ∀ c, output (offsets+2*task.cube.cables+c.val)=supplied c

/-- The same physical writer before and after its owned return. The low
report counts and original opener operands are read from the writer input. -/
structure FrozenControlReadback (task : SignedTaskArena.Layout) (prog : OpenSuffix.Inputs)
    (team base actual control offsets live ports bundles count w : ℕ) (supplied : Fin task.cube.cells → ℕ)
    (entry output : ℕ → ℕ) : Prop where
  owned : FrozenControlEntry task prog base actual control offsets w supplied entry output
  fields : task.OpenFields team base offsets control live ports bundles entry
  controlWords : ∀ j : Fin 37,entry (control+j.val)=task.controls j.val
  rows : entry (base+9) ≤ count
  cells : entry (base+11)=task.cube.cells

/-- Read the report descriptors, zero address and parameter count at the owned
output after their actual predecessor supplied the three signed frame words. -/
theorem FrozenControlEntry.report_inputs {task : SignedTaskArena.Layout} {prog : OpenSuffix.Inputs}
    {base actual control offsets w : ℕ} {supplied entry output}
    (h : FrozenControlEntry task prog base actual control offsets w supplied entry output)
    (data : entry (base+44)=task.after.descriptors ∧ entry (base+81)=task.cube.stop ∧
      entry (base+95)=task.p.parameters) :
    output (base+44)=task.after.descriptors ∧ output (base+81)=task.cube.stop ∧ output (base+95)=task.p.parameters := by
  have copy (j : ℕ) (hj : j<112) (n13 : j≠13) (n46 : j≠46) : output (base+j)=entry (base+j) :=
    h.retained.lower _ (by have := h.retained.primary; omega) (by omega) (by omega)
  exact ⟨(copy 44 (by decide) (by decide) (by decide)).trans data.1,
    (copy 81 (by decide) (by decide) (by decide)).trans data.2.1,
    (copy 95 (by decide) (by decide) (by decide)).trans data.2.2⟩

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    (task : SignedTaskArena.Layout)
    {decl : LengthDeclaration task.cube.n task.cube.header.d} {group : Fin task.cube.header.d → Fin (R+1)}
    {F : TeamRows.Returns (Fin (R+1)) task.cube w}
    {owners : (Packet task.cube.n task.cube.header.d task.cube.header.blocks → Selector task.cube.n task.cube.K task.cube.h) →
      Fin task.cube.header.d → Fin (R+1)}
    {template : Frame} {id : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ} {count : ℕ}

variable {dim sites ports cellBits lenBits geometryBits geoOrigin m next gap bankBits reportWidth broadcast : ℕ}
    {P : Type} {σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin ports)
    (fields : Fields sites task.cube.cables ports task.cube.cells cellBits lenBits geometryBits σ) (x : σ → Bool)
    (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (shape : Fin D.entries → BottomReports.BundleSort.Shape) (valid : VPVNP.VerifierNetwork.Frame σ Unit)
    (il : NativeIntervals.Layout) (previous dir : Fin (R+1) → ℕ → ℕ)
    {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin (R+1) → Fin m ↪o Fin il.count}
    {label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d}
    {hz : task.cube.header.d^(task.cube.n+1)=il.alphabet}
    (rows : ∀ u, PhysicalRows N cell il (previous u) ord (row u) Fin.valEmbedding label
      (productCode task.cube.n task.cube.header.d il.alphabet hz))
    (interval : ∀ u, il.Image (previous u) il.count (dir u))
    (packing : ∀ v, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) v ≤ task.cube.header.blocks*(task.cube.h*task.cube.b))

local notation "tables" => bases geoOrigin task.cube.cables task.cube.cells D.entries
local notation "ctrl" => controlsBase geoOrigin task.cube.cables task.cube.cells D.entries (D.teams*D.sites)
local notation "plan" => privateLayout il.frame geoOrigin task.cube.cables task.cube.cells D.entries D.description gap
local notation3 (prettyPrint := false) "banks" => task.cube.cellWriter il.frame ctrl decl.1
local notation "old" => siteID ∘ original
local notation3 (prettyPrint := false) "headers" => geometryHeaders fields old D.description (bankConfig banks gap valid) shape

variable (profile placed : Fin (R+1) → Memory w)
local notation3 (prettyPrint := false) "published(" u ")" => Directory.ISA.publish (placed u) il.frame next (D.directory pp lp)
variable {rr rt : Fin (R+1) → Bank w} {last : Fin (R+1) → Memory w} {es : Fin (R+1) → List (TeamRAM.Event w)}
    (W : ∀ u, WriterHistory task.cube.n reportWidth (H u).pub (H u).macros (rr u)
      (Directory.ISA.publish (placed u) il.frame next (D.directory pp lp)) (es u) (rt u) (last u))
local notation3 (prettyPrint := false) "bundle(" u ")" => fun i : Fin D.entries =>
  geometryHeader (Retains.id N) siteID fields (x:=x) plan (readings (W u).dataInput) task.cube.hostDirectory original i
    (shape i).copies (shape i).fine (shape i).incoming (shape i).cap


variable (valuation : Fin (R+1) → σ → Bool) (entryMem : Fin (R+1) → Memory w)
    (actualWriters : ∀ u, WriterHistory task.cube.n reportWidth (H u).pub (H u).macros (rr u)
      (entryMem u) (es u) (rt u) (last u))

local notation3 (prettyPrint := false) "actualBundle(" u ")" => fun i : Fin D.entries =>
  geometryHeader (Retains.id N) siteID fields (x:=valuation u) plan (readings (actualWriters u).dataInput)
    task.cube.hostDirectory original i (shape i).copies (shape i).fine (shape i).incoming (shape i).cap

set_option maxRecDepth 6500
set_option maxHeartbeats 1800000
include rows interval in
/-- On an actual returned cube assignment the published placement and the
two physical sort arrays supply all preconditions of the host, bundle and
control writers after the endpoint test. The resulting family returns exactly
for packed assignments whose unused bits are zero on both sides. -/
theorem SharedWriters.frozen_control_tests_at (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners}
    (receipt : ObservedOwned task.cube decl group F owners (f.receivedRows g group) q)
    (entered : ∀ u, entryMem u=published(u))
    (ready : ∀ u, DataReady (H u).pub (actualWriters u).dataInput)
    (records : ∀ u, (DataWriter.layout (readings (H u).pub) (readings (actualWriters u).dataInput)).output=task.cube.records)
    (shared : ∀ u, src u=readings (actualWriters u).sharedInput)
    (fit : ∀ u, il.Fits w (previous u)) (physical : ∀ u, il.Fields (previous u)) (primary : ∀ u, il.frame=readings (H u).pub 0)
    (space : ∀ u, HostScatter.CableColumns task.cube il.frame il (previous u)) (widths : il.widths=task.cube.widthBase)
    (low : ∀ u z, z<task.cube.publicBase → dir u z=readings (published(u)) z)
    (entry : ∀ u, NativeEntry task.cube il.frame ctrl decl.1 R (LocalRow.powerHeaderImage task.cube broadcast (dir u))
      (readings (published(u))) (readings (actualWriters u).dataInput))
    (pointers : ∀ u, CubeAllocation.HostPointers task.cube il.frame (readings (published(u))))
    (rep : ∀ u, Represents N cell aux siteID edgeID portID fields (valuation u)) (codes : ∀ c, (fields.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^geometryBits)
    (cableHeader : ∀ u, Header il.frame geoOrigin task.cube.cables task.cube.cells D.entries (readings (published(u))))
    (image : ∀ u, Image fields old (portID ∘ live) (valuation u) geoOrigin (readings (profile u)))
    (room : task.OpenRoom il.frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (2^bankBits) w)
    (nextFit : il.frame+112 ≤ next) (reserve : next+7*D.candidates ≤ geoOrigin)
    (payload : ctrl ≤ task.p.bundlePayload) (rank : task.p.bundleInverse = task.p.bundlePayload+2^bankBits)
    (ctrlFit : ∀ j : Fin 37, task.controls j.val < 2^geometryBits)
    (boot : ∀ u, task.OpenFields u.val il.frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (readings (profile u)))
    (placement : ∀ u, (plan).Image (readings (profile u)) D.entries (readings (placed u)))
    (positive : 0<task.cube.header.d) (keysFit : task.cube.cells < 2^lenBits)
    (descFit : D.description < 2^geometryBits) (scanFit : 2^Nat.clog 2 D.entries*D.description < 2^geometryBits)
    (copies : ∀ i, (shape i).copies < 2^geometryBits)
    (strideFit : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^geometryBits)
    (capacity : ∀ c, suppliedSize N cell c+gap+Directory.DataSlabs.size (cell ∘ original) (fun _ => D.description) c ≤ task.cube.cellStride)
    (controls : ∀ u (j : Fin 37), readings (profile u) (ctrl+j.val)=task.controls j.val)
    (sorted : ∀ u (j : Fin (2^bankBits+2^bankBits)), readings (profile u) (task.p.bundlePayload+j.val) =
      ParseBatchSort.value (fun v => (CellPacketGeometry.geometry (source task.cube.cells bankBits headers)).eval (valuation u) (.inl (j,v)))) :
    let program := fun u : Fin (R+1) => task.openInputs u.val il.frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites)
      D.entries bankBits (cell ∘ original) (actualBundle(u))
    OpenSuffix.ControlFamily program F.pub F.macros F.finalRegs F.output
      (NativeAssignments.RoutedPins N cell owners (packedSlotEmbedding N cell ord label task.cube.header.blocks (task.cube.h*task.cube.b) packing) q) ∧
    ∀ u, FrozenControlReadback task (program u) u.val il.frame (F.pub u 0).val ctrl (tables).ends (tables).livePairs
      (D.teams*D.sites) D.entries (D.directory pp lp).length w (fun c => suppliedSize N cell c)
      (readings (actualWriters u).dataInput) (readings (F.output u)) := by
  replace entered := funext entered
  subst entryMem
  intro program
  have openAt (u : Fin (R+1)) := (entry u).open_sources_of_frozen_words task D decl.1 pp lp (Retains.id N) cell aux
    siteID edgeID portID original live fields (valuation u) shape valid (profile u) (placed u) (readings (actualWriters u).dataInput) room
    nextFit reserve payload rank ctrlFit (boot u) (placement u) positive keysFit descFit scanFit copies strideFit
    codes fieldRoom capacity (rep u) (image u) (controls u) (sorted u)
  have before : geoOrigin+5*task.cube.cables ≤ task.cube.header.header := by
    have h := room.controlEnd
    dsimp only [controlsBase,bases] at h
    omega
  have prior (u : Fin (R+1)) (z : ℕ) (lo : geoOrigin ≤ z) (hi : z<geoOrigin+5*task.cube.cables) :
      readings (published(u)) z=readings (profile u) z :=
    published_geometry pp lp (placement u) nextFit reserve z lo (by dsimp only [bases]; omega)
  have first : il.frame+112≤ctrl := by dsimp only [controlsBase,bases]; omega
  let currentBundle (u : Fin (R+1)) (i : Fin D.entries) :=
    geometryHeader (Retains.id N) siteID fields (x:=valuation u) plan (readings (actualWriters u).dataInput)
      task.cube.hostDirectory original i (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
  have localData (u : Fin (R+1)) := writer.returned_control_entry N cell aux siteID edgeID portID fields il
    (previous u) (dir u) (rows u) (interval u) packing symbols handoff receipt u (actualWriters u) (ready u) (records u)
    (shared u) (fit u) (physical u) (primary u) (space u) widths (low u) (entry u) (pointers u) (rep u) codes fieldRoom
    (fun c => by have bound := capacity c; omega) (cableHeader u) (image u) (prior u) (by omega) before task rfl
    (cell ∘ original) (currentBundle u) (openAt u).1 (openAt u).2.1 room rank (openAt u).2.2 first payload
  obtain ⟨endBanks,head⟩ := receipt.padding_family rows interval (fun u => (localData u).1) anchor
  constructor
  · apply OpenSuffix.ControlFamily.of_ready (fun u => (localData u).2.1)
    exact OpenSuffix.team_returns_iff_pins (rows anchor) (interval anchor) packing program F.pub F.macros F.finalRegs
      F.output (fun u => (localData u).2.1) endBanks head
  · intro u
    have base : (F.pub u 0).val=il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans (primary u).symm
    have native : NativeEntry task.cube (readings (H u).pub 0) ctrl decl.1 R
        (LocalRow.powerHeaderImage task.cube broadcast (dir u)) (readings (published(u))) (readings (actualWriters u).dataInput) := by
      rw [←primary u]
      exact entry u
    have countLo := (entry u).low (il.frame+9) (by have := room.controlEnd; omega)
    have cellsLo := (entry u).low (il.frame+11) (by have := room.controlEnd; omega)
    have countBound : readings (actualWriters u).dataInput (il.frame+9) ≤ (D.directory pp lp).length := by
      refine countLo.trans_le ?_
      change (Directory.ISA.publish (placed u) il.frame next (D.directory pp lp) (il.frame+9)).val ≤ _
      rw [Directory.ISA.publish,Function.update_self]
      exact Nat.mod_le ..
    refine ⟨?_,(openAt u).1,(openAt u).2.1,countBound,cellsLo.trans (cableHeader u).cells⟩
    have keep := writer.owned_host_retention symbols handoff receipt u (actualWriters u) (ready u) (records u) (shared u)
      _ native
    change CubeAllocation.HostRetention task.cube (F.pub u 0).val
      (readings (published(u))) (readings (actualWriters u).dataInput) (readings (F.output u)) at keep
    rw [base] at keep
    have preserved := keep.from_written (entry u).low
    refine ⟨base,first,(localData u).2.1,?_,preserved,?_,?_,?_⟩
    · rw [←base]
      exact (localData u).2.2
    · exact (preserved.lower _ (by have := preserved.primary; omega) (by omega) (by omega)).trans (openAt u).1.controlWord
    · intro j
      exact (preserved.lower _ (by have := room.controlEnd; omega) (by omega) (by omega)).trans ((openAt u).2.1 j)

    · intro c
      let addr := (tables).ends+2*task.cube.cables+c.val
      have upper : addr < ctrl := by
        dsimp only [addr,bases,controlsBase]
        have hc := c.isLt
        omega
      have lowAddr : il.frame+112 ≤ addr := by
        dsimp only [addr,bases]
        omega
      have earlier := (image u).published_supplied N cell aux siteID edgeID portID fields D original live pp lp
        (rep u) codes fieldRoom (placement u) nextFit reserve c
      have secondary : addr<task.cube.header.header := by have := room.controlEnd; omega
      exact ((preserved.lower addr secondary (by omega) (by omega)).trans ((entry u).low addr secondary)).trans earlier

set_option maxRecDepth 6500
set_option maxHeartbeats 1800000
include rows interval in
/-- On an actual returned cube assignment the published placement and the
two physical sort arrays supply all preconditions of the host, bundle and
control writers after the endpoint test. The resulting family returns exactly
for packed assignments whose unused bits are zero on both sides. -/
theorem SharedWriters.frozen_control_tests (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners}
    (receipt : ObservedOwned task.cube decl group F owners (f.receivedRows g group) q)
    (ready : ∀ u, DataReady (H u).pub (W u).dataInput)
    (records : ∀ u, (DataWriter.layout (readings (H u).pub) (readings (W u).dataInput)).output=task.cube.records)
    (shared : ∀ u, src u=readings (W u).sharedInput)
    (fit : ∀ u, il.Fits w (previous u)) (physical : ∀ u, il.Fields (previous u)) (primary : ∀ u, il.frame=readings (H u).pub 0)
    (space : ∀ u, HostScatter.CableColumns task.cube il.frame il (previous u)) (widths : il.widths=task.cube.widthBase)
    (low : ∀ u z, z<task.cube.publicBase → dir u z=readings (published(u)) z)
    (entry : ∀ u, NativeEntry task.cube il.frame ctrl decl.1 R (LocalRow.powerHeaderImage task.cube broadcast (dir u))
      (readings (published(u))) (readings (W u).dataInput))
    (pointers : ∀ u, CubeAllocation.HostPointers task.cube il.frame (readings (published(u))))
    (rep : Represents N cell aux siteID edgeID portID fields x) (codes : ∀ c, (fields.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^geometryBits)
    (cableHeader : ∀ u, Header il.frame geoOrigin task.cube.cables task.cube.cells D.entries (readings (published(u))))
    (image : ∀ u, Image fields old (portID ∘ live) x geoOrigin (readings (profile u)))
    (room : task.OpenRoom il.frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (2^bankBits) w)
    (nextFit : il.frame+112 ≤ next) (reserve : next+7*D.candidates ≤ geoOrigin)
    (payload : ctrl ≤ task.p.bundlePayload) (rank : task.p.bundleInverse = task.p.bundlePayload+2^bankBits)
    (ctrlFit : ∀ j : Fin 37, task.controls j.val < 2^geometryBits)
    (boot : ∀ u, task.OpenFields u.val il.frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (readings (profile u)))
    (placement : ∀ u, (plan).Image (readings (profile u)) D.entries (readings (placed u)))
    (positive : 0<task.cube.header.d) (keysFit : task.cube.cells < 2^lenBits)
    (descFit : D.description < 2^geometryBits) (scanFit : 2^Nat.clog 2 D.entries*D.description < 2^geometryBits)
    (copies : ∀ i, (shape i).copies < 2^geometryBits)
    (strideFit : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^geometryBits)
    (capacity : ∀ c, suppliedSize N cell c+gap+Directory.DataSlabs.size (cell ∘ original) (fun _ => D.description) c ≤ task.cube.cellStride)
    (controls : ∀ u (j : Fin 37), readings (profile u) (ctrl+j.val)=task.controls j.val)
    (sorted : ∀ u (j : Fin (2^bankBits+2^bankBits)), readings (profile u) (task.p.bundlePayload+j.val) =
      ParseBatchSort.value (fun v => (CellPacketGeometry.geometry (source task.cube.cells bankBits headers)).eval x (.inl (j,v)))) :
    let program := fun u : Fin (R+1) => task.openInputs u.val il.frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites)
      D.entries bankBits (cell ∘ original) (bundle(u))
    OpenSuffix.ControlFamily program F.pub F.macros F.finalRegs F.output
      (NativeAssignments.RoutedPins N cell owners (packedSlotEmbedding N cell ord label task.cube.header.blocks (task.cube.h*task.cube.b) packing) q) ∧
    ∀ u, FrozenControlEntry task (program u) il.frame (F.pub u 0).val ctrl (tables).ends w (fun c => suppliedSize N cell c)
      (readings (W u).dataInput) (readings (F.output u)) := by
  have physicalReadback := writer.frozen_control_tests_at task N cell aux siteID edgeID portID fields original live shape valid il previous
    dir rows interval packing profile placed (fun _ => x) _ W symbols handoff receipt (fun _ => rfl) ready records
    shared fit physical primary space widths low entry pointers (fun _ => rep) codes fieldRoom cableHeader image room
    nextFit reserve payload rank ctrlFit boot placement positive keysFit descFit scanFit copies strideFit capacity controls sorted
  exact ⟨physicalReadback.1,fun u => (physicalReadback.2 u).owned⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
