import OAI.Hierarchy.DescentSeedTokenRun
import OAI.Hierarchy.DescentDatedSeedSlotGeometry
import OAI.Hierarchy.DescentDatedSeedOriginalNode
import OAI.Hierarchy.DescentArchiveRegisterFlag
import OAI.Hierarchy.DescentSeedCompleteImage
import OAI.Hierarchy.DescentSeedRegisterPorts
import OAI.Hierarchy.DescentOriginalPaddedNodes

namespace OAI
/-! # Initial occupancy and original flattened arity in the physical register pages -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed DescentDatedSeedStartup
open DescentDatedSeedStartup.Input DescentSeedInitialTable DescentColonies DescentSIMDLookup
open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentRetainedRangeDigits
open DescentPackedColony DescentRotor Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem seedPackedCells {Node Vertex : Type} (v : DescentDatedNodeMetadata.Chart) (one : v.nodes = 1)
    (Q : Fin v.hosts → Option ℕ) (rack : Fin v.hosts → Option Vertex)
    (old : Node → Vertex) (width : Vertex → ℕ)
    (slot : Fin v.nodes → Fin v.hosts → Fin v.groups → Option Node)
    (query : ∀ h, Q h = (rack h).map width)
    (observed : ∀ n h g, (slot n h g).map old = rack h)
    (f : Fin 2) (value : Fin v.nodes → Fin v.hosts → Fin v.groups → ℕ)
    (read : ∀ n h g, value n h g =
      (slot n h g).elim 0 (fun y => if f.val = 0 then 1 else width (old y))) :
    v.seedField Q f = fun h g => encode v.bits v.nodes (fun n => (value n h g : Cell v.bits)) := by
  funext h g
  change encode v.bits v.nodes (v.seedDigit Q f h) = _
  apply congrArg (encode v.bits v.nodes)
  funext n
  have atZero : n.val = 0 := by have small := n.isLt; omega
  rw [DescentDatedNodeMetadata.Chart.seedDigit, ite_eq_left atZero, query h, ← observed n h g, read n h g]
  cases hit : slot n h g <;> by_cases flag : f.val = 0 <;> simp [flag]

private theorem flagCells {Node Vertex : Type} (v : DescentDatedNodeMetadata.Chart) (one : v.nodes = 1)
    (Q : Fin v.hosts → Option ℕ) (rack : Fin v.hosts → Option Vertex)
    (old : Node → Vertex) (width : Vertex → ℕ)
    (slot : Fin v.nodes → Fin v.hosts → Fin v.groups → Option Node)
    (query : ∀ h, Q h = (rack h).map width)
    (observed : ∀ n h g, (slot n h g).map old = rack h)
    (flag : Fin v.nodes → Fin v.hosts → Fin v.groups → ℕ)
    (actual : ∀ n h g, flag n h g = if (slot n h g).isSome then 1 else 0) :
    v.seedField Q 0 = fun h g => encode v.bits v.nodes (fun n => (flag n h g : Cell v.bits)) := by
  apply seedPackedCells v one Q rack old width slot query observed 0 flag
  intro n h g
  rw [actual]
  cases slot n h g <;> rfl

private theorem arityNatCells {Node Vertex : Type} (v : DescentDatedNodeMetadata.Chart) (one : v.nodes = 1)
    (Q : Fin v.hosts → Option ℕ) (rack : Fin v.hosts → Option Vertex)
    (old : Node → Vertex) (width : Vertex → ℕ)
    (slot : Fin v.nodes → Fin v.hosts → Fin v.groups → Option Node)
    (query : ∀ h, Q h = (rack h).map width)
    (observed : ∀ n h g, (slot n h g).map old = rack h)
    (occ : Node → ℕ) (arity : ∀ y, occ y = width (old y)) :
    v.seedField Q 1 = fun h g => encode v.bits v.nodes (fun n =>
      (((slot n h g).elim (0 : ℕ) occ : ℕ) : Cell v.bits)) := by
  apply seedPackedCells v one Q rack old width slot query observed 1
    (fun n h g => (slot n h g).elim 0 occ)
  intro n h g
  cases hit : slot n h g with
  | none => rfl
  | some y => exact arity y

private theorem packedNatElim {Node : Type} (bits : ℕ) (found : Option Node) (occ : Node → ℕ) :
    ((found.elim (0 : ℕ) occ : ℕ) : Cell bits) =
      found.elim (0 : Cell bits) (fun y => (occ y : Cell bits)) := by
  cases found <;> simp

private theorem arityCells {Node Vertex : Type} (v : DescentDatedNodeMetadata.Chart) (one : v.nodes = 1)
    (Q : Fin v.hosts → Option ℕ) (rack : Fin v.hosts → Option Vertex)
    (old : Node → Vertex) (width : Vertex → ℕ)
    (slot : Fin v.nodes → Fin v.hosts → Fin v.groups → Option Node)
    (query : ∀ h, Q h = (rack h).map width)
    (observed : ∀ n h g, (slot n h g).map old = rack h)
    (occ : Node → ℕ) (arity : ∀ y, occ y = width (old y)) :
    v.seedField Q 1 = fun h g => encode v.bits v.nodes (fun n =>
      (slot n h g).elim (0 : Cell v.bits) (fun y => (occ y : Cell v.bits))) := by
  simpa only [packedNatElim] using
    arityNatCells v one Q rack old width slot query observed occ arity

private theorem archiveFlagZero {F P : Type} [Field F] [Fintype P] {d k grain degree wire hist : ℕ}
    {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} (r : Reached W G q ε S k 0 grain degree wire hist)
    (B : BitDescription W) (number : Local B) (ports : DatePorts) (room : RangeRoom ports r B)
    (x : Fin (2^ports.venue.k)) (n : Fin ports.nodes) (h : Fin ports.operandHosts)
    (g : Fin ports.venue.groups) :
    RegisterTimeline.archiveFlag r B number ports room x n h g =
      if (slotAt ports r B number room x n h g).isSome then 1 else 0 := by
  simp only [RegisterTimeline.archiveFlag, ite_true]

variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q fee : ℝ}
    {cp pins k s grain wire H : ℕ} (X : Approximation F cp pins)
    {c : (initialGroup X S.copies s).Choice} (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (op : RotorSpec) (l : DescentDatedSeedStartup.Layout) (payload Z : ℕ)
    (o : SeedNamed.Origin (G:=G) (q:=q) (fee:=fee) (z:=grain) (wire:=wire) X c digits)
local notation "ports" => initial G op X S.copies l k H (S.groupCount 0) payload Z
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H (S.groupCount 0) k
local notation "chart" => nodeChart l k H (S.groupCount 0)
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "cap" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H (S.groupCount 0) lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
variable (header : ℕ) {w : ℕ} (m : Memory w)
local notation "done" => completeImage G op X digits publicWide l header payload Z m

private theorem metadata_read (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (native : payload≤w) (space : cap<2^w) (x : Block k) (f : Fin 2) :
    Reads (metadataPage ports f x) ((chart).seedField Q f) l.operandLanes done :=by
  have div:=DescentDatedSeedStartup.Primitive.fences X S.copies l.seedWidth payload k H (S.groupCount 0) lanes finish
  have before:=div.1.trans div.2
  have fit:=(chart).seedFit top f x (before.trans_lt space)
  intro r
  have low : ((chart).seedBank top f x).base+(row H (S.groupCount 0) l.operandLanes r).val<finish:=
    (Nat.add_lt_add_left ((row H (S.groupCount 0) l.operandLanes r).isLt.trans_le fit.2) _).trans_le fit.1.2.2
  exact ((DescentDatedSeedStartup.Primitive.any X G op S.copies l.seedWidth Z payload k H (S.groupCount 0) lanes finish hs
    (afterCountImage X digits publicWide l header m) sourceSpace space native live).2.2 _ (.inl low)).trans
      ((chart).seedRead top Q (DescentPrivateHeader.initialized header (output X (Equiv.refl _) digits hs l m)) f x r)

open SeedNamed
open private namedArchiveGeometry originalGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  OrderedSlotGeometry.facts SlotGeometry.rackEntry SlotFact.checked
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
open private carriedCoordinates Coordinates.nodes SeedNamed.Origin.seedReadsAt
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
open private transferredArity ArityFact.checked
  from OAI.Hierarchy.DescentDatedSeedOriginalNode

private structure SeedFieldWords (v : DescentDatedNodeMetadata.Chart)
    (widthAt : Fin v.hosts → Option ℕ) (f : Fin 2) (O : Type) (valid : Prop) where
  words : O → valid → Fin v.blocks → Fin v.hosts → Fin v.groups → Cell (v.bits * v.nodes)
  emitted : ∀ number room x, v.seedField widthAt f = words number room x

section Transported
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 grain 3 wire s) (a : Archive W) (eqn : world r = W')
    (oldNames : NodeOrder.All a.bit ≃ Fin S.copies × Vertex X)
    (before : ∀ y : NodeOrder.All a.bit,
      (r.vertex (r.placement.pos y.1).2).val = (Fintype.equivFin (Vertex X) (oldNames y).2).val ∧
      (r.placement.pos y.1).1 = (digits (oldNames y).1).1 ∧ r.placement.block y.1 = (digits (oldNames y).1).2)
    (one : ∀ v : W.graph.Site, Fintype.card (a.bit.recipe v).Node = 1)
local notation "geometry₀" => namedArchiveGeometry X digits publicWide op l payload Z r a eqn oldNames before one

set_option maxHeartbeats 400000 in
private def physicalFlagWords [Fintype P] :
    SeedFieldWords chart Q 0 (OrderedSlotGeometry.ordering (geometry₀)) (OrderedSlotGeometry.room (geometry₀)) := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  let vertex := fun y => (oldNames (names y)).2
  let current := transport r eqn
  refine ⟨(fun nr ok x h g => encode l.operandBits 1 (fun n =>
    (RegisterTimeline.archiveFlag current pkg.data.bit nr ports ok x n h g : Cell l.operandBits))), ?_⟩
  intro nr ok x
  have rackAt := SlotFact.checked (SlotGeometry.rackEntry (OrderedSlotGeometry.facts (geometry₀) nr ok))
  exact flagCells chart rfl Q (rack X hs) vertex (fun v => legArity X v * l.groupsPerNode)
    (slotAt ports current pkg.data.bit nr ok x) (fun _ => rfl)
    (fun n h g => rackAt x n g h)
    (RegisterTimeline.archiveFlag current pkg.data.bit nr ports ok x)
    (archiveFlagZero current pkg.data.bit nr ports ok x)

set_option maxHeartbeats 400000 in
private def physicalArityWords {p R : ℕ} (hp : 0 < p) (sh : WorldShape p R a.bit)
    (groups : l.groupsPerNode = s/p)
    (counted : ∀ raw : NodeOrder.All a.bit, ((sh.sites raw.1).recipe hp).arity raw.2 =
      legArity X (oldNames raw).2 * (s/p)) :
    SeedFieldWords chart Q 1 (OrderedSlotGeometry.ordering (geometry₀)) (OrderedSlotGeometry.room (geometry₀)) := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  let vertex := fun y => (oldNames (names y)).2
  let current := transport r eqn
  let installed := pkg.carry (fun _ b => WorldShape p R b.bit) (sh.renamed (site r) (edge r))
  let lengthAt (y : NodeOrder.All pkg.data.bit) := (occurrences (installed.sites y.1) y.2).length
  refine ⟨(fun nr ok x h g => encode l.operandBits 1 (fun n =>
    (slotAt ports current pkg.data.bit nr ok x n h g).elim (0 : Cell l.operandBits)
      (fun y => (lengthAt y : Cell l.operandBits)))), ?_⟩
  intro nr ok x
  have rackAt := SlotFact.checked (SlotGeometry.rackEntry (OrderedSlotGeometry.facts (geometry₀) nr ok))
  have sizes := ArityFact.checked (transferredArity r a eqn hp sh (fun raw => legArity X (oldNames raw).2 * (s/p)) counted)
  exact arityCells chart rfl Q (rack X hs) vertex (fun v => legArity X v * l.groupsPerNode)
    (slotAt ports current pkg.data.bit nr ok x) (fun _ => rfl)
    (fun n h g => rackAt x n g h) lengthAt
    (fun y => (sizes y).trans (congrArg (fun n => legArity X (vertex y) * n) groups.symm))
end Transported

open private Origin.rawSeedCounted
  from OAI.Hierarchy.DescentDatedSeedOriginalNode in
set_option maxHeartbeats 400000 in
private def concreteArityWords {p R : ℕ} (hp : 0 < p) (units : 1 ≤ R) (width : p ∣ s)
    (groups : l.groupsPerNode = s/p) :=
  physicalArityWords X digits publicWide op l payload Z o.raw (seedArchive X S.copies s c)
    (linked_world X c digits o.seed) (NodeOrder.seedSites X S.copies s c)
    (fun y => SeedNamed.Origin.seedReadsAt o y.1) (initial_nodes X S.copies s c) hp
    (seedRetained X S.copies s hp units width c).shape groups
    (Origin.rawSeedCounted X c hp units width)

set_option maxHeartbeats 400000 in
private def concreteFlagWords :=
  physicalFlagWords X digits publicWide op l payload Z o.raw (seedArchive X S.copies s c)
    (linked_world X c digits o.seed) (NodeOrder.seedSites X S.copies s c)
    (fun y => SeedNamed.Origin.seedReadsAt o y.1) (initial_nodes X S.copies s c)

section Fields
variable (nr : OrderedSlotGeometry.ordering (originalGeometry X digits publicWide op l payload Z o))
    (ok : OrderedSlotGeometry.room (originalGeometry X digits publicWide op l payload Z o))
    (head : ℕ) {mw : ℕ} (mem : Memory mw)
local notation "output₀" => completeImage G op X digits publicWide l head payload Z mem

set_option maxHeartbeats 400000 in
theorem seed_nodeFlags (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (native : payload ≤ mw) (space : cap<2^mw) (x : Block k) :
    Reads (metadataPage ports 0 x)
      ((concreteFlagWords X digits publicWide op l payload Z o).words nr ok x) l.operandLanes output₀ := by
  exact Eq.subst (motive := fun rows => Reads (metadataPage ports 0 x) rows l.operandLanes output₀)
    ((concreteFlagWords X digits publicWide op l payload Z o).emitted nr ok x)
    (metadata_read X digits publicWide op l payload Z head mem sourceSpace live native space x 0)

set_option maxHeartbeats 400000 in
theorem seed_arity {p R : ℕ} (hp : 0<p) (units : 1≤R) (width : p∣s) (groups : l.groupsPerNode=s/p)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (native : payload ≤ mw) (space : cap<2^mw) (x : Block k) :
    Reads (metadataPage ports 1 x)
      ((concreteArityWords X digits publicWide op l payload Z o hp units width groups).words nr ok x) l.operandLanes output₀ := by
  exact Eq.subst (motive := fun rows => Reads (metadataPage ports 1 x) rows l.operandLanes output₀)
    ((concreteArityWords X digits publicWide op l payload Z o hp units width groups).emitted nr ok x)
    (metadata_read X digits publicWide op l payload Z head mem sourceSpace live native space x 1)
end Fields

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
