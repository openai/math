import OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentSeedRegisterPorts
import OAI.Hierarchy.DescentOriginalPaddedNodes
import OAI.Hierarchy.DescentSeedSiteGeometry

namespace OAI
/-! # The original copy and vertex at each allocated date-zero host slot -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed DescentDatedSeedStartup
open DescentSeedInitialTable DescentColonies DescentSIMDLookup
open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory
open DescentPackedColony DescentRotor Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private structure PhysicalSlots where
  Node : Type
  blocks : ℕ
  lanes : ℕ
  hosts : ℕ
  groups : ℕ
  get : Fin blocks → Fin lanes → Fin hosts → Fin groups → Option Node
  host : Node → ℕ
  group : Node → ℕ
  block : Node → ℕ
  lane : Node → ℕ
  capacity : Node → ℕ
  lane_lt : ∀ y, lane y < capacity y
  get_iff : ∀ x n h g y, get x n h g = some y ↔
    host y = h.val ∧ group y = g.val ∧ block y = x.val ∧ n.val = lane y

private def archiveSlots {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k age grain degree wire hist : ℕ} (ports : DatePorts)
    (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B) : PhysicalSlots where
  Node := NodeOrder.All B
  blocks := 2^ports.venue.k
  lanes := ports.nodes
  hosts := ports.operandHosts
  groups := ports.venue.groups
  get := slotAt ports r B number room
  host := fun y => (r.vertex (r.placement.pos y.1).2).val
  group := fun y => (r.placement.pos y.1).1.val
  block := fun y => (r.placement.block y.1).val
  lane := fun y => (number y.1 y.2).val
  capacity := fun y => Fintype.card (B.recipe y.1).Node
  lane_lt := fun y => (number y.1 y.2).isLt
  get_iff := by
    rintro x n h g ⟨v,u⟩
    have law := Reached.NodeCells.atPhysical_some r B number
      (x.cast (congrArg (2^·) room.radix.symm)) n h (g.cast room.groups.symm) v u
    constructor
    · intro hit
      obtain ⟨host, group, block, lane⟩ := law.mp hit
      exact ⟨host, congrArg Fin.val group, congrArg Fin.val block, lane⟩
    · rintro ⟨host,group,block,lane⟩
      exact law.mpr ⟨host, Fin.ext group, Fin.ext block, lane⟩

private structure SeedSlotData (physical : PhysicalSlots) (I V : Type) where
  old : physical.Node → I × V
  oldInv : I × V → physical.Node
  old_right : ∀ p, old (oldInv p) = p
  digits : I ≃ Fin physical.groups × Fin physical.blocks
  seat : V ↪ Fin physical.hosts
  physical_read : ∀ y,
    physical.host y = (seat (old y).2).val ∧
    physical.group y = (digits (old y).1).1.val ∧
    physical.block y = (digits (old y).1).2.val
  lanes_one : physical.lanes = 1
  singleton : ∀ y, physical.capacity y = 1

section Geometry
variable {I V : Type} {physical : PhysicalSlots} (shape : SeedSlotData physical I V)

private theorem slotGeometryCoordinates (x : Fin physical.blocks) (n : Fin physical.lanes)
    (h : Fin physical.hosts) (g : Fin physical.groups) (y : physical.Node)
    (hit : physical.get x n h g = some y) :
    x = (shape.digits (shape.old y).1).2 ∧ h = shape.seat (shape.old y).2 ∧
      g = (shape.digits (shape.old y).1).1 := by
  obtain ⟨host, group, block, _lane⟩ := (physical.get_iff x n h g y).mp hit
  obtain ⟨oldHost, oldGroup, oldBlock⟩ := shape.physical_read y
  exact ⟨Fin.ext (block.symm.trans oldBlock), Fin.ext (host.symm.trans oldHost),
    Fin.ext (group.symm.trans oldGroup)⟩

private theorem slotGeometryHost (x : Fin physical.blocks) (n : Fin physical.lanes)
    (g : Fin physical.groups) (v : V) :
    ∃ y : physical.Node, physical.get x n (shape.seat v) g = some y ∧ (shape.old y).2 = v := by
  let p : I × V := (shape.digits.symm (g, x), v)
  let y := shape.oldInv p
  have back : shape.old y = p := shape.old_right p
  have vertex : (shape.old y).2 = v := congrArg Prod.snd back
  have pair : shape.digits (shape.old y).1 = (g, x) :=
    (congrArg (fun t : I × V => shape.digits t.1) back).trans (shape.digits.apply_symm_apply (g, x))
  obtain ⟨oldHost, oldGroup, oldBlock⟩ := shape.physical_read y
  have laneSmall : physical.lane y < 1 := (physical.lane_lt y).trans_le (shape.singleton y).le
  have nSmall : n.val < 1 := n.isLt.trans_le shape.lanes_one.le
  refine ⟨y, (physical.get_iff x n (shape.seat v) g y).mpr ?_, vertex⟩
  exact ⟨oldHost.trans (congrArg (fun w : V => (shape.seat w).val) vertex),
    oldGroup.trans (congrArg (fun t : Fin physical.groups × Fin physical.blocks => t.1.val) pair),
    oldBlock.trans (congrArg (fun t : Fin physical.groups × Fin physical.blocks => t.2.val) pair),
    by omega⟩

private theorem slotGeometryRack (rack : Fin physical.hosts → Option V)
    (rack_real : ∀ v, rack (shape.seat v) = some v)
    (rack_absent : ∀ h, (¬ ∃ v, shape.seat v = h) → rack h = none)
    (x : Fin physical.blocks) (n : Fin physical.lanes)
    (g : Fin physical.groups) (h : Fin physical.hosts) :
    (physical.get x n h g).map (fun y => (shape.old y).2) = rack h := by
  classical
  by_cases live : ∃ v, shape.seat v = h
  · obtain ⟨v, rfl⟩ := live
    obtain ⟨y, hit, vertex⟩ := slotGeometryHost shape x n g v
    rw [hit, Option.map_some]
    exact (congrArg some vertex).trans (rack_real v).symm
  · have empty : physical.get x n h g = none := by
      cases hit : physical.get x n h g with
      | none => rfl
      | some y =>
        have located := slotGeometryCoordinates shape x n h g y hit
        exact (live ⟨(shape.old y).2, located.2.1.symm⟩).elim
    rw [empty, rack_absent h live]
    rfl

end Geometry

private structure SlotFact where
  statement : Prop
  checked : statement

private structure SlotGeometry where
  coordinates : SlotFact
  occupied : SlotFact
  rackEntry : SlotFact

private def geometryFacts {I V : Type} {physical : PhysicalSlots} (shape : SeedSlotData physical I V)
    (table : Fin physical.hosts → Option V)
    (present : ∀ v, table (shape.seat v) = some v)
    (absent : ∀ h, (¬ ∃ v, shape.seat v = h) → table h = none) : SlotGeometry where
  coordinates := ⟨_, slotGeometryCoordinates shape⟩
  occupied := ⟨_, slotGeometryHost shape⟩
  rackEntry := ⟨_, slotGeometryRack shape table present absent⟩

section Archive
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q fee : ℝ}
    {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {cp pins k s grain wire H : ℕ} (X : Approximation F cp pins)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k)
    (publicWide : Fintype.card (Vertex X) ≤ H) (op : RotorSpec)
    (l : DescentDatedSeedStartup.Layout) (payload Z : ℕ)
    (r : Reached W G q fee S k 0 grain 3 wire s) (B : BitDescription W)
    (number : Local B)
local notation "ports" => initial G op X S.copies l k H (S.groupCount 0) payload Z
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)

private def archiveGeometry (room : RangeRoom ports r B)
    (names : NodeOrder.All B ≃ Fin S.copies × Vertex X)
    (readback : ∀ y : NodeOrder.All B,
      (r.vertex (r.placement.pos y.1).2).val = (Fintype.equivFin (Vertex X) (names y).2).val ∧
      (r.placement.pos y.1).1 = (digits (names y).1).1 ∧
      r.placement.block y.1 = (digits (names y).1).2)
    (one : ∀ v : W.graph.Site, Fintype.card (B.recipe v).Node = 1) : SlotGeometry := by
  let shape : SeedSlotData (archiveSlots ports r B number room) (Fin S.copies) (Vertex X) := {
    old := names
    oldInv := names.symm
    old_right := names.apply_symm_apply
    digits := digits
    seat := hs
    physical_read := fun y => ⟨(readback y).1,
      congrArg Fin.val (readback y).2.1, congrArg Fin.val (readback y).2.2⟩
    lanes_one := rfl
    singleton := fun y => one y.1 }
  exact geometryFacts shape (rack X hs) (rack_real X hs) (fun h miss => by
    unfold rack
    exact dite_eq_right miss)

private structure OrderedSlotGeometry where
  ordering : Type
  room : Prop
  facts : ordering → room → SlotGeometry

open Hierarchy.DescentSixParty.SeedNamed in
open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
open private carriedCoordinates Coordinates.nodes Coordinates.read Coordinates.single
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
private def namedArchiveGeometry {W' : MarkedWorld F d P bits}
    (a : Archive W) (eqn : world r = W')
    (oldNames : NodeOrder.All a.bit ≃ Fin S.copies × Vertex X)
    (previous : ∀ y : NodeOrder.All a.bit,
      (r.vertex (r.placement.pos y.1).2).val = (Fintype.equivFin (Vertex X) (oldNames y).2).val ∧
      (r.placement.pos y.1).1 = (digits (oldNames y).1).1 ∧
      r.placement.block y.1 = (digits (oldNames y).1).2)
    (single : ∀ v : W.graph.Site, Fintype.card (a.bit.recipe v).Node = 1) : OrderedSlotGeometry := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let coords := carriedCoordinates r a eqn pkg
  let names := Coordinates.nodes coords
  let current := transport r eqn
  refine ⟨Local pkg.data.bit, RangeRoom ports current pkg.data.bit, fun number room =>
    archiveGeometry X digits publicWide op l payload Z current pkg.data.bit number room
      (names.trans oldNames) ?_ (Coordinates.single coords single)⟩
  intro y
  have latest := Coordinates.read coords y
  have first := previous (names y)
  exact ⟨latest.1.trans first.1, latest.2.1.trans first.2.1, latest.2.2.trans first.2.2⟩
end Archive

variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q fee : ℝ}
    {cp pins k s grain wire H : ℕ} (X : Approximation F cp pins)
    {c : (initialGroup X S.copies s).Choice} (digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k)
    (publicWide : Fintype.card (Vertex X) ≤ H) (op : RotorSpec)
    (l : DescentDatedSeedStartup.Layout) (payload Z : ℕ)
    (o : SeedNamed.Origin (G:=G) (q:=q) (fee:=fee) (z:=grain) (wire:=wire) X c digits)
open private seedReadsAt
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
set_option maxHeartbeats 400000 in
private def originalGeometry : OrderedSlotGeometry :=
  namedArchiveGeometry X digits publicWide op l payload Z o.raw (seedArchive X S.copies s c)
    (SeedNamed.linked_world X c digits o.seed) (NodeOrder.seedSites X S.copies s c)
    (fun y => seedReadsAt o y.1) (initial_nodes X S.copies s c)

variable (number : (originalGeometry X digits publicWide op l payload Z o).ordering)
    (room : (originalGeometry X digits publicWide op l payload Z o).room)

theorem seed_slot_coordinates :
    ((originalGeometry X digits publicWide op l payload Z o).facts number room).coordinates.statement :=
  ((originalGeometry X digits publicWide op l payload Z o).facts number room).coordinates.checked

/-- Each allocated host has an original node, including public boundary hubs with an empty history. -/
theorem seed_slot_host :
    ((originalGeometry X digits publicWide op l payload Z o).facts number room).occupied.statement :=
  ((originalGeometry X digits publicWide op l payload Z o).facts number room).occupied.checked

theorem seed_slot_rack :
    ((originalGeometry X digits publicWide op l payload Z o).facts number room).rackEntry.statement :=
  ((originalGeometry X digits publicWide op l payload Z o).facts number room).rackEntry.checked

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
