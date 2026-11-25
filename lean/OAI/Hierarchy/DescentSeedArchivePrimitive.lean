import OAI.Hierarchy.DescentDatedSeedArchiveFlags
import OAI.Hierarchy.DescentNamedSeedEncoding
import OAI.Hierarchy.DescentOriginalSeedPrimitiveWords
import OAI.Hierarchy.DescentDatedSeedActualTokens

namespace OAI
/-! # The seed's issued primitive page on original nodes and every padded cell -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentSeedRoot DescentPackedSeed DescentInitialHost Chronology Catalyst
open DescentColonies
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {q fee : ℝ} {S : AtomSchedule} {k s z wire : ℕ}
section
variable {P Tag : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 z 3 wire s) (a : Archive W) (eqn : world r=W')
    {dictionary_ : Tag→List (List Bool)→F} (code : Encoding Tag dictionary_ a.bit)
local notation "named" => Eq.ndrec (motive := fun V => Archive V)
  (renamedArchive a (site r) (edge r)) eqn

theorem across_label (y : NodeOrder.All (named).bit) :
    (Palette.transported r a eqn code).atNode y = code.atNode (acrossNodes r a eqn y) := by
  cases eqn
  rfl

private structure LabelFact where
  statement : Prop
  checked : statement

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
open private carriedCoordinates Coordinates.nodes carriedNodes_eq
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
private def transferredLabels (label : NodeOrder.All a.bit → Tag)
    (previous : ∀ raw, code.atNode raw = label raw) : LabelFact := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  refine ⟨(∀ y : NodeOrder.All pkg.data.bit,
    (Palette.transported r a eqn code).atNode y = label (names y)), ?_⟩
  intro y
  exact (across_label r a eqn code y).trans
    ((previous (acrossNodes r a eqn y)).trans
      (congrArg label (DFunLike.congr_fun (carriedNodes_eq r a eqn) y).symm))

end
variable {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
  {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
  (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
  (op : RotorSpec) (menu : Runnable F op) {p : ℕ}
private def rawSeedLabel {copies : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies s).Choice) (raw : NodeOrder.All (Chronology.seedArchive X copies s c).bit) :
    Label G s z op := .inl (seedRole X copies c raw.1.1 raw.1.2)

private theorem seedLabelAtSource {copies : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies s).Choice) (raw : NodeOrder.All (Chronology.seedArchive X copies s c).bit) :
    (seeded (G := G) (s := s) (Z := z) (p := p) op menu X c).atNode raw =
      rawSeedLabel (G := G) (z := z) op X c raw := by
  rcases raw with ⟨⟨j,v⟩,node⟩
  exact seed_at (G := G) (Z := z) (p := p) op menu X copies c j v node

set_option maxHeartbeats 800000 in
private def originLabelFact : LabelFact :=
  transferredLabels o.raw (Chronology.seedArchive X S.copies s c) (linked_world X c digits o.seed)
    (seeded (G := G) (s := s) (Z := z) (p := p) op menu X c)
    (rawSeedLabel (G := G) (z := z) op X c)
    (seedLabelAtSource (G := G) (z := z) (p := p) op menu X c)

theorem Origin.original_label : (originLabelFact (p := p) o op menu).statement :=
  (originLabelFact (p := p) o op menu).checked

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentKernelHistory DescentLocalArchiveOrder DescentPrimitivePalette SeedNamed Computability.BorderVNP.Crossing
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDatedSeedStartup.Input
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem singleton_data {b H groups M : ℕ} (values : Fin H→Fin groups→Cell b) (row_ : Row H groups M) :
    (data (fun h g=>encode b 1 (fun _=>values h g)) row_).val=(data values row_).val :=by
  have singleton (h g) : (encode b 1 (fun _=>values h g)).val=(values h g).val :=by
    change (finFunctionFinEquiv (fun _ : Fin 1=>values h g)).val=_
    simp
  have casted (a b' : ℕ) (same : a=b') (v : Fin H→Fin groups→Cell a) :
      (data (fun h g=>(v h g).cast (congrArg (2^·) same)) row_).val=(data v row_).val :=by subst b';rfl
  have funEq : (fun h g=>encode b 1 (fun _=>values h g))=fun h g=>(values h g).cast
      (congrArg (2^·) (Nat.mul_one b).symm) :=by funext h g; exact Fin.ext (singleton h g)
  rw [funEq]
  exact casted b (b*1) (Nat.mul_one b).symm values

private theorem singleton_reads {b H groups M w : ℕ} (bank : ProtocolRAM.Bank) (m : Memory w)
    (values : Fin H → Fin groups → Cell b) (entered : Fin 1 → Fin H → Fin groups → Cell b)
    (one : ∀ n h g, entered n h g = values h g)
    (read : DescentPackedColony.Reads bank values M m) :
    DescentPackedColony.Reads bank (fun h g => encode b 1 (fun n => entered n h g)) M m := by
  have eqRows : (fun h g => encode b 1 (fun n => entered n h g)) =
      fun h g => encode b 1 (fun _ => values h g) := by
    funext h g
    apply congrArg (encode b 1)
    funext n
    exact one n h g
  rw [eqRows]
  intro row_
  exact (read row_).trans
    (congrArg (fun t : ℕ => (t : Computability.VPVNP.BurstRAM.Word w)) (singleton_data values row_).symm)


private theorem tokenAtSlot {Node Copy Vertex Label Cell : Type}
    (slot : Option Node) (rack : Option Vertex) (pick : Copy)
    (copy : Node → Copy) (vertex : Node → Vertex) (role : Copy → Vertex → Label)
    (lab : Node → Label) (token : Label → Cell) (zero : Cell)
    (host : slot.map vertex = rack) (same : ∀ y, slot = some y → pick = copy y)
    (labels : ∀ y, lab y = role (copy y) (vertex y)) :
    slot.elim zero (fun y => token (lab y)) = rack.elim zero (fun v => token (role pick v)) := by
  rw [←host]
  cases slot with
  | none => rfl
  | some y =>
    exact congrArg token ((labels y).trans (congrArg (fun i => role i (vertex y)) (same y rfl).symm))

open SeedNamed
open private namedArchiveGeometry originalGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  OrderedSlotGeometry.facts SlotGeometry.coordinates SlotGeometry.rackEntry SlotFact.checked
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
open private carriedCoordinates Coordinates.nodes carriedNodes_eq SeedNamed.Origin.seedReadsAt
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates

private structure PrimitiveCells {width blocks hosts groups : ℕ} (Ordering : Type) (fits : Prop)
    (original : Fin blocks → Fin hosts → Fin groups → Cell width) where
  atSlot : Ordering → fits → Fin blocks → Fin hosts → Fin groups → Fin 1 → Cell width
  scalar : ∀ nr ok x h g n, atSlot nr ok x h g n = original x h g

variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec) (menu : Runnable F op)
    {k cp p H : ℕ} (X : Approximation F cp p) (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "stored" => (ports).archive.roles.bank
local notation "bits₀" => printedBits G l.seedWidth Z op
variable {q ε : ℝ} {wire : ℕ} {choice : (initialGroup X S.copies l.seedWidth).Choice}
local notation "original" => Primitive.value X G op S.copies l.seedWidth Z k H g₀ hs choice digits

section Transported
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 Z 3 wire l.seedWidth) (a : Archive W) (eqn : world r = W')
    (oldNames : NodeOrder.All a.bit ≃ Fin S.copies × Vertex X)
    (before : ∀ y : NodeOrder.All a.bit,
      (r.vertex (r.placement.pos y.1).2).val = (Fintype.equivFin (Vertex X) (oldNames y).2).val ∧
      (r.placement.pos y.1).1 = (digits (oldNames y).1).1 ∧ r.placement.block y.1 = (digits (oldNames y).1).2)
    (one : ∀ v : W.graph.Site, Fintype.card (a.bit.recipe v).Node = 1)
local notation "geometry₀" => namedArchiveGeometry X digits publicWide op l payload Z r a eqn oldNames before one

set_option maxHeartbeats 500000 in
private def physicalCells {price : ℕ}
    (oldCode : Encoding (Label G l.seedWidth Z op) (dictionary G op menu price) a.bit)
    (oldLabel : ∀ y, oldCode.atNode y = .inl (seedRole X S.copies choice (oldNames y).1 (oldNames y).2)) :
    PrimitiveCells (OrderedSlotGeometry.ordering (geometry₀)) (OrderedSlotGeometry.room (geometry₀)) original := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  let labels := (Palette.transported r a eqn oldCode).atNode
  let slots := fun nr ok => slotAt ports (transport r eqn) pkg.data.bit nr ok
  refine ⟨fun nr ok x h g n => (slots nr ok x n h g).elim 0
    (fun y => token G l.seedWidth Z op (labels y)), ?_⟩
  intro nr ok x h g n
  let geom := OrderedSlotGeometry.facts (geometry₀) nr ok
  have host := SlotFact.checked (SlotGeometry.rackEntry geom) x n g h
  have coords := SlotFact.checked (SlotGeometry.coordinates geom) x n h g
  let role := fun j v => (Sum.inl (seedRole X S.copies choice j v) : Label G l.seedWidth Z op)
  refine tokenAtSlot (slots nr ok x n h g) (rack X hs h) (digits.symm (g,x))
    (fun y => (oldNames (names y)).1) (fun y => (oldNames (names y)).2) role labels
    (token G l.seedWidth Z op) 0 host ?_ ?_
  · intro y hit
    obtain ⟨block, _, group⟩ := coords y hit
    apply digits.injective
    exact (digits.apply_symm_apply (g,x)).trans (Prod.ext group block)
  · intro y
    exact (across_label r a eqn oldCode y).trans ((oldLabel (acrossNodes r a eqn y)).trans
      (congrArg (fun v => role (oldNames v).1 (oldNames v).2)
        (DFunLike.congr_fun (carriedNodes_eq r a eqn) y).symm))
end Transported

variable (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) choice digits)

set_option maxHeartbeats 500000 in
private def seedCells (price : ℕ) :=
  physicalCells G op menu X digits publicWide l payload Z o.raw (seedArchive X S.copies l.seedWidth choice)
    (linked_world X choice digits o.seed) (NodeOrder.seedSites X S.copies l.seedWidth choice)
    (fun y => SeedNamed.Origin.seedReadsAt o y.1) (DescentBundleHistory.initial_nodes X S.copies l.seedWidth choice)
    (seeded (G := G) (Z := Z) (p := price) op menu X choice)
    (seedLabelAtSource (G := G) (z := Z) (p := price) op menu X choice)

variable (number : OrderedSlotGeometry.ordering (originalGeometry X digits publicWide op l payload Z o))
    (room : OrderedSlotGeometry.room (originalGeometry X digits publicWide op l payload Z o)) (a : ℕ)

set_option maxHeartbeats 500000 in
/-- A scalar original token is already the whole one-node vector. In particular
an unpaid seed pin still materializes its one-based primitive label. -/
theorem seed_primitive {w : ℕ} (m : Memory w) (x : Block k)
    (read : Reads (stored x.val) ((original) x) (ports).roleLanes m) :
    Reads (stored x.val) (fun h g => encode bits₀ 1
      ((seedCells G op menu X digits publicWide l payload Z o a).atSlot number room x h g))
      (ports).roleLanes m := by
  let cells := seedCells G op menu X digits publicWide l payload Z o a
  exact singleton_reads (stored x.val) m ((original) x) (fun n h g => cells.atSlot number room x h g n)
    (fun n h g => cells.scalar number room x h g n) read

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
