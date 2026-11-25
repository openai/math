import OAI.Hierarchy.DescentSeedRegisteredLivePointers
import OAI.Hierarchy.DescentSeedRenamedPointers
import OAI.Hierarchy.DescentDatedSeedSlotGeometry
import OAI.Hierarchy.DescentDatedSeedOriginalNode

namespace OAI
/-! # Seed pointer pages for every actual slot of the first named archive -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentKernelHistory DescentRetainedRangeDigits DescentLocalArchiveOrder SeedNamed Computability.BorderVNP.Crossing
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan DescentRotor
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
open DescentBundleHistory

private structure HeaderRows (ports : DatePorts) where
  Node : Type
  lookup : Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → Option Node
  count : Node → ℕ
  pointer : Node → ℕ → Pointer

private def HeaderRows.read {ports : DatePorts} (r : HeaderRows ports) {w : ℕ} (m : Memory w)
    (x : Fin (2^ports.venue.k)) (j : Fin ports.argumentsPerNode) (f : Fin 4) : Prop :=
  let face := f.castLE (by decide : 4 ≤ 7)
  ∃ cells : Fin ports.operandHosts → Fin ports.venue.groups → Cell (ports.operandBits * ports.nodes),
    Reads (previousBank ports.rangeLayout ports.archive.arguments x (page face j)) cells ports.operandLanes m ∧
    ∀ (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) (n : Fin ports.nodes) (y : r.Node),
      r.lookup x n h g = some y → j.val < r.count y →
      (((encode ports.operandBits ports.nodes).symm (cells h g)) n).val = (r.pointer y j.val).header f

open private SeedNamed.Origin.rawArgumentClaim
  from OAI.Hierarchy.DescentSeedRenamedPointers in
private theorem raw_header_of_claim {F : Type} [Field F] {cp pins copies grain width : ℕ}
    (X : Approximation F cp pins) (c : (initialGroup X copies grain).Choice)
    (raw : NodeOrder.All (BitDescription.initial X copies grain c))
    (read : ℕ → Pointer)
    (known : SeedNamed.Origin.rawArgumentClaim (copies := copies) (grain := grain) (width := width) X c raw read)
    (arg : Fin ((initialRecipe X copies grain c raw.1).arity raw.2)) (chunk : Fin (grain / width))
    (j : ℕ) (atIndex : (finProdFinEquiv (arg, chunk)).val = j) (f : Fin 4) :
    (read j).header f =
      (Seed.originalAt X raw.1.2
        (leg X raw.1.2 (Fin.cast (recipe_arity X c raw.1.1 raw.1.2 raw.2) arg))
        raw.1.1.val chunk.val).header f := by
  subst j
  exact congrArg (fun ptr : Pointer => ptr.header f) (known arg chunk)

private theorem value_at_slot {B H G : Type*}
    (read : ℕ → B → H → G → ℕ) {i j : ℕ} {x x' : B} {h h' : H} {g g' : G} {t : ℕ}
    (index : i = j) (ex : x = x') (eh : h = h') (eg : g = g')
    (physical : read i x' h' g' = t) : read j x h g = t := by
  cases index
  cases ex
  cases eh
  cases eg
  exact physical


section RawSeedArithmetic
variable {F : Type} [Field F] {S : AtomSchedule} {k cp pins H s a : ℕ}
    (X : Approximation F cp pins) (digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k)
    (wide : Fintype.card (Vertex X) ≤ H) (l : DescentDatedSeedStartup.Layout)
    (choice : (initialGroup X S.copies s).Choice)
local notation "seedSeat" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb wide)

open private SeedNamed.Origin.rawArgumentClaim
  from OAI.Hierarchy.DescentSeedRenamedPointers in
private theorem rawSeedHeader
    (room : 3 < 2^l.operandBits) (copies : S.copies ≤ 2^l.operandBits)
    (quota : l.groupsPerNode ≤ 2^l.operandBits) (pieces : l.groupsPerNode = s/a)
    (raw : NodeOrder.All (BitDescription.initial X S.copies s choice)) (readPointer : ℕ → Pointer)
    (known : SeedNamed.Origin.rawArgumentClaim (copies := S.copies) (grain := s) (width := a)
      X choice raw readPointer)
    (x : Block k) (h : Fin H) (g : Fin (S.groupCount 0)) (n : Fin 1) (j : ℕ) (f : Fin 4)
    (located : x = (digits raw.1.1).2 ∧ h = seedSeat raw.1.2 ∧ g = (digits raw.1.1).1)
    (count : ℕ) (counted : count = legArity X raw.1.2 * (s/a)) (valid : j < count) :
    (((encode l.operandBits 1).symm
      (Seed.Physical.value X seedSeat (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 j
        (f.castLE (by decide : 4 ≤ 7)) x h g)) n).val = (readPointer j).header f := by
  rcases raw with ⟨⟨copy, vertex⟩, node⟩
  obtain ⟨xEq, hEq, gEq⟩ := located
  let ar := (initialRecipe X S.copies s choice ⟨copy, vertex⟩).arity node
  have bound : j < ar * (s / a) := by
    change j < (initialRecipe X S.copies s choice ⟨copy, vertex⟩).arity node * (s / a)
    rw [recipe_arity X choice copy vertex node]
    exact Eq.subst (motive := fun t : ℕ => j < t) counted valid
  let offset : Fin (ar * (s / a)) := ⟨j, bound⟩
  let loc : Fin ar × Fin (s / a) := finProdFinEquiv.symm offset
  have ix : (finProdFinEquiv loc).val = j :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply offset)
  let entry := Fin.castLE (DescentBundleHistory.initial_arity X S.copies s choice ⟨copy, vertex⟩ node) loc.1
  let col := finProdFinEquiv (entry, loc.2.cast pieces.symm)
  have same : col.val = j := by
    calc
      col.val = (finProdFinEquiv loc).val := by
        change loc.2.val + l.groupsPerNode * loc.1.val = loc.2.val + (s / a) * loc.1.val
        exact congrArg (fun t : ℕ => loc.2.val + t * loc.1.val) pieces
      _ = j := ix
  let decoded := fun (i : ℕ) (b : Block k) (host : Fin H) (group : Fin (S.groupCount 0)) =>
    (((encode l.operandBits 1).symm
      (Seed.Physical.value X seedSeat (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 i
        (f.castLE (by decide : 4 ≤ 7)) b host group)) n).val
  have digit := seed_pointer_digit X digits wide l choice room copies quota copy vertex node
    loc.1 (loc.2.cast pieces.symm) f n
  have atPointer := raw_header_of_claim (width := a) X choice ⟨⟨copy,vertex⟩,node⟩
    readPointer known loc.1 loc.2 j ix f
  exact (value_at_slot decoded same xEq hEq gEq digit).trans atPointer.symm

end RawSeedArithmetic

private abbrev HeaderValues (ports : DatePorts) :=
  Fin (2 ^ ports.venue.k) → Fin ports.argumentsPerNode → Fin 4 →
    Fin ports.operandHosts → Fin ports.venue.groups → Cell (ports.operandBits * ports.nodes)

private structure HeaderProgram (ports : DatePorts) (O : Type) (Fit Can : Prop) (values : HeaderValues ports) where
  rows : O → Fit → HeaderRows ports
  read : ∀ (nr : O) (ok : Fit), Can → ∀ {w : ℕ} (m : Memory w) (x : Fin (2 ^ ports.venue.k))
    (j : Fin ports.argumentsPerNode) (f : Fin 4),
    Reads (previousBank ports.rangeLayout ports.archive.arguments x (page (f.castLE (by decide : 4 ≤ 7)) j))
      (values x j f) ports.operandLanes m → HeaderRows.read (rows nr ok) m x j f

open private originalGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private SeedNamed.Origin.seedKeysDescribe from OAI.Hierarchy.DescentSeedRenamedPointers
open private SeedNamed.Origin.seedReadsAt from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
open private SeedNamed.Origin.rawSeedCounted from OAI.Hierarchy.DescentDatedSeedOriginalNode

section PhysicalHeader
open SeedNamed
open private namedArchiveGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  OrderedSlotGeometry.facts SlotGeometry.coordinates SlotFact.checked
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
open private carriedCoordinates Coordinates.nodes
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
open private transferredArity ArityFact.checked
  from OAI.Hierarchy.DescentDatedSeedOriginalNode
open private SeedNamed.FromPublicKeys SeedNamed.physicalPointerClaims
  SeedNamed.PointerClaim.checked SeedNamed.OrderedPointerClaims.atOrder SeedNamed.Origin.rawArgumentClaim
  from OAI.Hierarchy.DescentSeedRenamedPointers

variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q fee : ℝ} {S : AtomSchedule} {k z wire s cp pins H : ℕ}
    (X : Approximation F cp pins) (digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k)
    (publicWide : Fintype.card (Vertex X) ≤ H) (op : RotorSpec) (l : DescentDatedSeedStartup.Layout)
    (payload Z : ℕ) {choice : (initialGroup X S.copies s).Choice}
    (r : Reached W G q fee S k 0 z 3 wire s) (ar : Archive W) (eqn : world r = W')
    (oldSites : NodeOrder.All ar.bit ≃ Fin S.copies × Vertex X)
    (seen : ∀ t : NodeOrder.All ar.bit,
      (r.vertex (r.placement.pos t.1).2).val = (Fintype.equivFin (Vertex X) (oldSites t).2).val ∧
      (r.placement.pos t.1).1 = (digits (oldSites t).1).1 ∧
      r.placement.block t.1 = (digits (oldSites t).1).2)
    (oneNode : ∀ v : W.graph.Site, Fintype.card (ar.bit.recipe v).Node = 1)
local notation "p₀" => initial G op X S.copies l k H (S.groupCount 0) payload Z
local notation "seat₀" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "geometry₀" => namedArchiveGeometry X digits publicWide op l payload Z r ar eqn oldSites seen oneNode

local notation "can₀" width => (3 < 2^l.operandBits ∧ S.copies ≤ 2^l.operandBits ∧
  l.groupsPerNode ≤ 2^l.operandBits ∧ l.groupsPerNode = s/width)
local notation "values₀" => (fun (x : Block k) (j : Fin (p₀).argumentsPerNode) (f : Fin 4) =>
  Seed.Physical.value X seat₀ (Equiv.refl _) digits l.groupsPerNode l.operandBits 1
    j.val (f.castLE (by decide : 4 ≤ 7)) x)

set_option maxHeartbeats 1600000 in
private def physicalHeaderProgram {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
    (inputPin : P → ℕ)
    (oldRaw : NodeOrder.All ar.bit → NodeOrder.All (BitDescription.initial X S.copies s choice))
    (sameSite : ∀ t, oldSites t = ((oldRaw t).1.1, (oldRaw t).1.2))
    (counted : ∀ t : NodeOrder.All ar.bit, ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldRaw t).1.2 * (s/a))
    (pointers : SeedNamed.FromPublicKeys r ar hp inputPin sh
      (fun t => SeedNamed.Origin.rawArgumentClaim (copies := S.copies) (grain := s) (width := a) X choice (oldRaw t))) :
    HeaderProgram p₀ (OrderedSlotGeometry.ordering (geometry₀))
      (OrderedSlotGeometry.room (geometry₀)) (can₀ a) values₀ := by
  let pkg := transportArchive (renamedArchive ar (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r ar eqn pkg)
  let current := SeedNamed.transport r eqn
  let installed : WorldShape a R pkg.data.bit :=
    pkg.carry (fun _ b => WorldShape a R b.bit) (sh.renamed (site r) (edge r))
  let countAt (y : NodeOrder.All pkg.data.bit) := (occurrences (installed.sites y.1) y.2).length
  let makeRows (nr : OrderedSlotGeometry.ordering (geometry₀))
      (ok : OrderedSlotGeometry.room (geometry₀)) : HeaderRows p₀ := {
    Node := NodeOrder.All pkg.data.bit
    lookup := slotAt p₀ current pkg.data.bit nr ok
    count := countAt
    pointer := Reached.argumentPointer current pkg.data.bit nr installed hp inputPin (p₀).argumentsPerNode }
  refine ⟨makeRows, ?_⟩
  intro nr ok limits w mem x j f paid
  obtain ⟨room, copies, quota, pieces⟩ := limits
  refine ⟨values₀ x j f, paid, ?_⟩
  intro h g n y hit valid
  let t := names y
  have atSites := SlotFact.checked (SlotGeometry.coordinates (OrderedSlotGeometry.facts (geometry₀) nr ok))
  have atOld : x = (digits (oldSites t).1).2 ∧ h = seat₀ (oldSites t).2 ∧ g = (digits (oldSites t).1).1 :=
    atSites x n h g y hit
  have atRaw := Eq.subst (motive := fun u : Fin S.copies × Vertex X =>
    x = (digits u.1).2 ∧ h = seat₀ u.2 ∧ g = (digits u.1).1) (sameSite t) atOld
  have sizes := ArityFact.checked (transferredArity r ar eqn hp sh
    (fun u => legArity X (oldRaw u).1.2 * (s/a)) counted)
  have actual := SeedNamed.PointerClaim.checked (SeedNamed.OrderedPointerClaims.atOrder
    (SeedNamed.physicalPointerClaims r ar eqn hp inputPin sh
      (fun u => SeedNamed.Origin.rawArgumentClaim (copies := S.copies) (grain := s) (width := a) X choice (oldRaw u)) pointers)
    nr (p₀).argumentsPerNode)
  exact rawSeedHeader X digits publicWide l choice room copies quota pieces (oldRaw t)
    (Reached.argumentPointer current pkg.data.bit nr installed hp inputPin (p₀).argumentsPerNode y)
    (actual y) x h g n j.val f atRaw (countAt y) (sizes y) valid

end PhysicalHeader
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z
local notation "ob" => operandBase X l H g₀
local notation "db" => directoryBase X l H g₀ k
local notation "argBase" => Seed.Physical.bankStart X ob k g₀ l.operandLanes
local notation "L" => (ports).rangeLayout

variable {q ε : ℝ} {s wire z : ℕ} {choice : (initialGroup X S.copies s).Choice}
    (o : SeedNamed.Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) choice digits)
    (ord : OrderedSlotGeometry.ordering (originalGeometry X digits publicWide op l payload Z o))
    (ready : OrderedSlotGeometry.room (originalGeometry X digits publicWide op l payload Z o))
    {a R : ℕ} (hp : 0<a) (units : 1≤R) (whole : a∣s)
local notation "pin" => (fun y : (Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width)))=>y.1.val)

set_option maxHeartbeats 800000 in
private def concreteHeaderProgram :=
  physicalHeaderProgram (choice := choice) (G := G) X digits publicWide op l payload Z o.raw
    (seedArchive X S.copies s choice) (linked_world X choice digits o.seed)
    (NodeOrder.seedSites X S.copies s choice) (fun y => SeedNamed.Origin.seedReadsAt o y.1)
    (initial_nodes X S.copies s choice) hp (seedRetained X S.copies s hp units whole choice).shape
    pin id (fun _ => rfl) (SeedNamed.Origin.rawSeedCounted X choice hp units whole)
    (SeedNamed.Origin.seedKeysDescribe o hp units whole)

local notation "program₀" => concreteHeaderProgram G op X digits publicWide l payload Z o hp units whole

set_option maxHeartbeats 1600000 in
/-- Every occupied original index is decoded from the same seven-page seed tensor.
Each live leg retains its natural cable number or original copy ordinal. -/
theorem seed_argument_headers {w : ℕ} (m : Memory w) (fields : l.operandBits*l.operandLanes≤w)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w)
    (room : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits) (quota : l.groupsPerNode≤2^l.operandBits)
    (pieces : l.groupsPerNode=s/a) (x : Block k) (j : Fin (ports).argumentsPerNode) (f : Fin 4) :
    HeaderRows.read (HeaderProgram.rows (program₀) ord ready) ((final) m) x j f := by
  exact HeaderProgram.read (program₀) ord ready ⟨room,copies,quota,pieces⟩ ((final) m) x j f
    (seed_operand_cells G op X digits publicWide l header payload Z m fields early sourceSpace
      live machine space (f.castLE (by decide : 4 ≤ 7)) j x)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
