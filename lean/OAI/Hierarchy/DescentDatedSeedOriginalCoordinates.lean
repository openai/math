import OAI.Hierarchy.DescentNamedOriginalArchive
import OAI.Hierarchy.DescentSeedNodeOrder
import OAI.Hierarchy.DescentBundleSeed

namespace OAI
/-! # Original sites, nodes and their physical coordinates at date zero -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentKernelHistory DescentBundleHistory DescentColonies
open DescentSeedRoot DescentPackedSeed Chronology Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {q fee : ℝ} {S : AtomSchedule} {k s z wire : ℕ}
section Transport
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 z 3 wire s) (a : Archive W) (eqn : world r=W')
local notation "named" => Eq.ndrec (motive := fun V => Archive V) (renamedArchive a (site r) (edge r)) eqn
local notation "cap" => transport r eqn

/-- Inverting the original static site permutation leaves the scalar node in its original recipe. -/
def acrossNodes : NodeOrder.All (named).bit ≃ NodeOrder.All a.bit :=by
  cases eqn
  exact NodeOrder.renamedNames a.bit (site r) (edge r)

private theorem across_coordinates (y : NodeOrder.All (named).bit) :
    let raw:=acrossNodes r a eqn y
    ((cap).vertex ((cap).placement.pos y.1).2).val=(r.vertex (r.placement.pos raw.1).2).val ∧
      ((cap).placement.pos y.1).1=(r.placement.pos raw.1).1 ∧ (cap).placement.block y.1=r.placement.block raw.1 :=by
  cases eqn
  exact ⟨rfl,rfl,rfl⟩

private theorem across_card (one : ∀v,Fintype.card (a.bit.recipe v).Node=1) (v : W'.graph.Site) :
    Fintype.card ((named).bit.recipe v).Node=1 :=by
  cases eqn
  exact one ((site r).symm v)

private structure Coordinates (b : Archive W') (target : Reached W' G q fee S k 0 z 3 wire s) where
  nodes : NodeOrder.All b.bit ≃ NodeOrder.All a.bit
  read (y : NodeOrder.All b.bit) :
    let raw := nodes y
    (target.vertex (target.placement.pos y.1).2).val = (r.vertex (r.placement.pos raw.1).2).val ∧
      (target.placement.pos y.1).1 = (r.placement.pos raw.1).1 ∧
        target.placement.block y.1 = r.placement.block raw.1
  single (one : ∀ v, Fintype.card (a.bit.recipe v).Node = 1) (v : W'.graph.Site) :
    Fintype.card (b.bit.recipe v).Node = 1

private def physicalAt {U : MarkedWorld F d P bits}
    (target : Reached U G q fee S k 0 z 3 wire s) (v : U.graph.Site) :
    ℕ × (Fin (S.groupCount 0) × Block k) :=
  ((target.vertex (target.placement.pos v).2).val,
    (target.placement.pos v).1, target.placement.block v)

private def siteOfNode {U : MarkedWorld F d P bits} (b : Archive U)
    (y : NodeOrder.All b.bit) : U.graph.Site :=
  y.1

private abbrev ReadsAs {A B : Type} (u v : ℕ × (A × B)) : Prop :=
  u.1 = v.1 ∧ u.2.1 = v.2.1 ∧ u.2.2 = v.2.2

private theorem readsAs_trans {A B : Type} {u v t : ℕ × (A × B)}
    (one : ReadsAs u v) (two : ReadsAs v t) : ReadsAs u t :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.trans two.2.2⟩

private theorem coordinatesReadAt (b : Archive W') (target : Reached W' G q fee S k 0 z 3 wire s)
    (coords : Coordinates r a b target) (y : NodeOrder.All b.bit) :
    ReadsAs (physicalAt target (siteOfNode b y))
      (physicalAt r (siteOfNode a (coords.nodes y))) :=
  coords.read y

private structure ArchiveFact where
  statement : Prop
  checked : statement

private def coordinateReport {previous : Reached W G q fee S k 0 z 3 wire s}
    {oldBook : Archive W} {newBook : Archive W'}
    {current : Reached W' G q fee S k 0 z 3 wire s}
    (coords : Coordinates previous oldBook newBook current)
    (names : NodeOrder.All newBook.bit ≃ NodeOrder.All oldBook.bit)
    (agree : names = coords.nodes)
    (initial : W.graph.Site → ℕ × (Fin (S.groupCount 0) × Block k))
    (observed : ∀ v, ReadsAs (physicalAt previous v) (initial v)) : ArchiveFact where
  statement := ∀ y : NodeOrder.All newBook.bit,
    ReadsAs (physicalAt current (siteOfNode newBook y)) (initial (siteOfNode oldBook (names y)))
  checked := by
    subst names
    intro y
    exact readsAs_trans (coordinatesReadAt previous oldBook newBook current coords y)
      (observed (siteOfNode oldBook (coords.nodes y)))

private def carriedCoordinates
    (pkg : ArchiveTransport (renamedArchive a (site r) (edge r)) W') :
    Coordinates r a pkg.data (transport r eqn) :=
  pkg.carry (fun U b => (e : world r = U) → Coordinates r a b (transport r e))
    (fun e => by
      have loop : e = rfl := Subsingleton.elim _ _
      rw [loop]
      exact ⟨acrossNodes r a rfl, across_coordinates r a rfl, across_card r a rfl⟩) eqn

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
private theorem carriedNodes_eq :
    (carriedCoordinates r a eqn (transportArchive (renamedArchive a (site r) (edge r)) eqn)).nodes =
      acrossNodes r a eqn := by
  cases eqn
  rfl

/-- The physical inverse, its original renaming, and the observable coordinates
of a node. Their domains can be selected without evaluating either equivalence. -/
private structure CoordinateData where
  domain : Type
  codomain : Type
  nodes : domain ≃ codomain
  reference : domain ≃ codomain
  agreement : nodes = reference
  readAs : (domain ≃ codomain) → Prop
  observed : readAs nodes

private def CoordinateData.agreementFact (data : CoordinateData) : ArchiveFact :=
  ⟨data.nodes = data.reference, data.agreement⟩

private def CoordinateData.readFact (data : CoordinateData) : ArchiveFact :=
  ⟨data.readAs data.nodes, data.observed⟩

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
private def coordinateData
    (initial : W.graph.Site → ℕ × (Fin (S.groupCount 0) × Block k))
    (seen : ∀ v, ReadsAs (physicalAt r v) (initial v)) : CoordinateData := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let coords := carriedCoordinates r a eqn pkg
  exact {
    domain := NodeOrder.All pkg.data.bit
    codomain := NodeOrder.All a.bit
    nodes := coords.nodes
    reference := acrossNodes r a eqn
    agreement := carriedNodes_eq r a eqn
    readAs := fun names => ∀ y : NodeOrder.All pkg.data.bit,
      ReadsAs (physicalAt (transport r eqn) (siteOfNode pkg.data y))
        (initial (siteOfNode a (names y)))
    observed := (coordinateReport coords coords.nodes rfl initial seen).checked
  }

private abbrev oneNodeEach {U : MarkedWorld F d P bits} (a : Archive U) : Prop :=
  ∀ v : U.graph.Site, Fintype.card (a.bit.recipe v).Node = 1

private def singletonAfterRenaming {U V : MarkedWorld F d P bits}
    (a : Archive U) (v : Equiv.Perm U.graph.Site) (e : Equiv.Perm U.graph.Edge)
    (pkg : ArchiveTransport (renamedArchive a v e) V) (one : oneNodeEach a) : ArchiveFact where
  statement := oneNodeEach pkg.data
  checked := by
    have renamed : oneNodeEach (renamedArchive a v e) := fun u => one (v.symm u)
    exact (pkg.carry (fun _ b => PLift (oneNodeEach b)) ⟨renamed⟩).down

end Transport

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
local notation "arch" => seedArchive X S.copies s c

private def seedAt {n b copies grain : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice) (names : Fin copies ≃ Fin n × Block b)
    (u : ((initialGroup X copies grain).state c).graph.Site) : ℕ × (Fin n × Block b) :=
  ((Fintype.equivFin (Vertex X) u.2).val, (names u.1).1, (names u.1).2)

private theorem seedReadsAt (v : ((initialGroup X S.copies s).state c).graph.Site) :
    ReadsAs (physicalAt o.raw v) (seedAt (grain:=s) X c digits v) := by
  have read := o.seed.coordinates_read v
  exact ⟨read.2, read.1, congrFun o.seed.blocks v⟩

set_option maxHeartbeats 400000 in
private def originData : CoordinateData :=
  coordinateData o.raw arch (linked_world X c digits o.seed)
    (seedAt (grain:=s) X c digits) (seedReadsAt o)

/-- The inverse node equiv read from the original seed's physical sites. -/
abbrev originalNode := (originData o).nodes

/-- The stored inverse agrees with the renaming of the original seed nodes. -/
theorem originalNode_eq_acrossNodes : (CoordinateData.agreementFact (originData o)).statement :=
  (CoordinateData.agreementFact (originData o)).checked

theorem original_coordinates : (CoordinateData.readFact (originData o)).statement :=
  (CoordinateData.readFact (originData o)).checked

private theorem seedOneNodeEach {cp pins : ℕ} (X : Approximation F cp pins)
    (R s : ℕ) (c : (initialGroup X R s).Choice) :
    oneNodeEach (seedArchive X R s c) :=
  initial_nodes X R s c

include o in
private def singletonEvidence : ArchiveFact :=
  singletonAfterRenaming (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
    o.archivePackage (seedOneNodeEach X S.copies s c)

theorem original_single : (singletonEvidence o).statement :=
  (singletonEvidence o).checked

end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
