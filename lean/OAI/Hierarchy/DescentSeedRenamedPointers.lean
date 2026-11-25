import OAI.Hierarchy.DescentSeedRawPointer
import OAI.Hierarchy.DescentNamedSeedInitialShape
import OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
import OAI.Hierarchy.DescentSeedNamedFirstCable

namespace OAI
/-! # Four pointer fields survive the physical relabelling of the original seed -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentOperandStateBanks
open DescentCompiler DescentColonies DescentInitialHost DescentSeedRoot DescentPackedSeed Chronology
open Computability.BorderVNP.Crossing ThreeFlat.Routing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k s z wire p R : ℕ}

private theorem seed_lookup_map_some {α β : Type*} (g : α → β) (xs : List α)
    (j : ℕ) (a : α) (h : xs[j]? = some a) :
    (xs.map g)[j]? = some (g a) := by
  rw [List.getElem?_map, h]; rfl

private theorem reroute_public_at {Tag A B : Type} {w : A → ℕ} {w' : B → ℕ}
    {p : ℕ} {recipe : BitRecipe Tag A w} (sh : Shape p recipe) {route : BitRef w → BitRef w'}
    (f : BlockMap p w w' route) (u : recipe.Node) (j : ℕ) (ref : BlockRef p w)
    (read : (sh.keys u)[j]? = some (.inl ref)) :
    ((sh.reroute f).keys u)[j]? = some (.inl (f.map ref)) := by
  let lookup := fun xs : List (BlockRef p w' ⊕ BlockRef p recipe.hiddenWidth) => xs[j]?
  exact (congrArg lookup (reroute_keys sh f u)).trans
    (seed_lookup_map_some (Sum.map f.map id) (sh.keys u) j (.inl ref) read)

section Map
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W) (eqn : world r=W')
local notation "after" => Eq.ndrec (motive := fun V => Archive V) (renamedArchive a (site r) (edge r)) eqn
local notation "current" => transport r eqn
local notation "name" v => namedMap W (site r) (edge r) v

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
private theorem carried_shape (shape : WorldShape p R a.bit) :
    (transportArchive (renamedArchive a (site r) (edge r)) eqn).carry
      (fun _ b => WorldShape p R b.bit) (shape.renamed (site r) (edge r)) =
      transport_shape r a eqn shape := by
  cases eqn
  rfl

private theorem public_names (hp : 0<p) (pin : P→ℕ) (v : (world r).graph.Site)
    (ref : BlockRef p (boundaryWidth W.graph ((site r).symm v))) :
    Reached.publicPointer (reached r) hp pin v ((name v).map ref)=
      Reached.publicPointer r hp pin ((site r).symm v) ref :=by
  rcases ref with ⟨e|ext,t,fit⟩
  · let oldRef : BlockRef p (boundaryWidth W.graph ((site r).symm v)) := ⟨.inl e, t, fit⟩
    exact Signed.firstCable_incident r hp v e t ((name v).map oldRef).fits fit
  · rfl

theorem transported_public (hp : 0<p) (pin : P→ℕ) (shape : WorldShape p R a.bit)
    (order : Local (after).bit) (slots : ℕ) (y : NodeOrder.All (after).bit) (j : ℕ)
    (ref : BlockRef p (boundaryWidth W.graph (acrossNodes r a eqn y).1))
    (read : ((shape.sites (acrossNodes r a eqn y).1).keys (acrossNodes r a eqn y).2)[j]?=some (.inl ref)) :
    Reached.argumentPointer current (after).bit order (transport_shape r a eqn shape) hp pin slots y j=
      Reached.publicPointer r hp pin (acrossNodes r a eqn y).1 ref :=by
  cases eqn
  have key : (((shape.renamed (site r) (edge r)).sites y.1).keys y.2)[j]?=
      some (.inl ((name y.1).map ref)):=by
    change (((shape.sites ((site r).symm y.1)).reroute (name y.1)).keys y.2)[j]?=_
    exact reroute_public_at (shape.sites ((site r).symm y.1)) (name y.1) y.2 j ref read
  exact (Reached.argument_public (reached r) hp pin _ order _ slots y.1 y.2 j _ key).trans
    (public_names r hp pin y.1 ref)

private theorem transported_public_at (hp : 0<p) (pin : P→ℕ) (shape : WorldShape p R a.bit)
    (order : Local (after).bit) (slots : ℕ) (y : NodeOrder.All (after).bit) (j : ℕ)
    (raw : NodeOrder.All a.bit) (identified : raw = acrossNodes r a eqn y) :
    ∀ (ref : BlockRef p (boundaryWidth W.graph raw.1)),
      ((shape.sites raw.1).keys raw.2)[j]? = some (.inl ref) →
      Reached.argumentPointer current (after).bit order (transport_shape r a eqn shape) hp pin slots y j =
        Reached.publicPointer r hp pin raw.1 ref := by
  subst raw
  exact transported_public r a eqn hp pin shape order slots y j

private structure PointerClaim where
  statement : Prop
  checked : statement

private structure OrderedPointerClaims where
  ordering : Type
  atOrder : ordering → ℕ → PointerClaim

private abbrev FromPublicKeys (hp : 0 < p) (pin : P → ℕ) (sh : WorldShape p R a.bit)
    (claim : NodeOrder.All a.bit → (ℕ → Pointer) → Prop) : Prop :=
  ∀ (raw : NodeOrder.All a.bit) (read : ℕ → Pointer),
    (∀ (j : ℕ) (ref : BlockRef p (boundaryWidth W.graph raw.1)),
      ((sh.sites raw.1).keys raw.2)[j]? = some (.inl ref) →
      read j = Reached.publicPointer r hp pin raw.1 ref) → claim raw read

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
open private carriedCoordinates carriedNodes_eq Coordinates.nodes
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
private def physicalPointerClaims (hp : 0 < p) (pin : P → ℕ) (sh : WorldShape p R a.bit)
    (claim : NodeOrder.All a.bit → (ℕ → Pointer) → Prop)
    (earn : FromPublicKeys r a hp pin sh claim) : OrderedPointerClaims := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  let installed : WorldShape p R (after).bit := pkg.carry (fun _ b => WorldShape p R b.bit)
    (sh.renamed (site r) (edge r))
  refine ⟨Local (after).bit, fun order slots => ⟨
    (∀ y : NodeOrder.All (after).bit, claim (names y)
      (Reached.argumentPointer current (after).bit order installed hp pin slots y)), ?_⟩⟩
  intro y
  apply earn (names y) _
  intro j ref key
  have measured := transported_public_at r a eqn hp pin sh order slots y j (names y)
    (DFunLike.congr_fun (carriedNodes_eq r a eqn) y) ref key
  exact (congrArg (fun b : WorldShape p R (after).bit =>
    Reached.argumentPointer current (after).bit order b hp pin slots y j)
    (carried_shape r a eqn sh)).trans measured

end Map

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
    (hp : 0<p) (one : 1≤R) (whole : p∣s)
set_option quotPrecheck false in
local notation "pin" => (fun z : (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) => z.1.val)

private def rawArgumentClaim {copies grain width : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice)
    (raw : NodeOrder.All (BitDescription.initial X copies grain c)) (read : ℕ → Pointer) : Prop :=
  ∀ (arg : Fin ((initialRecipe X copies grain c raw.1).arity raw.2)) (chunk : Fin (grain/width)),
    read (finProdFinEquiv (arg,chunk)).val =
      Seed.originalAt X raw.1.2 (leg X raw.1.2 (Fin.cast (recipe_arity X c raw.1.1 raw.1.2 raw.2) arg))
        raw.1.1.val chunk.val

private theorem seedKeysDescribe :
    FromPublicKeys o.raw (Chronology.seedArchive X S.copies s c) hp pin
      (seedRetained X S.copies s hp one whole c).shape
      (rawArgumentClaim (copies := S.copies) (grain := s) (width := p) X c) := by
  rintro ⟨⟨j, v⟩, node⟩ read publicAt arg chunk
  exact (publicAt (finProdFinEquiv (arg,chunk)).val
    (flatSeedRef X c hp j v node arg chunk)
    (seed_key_at X c hp whole j v node arg chunk)).trans
    (original_public X o hp j v node arg chunk)

set_option maxHeartbeats 400000 in
private def seedPointerClaims : OrderedPointerClaims :=
  physicalPointerClaims o.raw (Chronology.seedArchive X S.copies s c)
    (linked_world X c digits o.seed) hp pin (seedRetained X S.copies s hp one whole c).shape
    (rawArgumentClaim (copies := S.copies) (grain := s) (width := p) X c)
    (seedKeysDescribe o hp one whole)

theorem named_argument (order : (seedPointerClaims o hp one whole).ordering) (slots : ℕ) :
    ((seedPointerClaims o hp one whole).atOrder order slots).statement :=
  ((seedPointerClaims o hp one whole).atOrder order slots).checked

end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
