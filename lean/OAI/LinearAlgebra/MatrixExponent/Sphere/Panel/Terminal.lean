import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Pattern
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Window
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
import OAI.LinearAlgebra.MatrixExponent.Sphere.Concentration.Kits
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Wiring

/-!
# Carrying the two exterior lists to a frozen collector

Concentration moves the exterior of each input station as two
ordered lists, within the same block of a child of the old host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring Packing
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {G H : Diagram F x y}
  {S U : Scheme F} {r : S.format.obj} {t : U.format.obj}
  (p : S.Presentation r G) (q : U.Presentation t H) {z : ℕ}
  (child : B U.m ≃ B S.m × B z) (outer : Bool ↪ B U.e)

structure Carrier (v : G.V) (w : H.V) : Prop where
  parent : (child (q.vertex w).1).1 = (p.vertex v).1
  block : (q.vertex w).2.1.val = (p.vertex v).2.1.val
  seat : (q.vertex w).2.2 = 0
  left : ∀ j : Fin (G.extLeft v).length, let a := (q.boundary (.inl ((G.extLeft v).get j))).val
    a.1 = (q.vertex w, outer false) ∧ a.2.val = j.val
  right : ∀ j : Fin (G.extRight v).length, let a := (q.boundary (.inr ((G.extRight v).get j))).val
    a.1 = (q.vertex w, outer true) ∧ a.2.val = j.val

def Retains := ∀ i : slots x ⊕ slots y, ∃ w, Carrier p q child outer (portEnd G i) w

theorem owner (i : slots x ⊕ slots y) : (p.boundary i).val.1.1 = p.vertex (portEnd G i) := by
  cases i <;> exact p.end_station _

variable {p q child outer} {v : G.V} {w : H.V}

theorem Carrier.owns (c : Carrier p q child outer v w) (i : slots x ⊕ slots y) (h : portEnd G i = v) :
    (q.boundary i).val.1 = (q.vertex w, outer i.isRight) := by
  cases i with
  | inl i =>
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ((G.mem_extLeft v i).mpr h)
    exact (c.left _).1
  | inr i =>
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ((G.mem_extRight v i).mpr h)
    exact (c.right _).1

namespace Retains
variable (f : Retains p q child outer)
include f

theorem parent (i : slots x ⊕ slots y) :
    (child (q.boundary i).val.1.1.1).1 = (p.boundary i).val.1.1.1 := by
  obtain ⟨w, c⟩ := f i
  rw [c.owns i rfl, owner]
  exact c.parent

theorem load_le (i : B U.m) : U.load t i ≤ S.load r (child i).1 := by
  let e := q.boundary.symm.trans p.boundary
  have he (j : U.exposed t) : S.owner r (e j) = (child (U.owner t j)).1 := by
    obtain ⟨s, rfl⟩ := q.boundary.surjective j
    rw [show e (q.boundary s) = p.boundary s by simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]]
    exact (f.parent s).symm
  let g (x : U.fiber t i) : S.fiber r (child i).1 := ⟨e x.val, by rw [he, x.property]⟩
  exact Fintype.card_le_of_injective g fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))

theorem fits {k V : ℕ} (h : S.Fits r V k) : U.Fits t (2 ^ U.m + wd x + wd y) k :=
  q.fits le_rfl (fun i => (f.load_le i).trans (h.2 _))

end Retains
end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-! # The initial tile as a function of the occupied cell's ordered ports -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Surface Surface.Local Routing.Private SphereScale
open scoped Classical
variable {F K A B : Type} [Field F] [Field K] [Algebra K F]
  {x y : Wire} {q h ℓ D T b d g m : ℕ} {W : ℝ}

def seamName (color : ℕ → Fin q) (k : ℕ) := (color k.unpair.1, color k.unpair.2)

namespace Seed

private def drawRow (s : Seed F) (names : ℕ → A) (n i : ℕ) (pos : F) (e : ℕ) :
    Entry F (d * b) d B A :=
  let row := s.rows.getD i (0, ⟨⟨.unit, .unit, fun _ _ => 0⟩, false, []⟩)
  ⟨pos, e, 0, if row.2.mobile then .active 0 else .collector,
    if row.2.mobile then none else some (names row.1), [],
    row.2.label (d * b) d n (Nat.pair s.color row.1)⟩

private def draw (s : Seed F) (p : Pattern K D g (probes ℓ D)) (hK : Ready K ℓ D g m b d)
    (name : ℕ → A) (color : ℕ → Fin q) (stamp : B) (shape : Shape (probes ℓ D) b d) :
    Tile F (d * b) d q B A :=
  let u := p.template F (d * b)
  let w := p.patch (F := F) hK
  let head : Entry F (d * b) d B A :=
    ⟨w.pos (.inr none), 0, 0, .collector, none, [stamp], auxLabel w.program shape none⟩
  let aux : Fin (probes ℓ D) → Entry F (d * b) d B A := fun j =>
    ⟨w.pos (.inr (some j)), (shape.1 j).val, (shape.2 j).val, .residue, none, [stamp], auxLabel w.program shape (some j)⟩
  let rows := List.ofFn fun i : Fin u.stations =>
    s.drawRow name (probes ℓ D) i.val (w.pos (.inl (u.old i))) (u.level (u.old i))
  let ports := List.ofFn fun i : Fin u.ports =>
    (seamName color ((s.ordered (d * b)).getD i.val 0), w.pos (.inl (u.edge i)), u.level (u.edge i))
  ⟨⟨head :: (List.ofFn aux ++ rows), ports, {stamp}⟩, {(stamp, .inl w.program.labels)}⟩

/-- Every quantity used to construct the tile is local. The default
on malformed data is irrelevant to the contraction. -/
def tile (s : Seed F) (hK : Ready K ℓ D g m b d)
    (name : ℕ → A) (color : ℕ → Fin q) (stamp : B) (shape : Shape (probes ℓ D) b d) :
    Tile F (d * b) d q B A :=
  if h : ∃ p : Pattern K D g (probes ℓ D), s.Identifies (d * b) p then
    s.draw h.choose hK name color stamp shape
  else ⟨⟨[], [], ∅⟩, ∅⟩

end Seed

variable (P : Input F x y h D T (d * b) g W) (sc : Scales g ℓ D T m b d) (hK : Ready K ℓ D g m b d)
  (H : P.LocalRanks) (name : ℕ → A) (color : ℕ → Fin q) (stamp : P.Occupied → B)
  (shape : P.Occupied → Shape (probes ℓ D) b d) (c : P.Occupied)
include H

private theorem row_eq (i : Fin (P.grid.stations c).card) :
    let p := P.kit sc hK
    let a := Template.originalAt p P.tag c i
    (P.seed c).drawRow (B := B) name (probes ℓ D) i.val a.pos a.a =
      P.initialCopy p (P.maxPackets sc) (name ∘ P.stationRank) c i := by
  intro p a
  let v := P.grid.label c i
  have key : Nat.pair (P.seed c).color (P.stationRank v) = P.nodeRank v := by
    have h := congrArg (fun c : P.Occupied => c.val.1) (P.grid.label_cell c i)
    unfold nodeRank
    exact congrArg (fun x => Nat.pair (P.hostRank x) _) h.symm
  have hrow (w) : (P.seed c).rows.getD i.val w = P.entry v := by
    simp [seed, List.getD_eq_getElem?_getD, v]
  unfold Seed.drawRow
  rw [hrow]
  simp only [entry, key, P.inspect_label H sc.Rpos (P.maxPackets sc)]
  have hr : a.label = P.tag (n := probes ℓ D) c (.inl v) := rfl
  change _ = (⟨a.pos, a.a, 0, a.label.role, a.label.name.map _, [], _⟩ : Entry F (d * b) d B A)
  rw [hr]
  by_cases h : P.mobile v <;> simp [inspect, tag, h, v]

def initialTile : Tile F (d * b) d q B A :=
  let p := P.kit sc hK
  let row := P.originRecord p (P.maxPackets sc) (name ∘ P.stationRank) stamp shape
  ⟨row.body (seamName color ∘ P.grid.seamRank) c, {(stamp c, .inl (p c).program.labels)}⟩

theorem initial_tile :
    (P.seed c).tile hK name color (stamp c) (shape c) = P.initialTile sc hK name color stamp shape c := by
  let p := P.kit sc hK
  let u := P.grid.template K P.weight c
  let a := P.planAt sc K c
  have ha := P.seed_identifies (K := K) sc H c
  have he : ∃ q : Pattern K D g (probes ℓ D), (P.seed c).Identifies (d * b) q := ⟨a, ha⟩
  rw [Seed.tile, dite_eq_left he, he.choose_spec.unique ha]
  have rows (i : Fin (P.grid.stations c).card) :
      (P.seed c).drawRow (B := B) name (probes ℓ D) i.val ((p c).pos (.inl (u.old i))) (u.level (u.old i)) =
      P.initialCopy p (P.maxPackets sc) (name ∘ P.stationRank) c i := P.row_eq sc hK H name c i
  have ports (i : Fin (P.grid.ports c).card) :
      (seamName color (((P.seed c).ordered (d * b)).getD i.val 0), (p c).pos (.inl (u.edge i)), u.level (u.edge i)) =
      (seamName color (P.grid.seamRank (P.grid.seam c i)), (p c).pos (.inl (u.edge i)), P.grid.energy (d * b) (P.grid.seam c i)) := by
    rw [P.ordered_seams H sc.Rpos, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
    change (_, _, (d * b) * (8 * (P.grid.mark c (Fin.natAdd _ i)).card ^ 2)) = _
    rw [Grid.mark_seam]
    rfl
  dsimp only [Seed.draw, initialTile, Record.body, originRecord]
  congr 2
  · change P.initialAux p stamp shape c none :: (List.ofFn (fun i => P.initialAux p stamp shape c (some i)) ++
      List.ofFn (fun i : Fin (P.grid.stations c).card => (P.seed c).drawRow name (probes ℓ D) i.val
        ((p c).pos (.inl (u.old i))) (u.level (u.old i)))) = _
    rw [funext rows]
  · change List.ofFn (fun i : Fin (P.grid.ports c).card =>
      (seamName color (((P.seed c).ordered (d * b)).getD i.val 0), (p c).pos (.inl (u.edge i)), u.level (u.edge i))) =
      (List.ofFn (fun i => (P.grid.seam c i, (p c).pos (.inl (u.edge i))))).map _
    rw [funext ports, List.map_ofFn]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Local initialization on a common host

An occurrence reads its own pattern and the patterns at its neighbors.
The mobile flags and short colors are additional local data. Vacant
slots can be detected because every actual station has positive arity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Assembly Coloring Sphere
open scoped Classical

variable {F : Type} [Field F] {m d k e : ℕ}

/-- The route may specify arbitrarily wide bundles. It is a function
of the pattern labels, not a separate tape of individual bit addresses. -/
def localView (p : Pattern F d k e) (near : B d → Pattern F d k e) (tone : B d → ℕ)
    (mobile : B k → Bool) (j : B k) : StationView F :=
  ⟨p.orderedTable j, mobile j, Scheme.Presentation.route p j near (fun i j => Nat.pair (tone i) j.val)⟩

def localSeed (p : Pattern F d k e) (color : ℕ) (near : B d → Pattern F d k e) (tone : B d → ℕ)
    (mobile : B k → Bool) : Seed F :=
  arrange color ((univ.filter fun j => Nonempty (p.Pin j)).image fun j =>
    (j.val, localView p near tone mobile j))

variable {x y : Wire} {h D T r g : ℕ} {W : ℝ} (P : Input F x y h D T r g W)
    {S : Scheme F} {s : S.format.obj} (p : S.Presentation s P.diagram)

/-- Relation between the diagram placement and its ordered presentation. -/
structure Placed (addr : P.Occupied ↪ B S.m × B S.h) (tone : B S.m → ℕ)
    (mobile : S.Vtx → Bool) : Prop where
  standard : p.Canonical
  location : ∀ v, ((p.vertex v).1, (p.vertex v).2.1) = addr (P.grid.cell v)
  color : ∀ c, P.hostRank c.val.1 = tone (addr c).1
  name : ∀ v, P.stationRank v = (p.vertex v).2.2.val
  flag : ∀ v, decide (P.mobile v) = mobile (p.vertex v)

theorem occupied_slot (v : S.Vtx) : Nonempty (S.LocalPin s v) ↔ v ∈ Set.range p.vertex := by
  constructor
  · rintro ⟨x⟩
    exact p.cover (S.port s v x)
  · rintro ⟨i, rfl⟩
    let l := P.diagram.table i
    let j := (Transcript.positions (.pair l.1 l.2.1)).symm ⟨0, P.positive i⟩
    exact ⟨p.pin i j⟩

variable {P p} {addr : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ}
  {mobile : S.Vtx → Bool} (H : P.Placed p addr tone mobile)
include H

theorem Placed.inspect (v : P.diagram.V) :
    let i := p.vertex v
    P.inspect v = localView (S.pattern s i) (fun j => S.pattern s ((s i.1).1 j, i.2.1, i.2.2))
      (fun j => tone ((s i.1).1 j)) (fun j => mobile (i.1, i.2.1, j)) i.2.2 := by
  intro i
  let f (j : S.Vtx) := Nat.pair (tone j.1) j.2.2.val
  have key : P.nodeRank = f ∘ p.vertex := by
    funext v
    unfold nodeRank
    have := H.color (P.grid.cell v)
    rw [← H.location] at this
    change P.hostRank (P.place v).1 = tone (p.vertex v).1 at this
    rw [this, H.name]; rfl
  unfold Input.inspect localView
  rw [key, (H.standard v).2 f, H.flag]
  congr 1
  exact (H.standard v).1

/-- Initial data depend only on local pattern records and short colors. -/
theorem Placed.seed_eq (hr : P.LocalRanks) (c : P.Occupied) :
    let i := addr c
    P.seed c = localSeed (S.decode ((s i.1).2 i.2)) (tone i.1)
      (fun j => S.decode ((s ((s i.1).1 j)).2 i.2)) (fun j => tone ((s i.1).1 j))
      (fun j => mobile (i.1, i.2, j)) := by
  intro i
  let A := S.decode ((s i.1).2 i.2)
  let row := localView A (fun j => S.decode ((s ((s i.1).1 j)).2 i.2))
    (fun j => tone ((s i.1).1 j)) (fun j => mobile (i.1, i.2, j))
  have e (v : P.diagram.V) (k : B S.k) (h : p.vertex v = (i.1, i.2, k)) :
      P.entry v = (k.val, row k) := by
    rw [entry, H.name, H.inspect, h]
    rfl
  have eq : (P.grid.stations c).image P.entry =
      (univ.filter fun j => Nonempty (A.Pin j)).image (fun k => (k.val, row k)) := by
    ext x
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : P.grid.cell v = c := by simpa [Grid.stations] using hv
      let k := (p.vertex v).2.2
      have he : p.vertex v = (i.1, i.2, k) := by
        have := H.location v
        rw [hv'] at this
        change ((p.vertex v).1, (p.vertex v).2.1) = (i.1, i.2) at this
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj this
        exact Prod.ext h₁ (Prod.ext h₂ rfl)
      exact ⟨k, (P.occupied_slot p _).mpr ⟨v, he⟩, (e v k he).symm⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨v, hv⟩ := (P.occupied_slot p (i.1, i.2, k)).mp hk
      have he : P.grid.cell v = c := by
        apply addr.injective
        rw [← H.location v, hv]
      exact ⟨v, by simp [Grid.stations, he], e v k hv⟩
  rw [P.seed_arrange hr, H.color, eq]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Putting a presented local input in canonical order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {s : S.format.obj} {G : Diagram F x y}
  (p : S.Presentation s G) (h : p.Directed)

theorem ordered_source : (p.ordered h).source = G.source := rfl
theorem ordered_target : (p.ordered h).target = G.target := rfl
theorem ordered_portEnd : Packing.portEnd (p.ordered h) = Packing.portEnd G := rfl

theorem ordered_arity : (p.ordered h).arity = G.arity := by
  funext v
  have e := Fintype.card_congr ((p.stationPin v).trans (p.pin v).symm)
  simp only [Transcript.Ports, Fintype.card_sum, card_slots] at e
  exact e

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Assembly Coloring Sphere
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {s : S.format.obj}
  {x y : Wire} {h D T r g : ℕ} {W : ℝ} (P : Input F x y h D T r g W)
  (p : S.Presentation s P.diagram) (direct : p.Directed) (host : P.V → ℕ)

/-- Retain every port endpoint, station and host position. -/
def normalize : Input F x y h D T r g W where
  V := P.V
  diagram := p.ordered direct
  place := P.place
  adj := P.adj
  sym := P.sym
  degree := P.degree
  edge := P.edge
  loopless := P.loopless
  positive := by rw [p.ordered_arity direct]; exact P.positive
  width := P.width
  mobile := P.mobile
  ext := P.ext
  occupied := P.occupied
  immobile := P.immobile
  count := P.count
  mass := by rw [p.ordered_arity direct]; exact P.mass
  squares := by rw [p.ordered_arity direct]; exact P.squares
  ranks := some (fun v => (p.vertex v).2.2.val, host)

theorem normalize_eval : (P.normalize p direct host).diagram.eval = P.diagram.eval :=
  funext fun x => funext fun y => p.ordered_eval direct x y

theorem normalize_order : (P.normalize p direct host).diagram.PortOrder (2 ^ (S.e + 1)) :=
  p.ordered_order direct

theorem normalize_placed (addr : P.Occupied ↪ B S.m × B S.h) (tone : B S.m → ℕ)
    (mobile : S.Vtx → Bool)
    (loc : ∀ v, ((p.vertex v).1, (p.vertex v).2.1) = addr (P.grid.cell v))
    (color : ∀ c, host c.val.1 = tone (addr c).1)
    (mob : ∀ v, decide (P.mobile v) = mobile (p.vertex v)) :
    (P.normalize p direct host).Placed (p.toOrdered direct) addr tone mobile :=
  ⟨p.canonical_ordered direct, loc, color, fun _ => rfl, mob⟩

variable {P p}
theorem Placed.ranks {addr : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ}
    {mobile : S.Vtx → Bool} (hp : P.Placed p addr tone mobile)
    (supplied : P.ranks.isSome) (inj : ∀ u, Set.InjOn P.hostRank (insert u (P.adj u) : Finset P.V)) :
    P.LocalRanks := by
  refine ⟨supplied, ?_, inj⟩
  intro u v h₁ h₂
  have cell : P.grid.cell u = P.grid.cell v := Subtype.ext h₁
  have eq := (hp.location u).trans ((congrArg addr cell).trans (hp.location v).symm)
  obtain ⟨ha, hb⟩ := Prod.mk.inj eq
  rw [hp.name, hp.name] at h₂
  exact p.vertex.injective (Prod.ext ha (Prod.ext hb (Fin.ext h₂)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # A common host chart for the initial sphere layout -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Assembly Coloring Sphere.Surface.Local
open scoped Classical

variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W) (S : Scheme F) (s : S.format.obj)

structure HostChart where
  host : P.V ↪ B S.m
  block : Packing.Cell h ↪ B S.h
  adjacent : ∀ i j, j ∈ P.adj i → i ≠ j → ∃ k, (s (host i)).1 k = host j
  reciprocal : Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) s

namespace HostChart
variable {P S s} (A : P.HostChart S s)

def coord : P.Occupied ↪ B S.m × B S.h :=
  ⟨fun c => (A.host c.val.1, A.block c.val.2), fun _ _ e =>
    Subtype.ext (Prod.ext (A.host.injective (congrArg Prod.fst e)) (A.block.injective (congrArg Prod.snd e)))⟩

def graph (_ : P.HostChart S s) (v : B S.m) := (s v).1

theorem sym : ∀ i j, A.graph i j ≠ i → ∃ k, A.graph (A.graph i j) k = i :=
  fun i j h => (A.reciprocal i j h).exists

def atlas (hr : 0 < r) : Atlas P.Occupied P.grid.Seam S.m S.d S.h where
  coord := A.coord
  graph := A.graph
  reciprocal := A.sym
  src j := j.val.1
  dst j := j.val.2
  links := Subtype.val_injective
  adjacent j := by
    obtain ⟨n, hn, hm⟩ := j.property.2
    have ne := j.property.1
    rw [← hn, ← hm] at ne ⊢
    obtain ⟨eq, hadj⟩ := P.contact hr n
    have dif : (P.place (P.grid.src n)).1 ≠ (P.place (P.grid.dst n)).1 :=
      fun he => ne (Subtype.ext (Prod.ext he eq.symm))
    exact ⟨congrArg A.block eq.symm, A.adjacent _ _ (hadj.resolve_left dif.symm) dif⟩

def tone (R : ℕ) := Neighborhood.tone A.graph R

def palette (hr : 0 < r) (R : ℕ) : Palette (A.atlas hr) R (Neighborhood.paletteSize S.d R) :=
  ⟨A.tone R, Neighborhood.tone_separates _ R A.sym⟩

def rank (R : ℕ) (v : P.V) := (A.tone R (A.host v)).val

theorem distinguishes (R : ℕ) (hR : 2 ≤ R) (v : P.V) :
    Set.InjOn (A.rank R) (insert v (P.adj v) : Finset P.V) := by
  have one (w : P.V) (h : w ∈ insert v (P.adj v)) : Neighborhood.Reach A.graph 1 (A.host v) (A.host w) := by
    by_cases e : w = v
    · subst w; exact .refl ..
    exact ⟨_, .inr (A.adjacent _ _ ((mem_insert.mp h).resolve_left e) (Ne.symm e)), rfl⟩
  intro i hi j hj he
  have two := ((one i hi).symm A.sym).join (one j hj)
  have e := two.join (Neighborhood.Reach.refl A.graph (R - 2) (A.host j))
  rw [show 1 + 1 + (R - 2) = R by omega] at e
  exact A.host.injective (Neighborhood.tone_separates _ _ A.sym _ _ e (Fin.ext he))

variable [Field F] (p : S.Presentation s P.diagram) (dir : p.Directed) (R : ℕ)

/-- Add short local ranks after putting the stations in span order. -/
def normalized := P.normalize p dir (A.rank R)

def next : (A.normalized p dir R).HostChart S s :=
  ⟨A.host, A.block, A.adjacent, A.reciprocal⟩

theorem normalized_placed (mobile : S.Vtx → Bool)
    (loc : ∀ v, ((p.vertex v).1, (p.vertex v).2.1) = A.coord (P.grid.cell v))
    (mob : ∀ v, decide (P.mobile v) = mobile (p.vertex v)) :
    (A.normalized p dir R).Placed (p.toOrdered dir) (A.next p dir R).coord (fun i => (A.tone R i).val) mobile :=
  P.normalize_placed p dir (A.rank R) A.coord _ mobile loc (fun _ => rfl) mob

theorem normalized_ranks (hR : 2 ≤ R) (mobile : S.Vtx → Bool)
    (loc : ∀ v, ((p.vertex v).1, (p.vertex v).2.1) = A.coord (P.grid.cell v))
    (mob : ∀ v, decide (P.mobile v) = mobile (p.vertex v)) : (A.normalized p dir R).LocalRanks :=
  (A.normalized_placed p dir R mobile loc mob).ranks rfl (A.distinguishes R hR)

end HostChart
end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # The initial frame of a colored, planted local concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Finset Sphere Surface Surface.Local Assembly Coloring Routing.Private SphereScale
open scoped Classical

variable {F K : Type}

/-- Parameters shared across host records and all initial energy shapes. -/
abbrev design (S : Scheme F) (g ℓ D b d p l : ℕ) : Surface.Local.Design :=
  let U := D ^ 5
  let M := room ℓ D g
  let R := Neighborhood.paletteSize S.d (2 * U + 2)
  let Q := Neighborhood.paletteSize S.d (horizon U (R * M) 0)
  ⟨d * b, d, S.m, S.d, S.h, U, R, Q, M, 2 * g, SphereScale.energy ℓ D (d * b), depth ℓ D g (p ^ l) (d * b), p, l⟩

abbrev finiteName (j : ℕ) (v : ℕ) : B j := Fin.ofNat _ v

variable [Field F] [Field K] [Algebra K F] {x y : Wire} {h g ℓ D T b d p l : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
  (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "Cfg" => design S g ℓ D b d p l
local notation "kit" => P.kit sc hK

def scheduling := A.palette sc.Rpos (2 * (Cfg).U + 2)
def aliases := A.palette sc.Rpos (horizon (Cfg).U (Cfg).waves 0)

def bootMark (v : P.Occupied) : Stamp (Cfg).Q (Cfg).waves (Cfg).U :=
  ((P.aliases A sc).mark v, none)

def bootRecord := P.originRecord kit (P.maxPackets sc) (finiteName S.k ∘ P.stationRank)
  (P.bootMark A sc) s

def localWorld : Scenario F (B S.k) (B S.ℓ) Cfg x y where
  V := P.Occupied
  E := P.grid.Seam
  T := P.diagram.V
  X := P.Parameters kit
  J := P.Occupied
  L := P.grid.Seam
  atlas := A.atlas sc.Rpos
  π := P.scheduling A sc
  c := P.aliases A sc
  ref := P.reference kit (finiteName S.k ∘ P.stationRank)
  origin := P.plant kit s
  pos := (P.bootRecord A sc hK s).positions
  size v := (kit v).program.labels
  header j := (z j.1).2 j.2
  controls := ⟨_, _, P.plant_controls kit s⟩
  room _ reach := P.moved_room kit s sc reach
  close a b :=
    { toFun := fun f => ∑ k, f ((a, b), k)
      map_add' := by intros; simp [sum_add_distrib]
      map_smul' := by intros; simp [mul_sum] }

def start : (P.localWorld A sc hK s).At 0 := by
  have : NeZero (Cfg).Q := ⟨by unfold design Neighborhood.paletteSize; positivity⟩
  have mat := P.matches_origin kit (P.maxPackets sc) (finiteName S.k ∘ P.stationRank)
    (P.bootMark A sc) s (startName (P.aliases A sc)) (fun _ => rfl)
  refine Frame.initial (P.scheduling A sc) (P.aliases A sc) mat (fun _ => rfl)
    ?_ (P.plant_layout kit s sc.Rpos) (P.plant_valid kit s _) (P.plant_clock kit s)
  intro v
  exact ((P.moved_room kit s sc (U := D ^ 5) .refl).length v)

theorem start_sum (a : Val x) (b : Val y) :
    P.diagram.eval a b = ∑ s, (P.localWorld A sc hK s).eval (P.start A sc hK s) a b :=
  (P.eval_plant kit a b).symm

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Reading the initial wave records from the local input -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Surface Surface.Local Assembly Coloring Routing.Private SphereScale
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h g ℓ D T b d p l : ℕ} {W : ℝ}

def live (S : Scheme F) (own : B S.ℓ) : Prop := ∃ j, Nonempty ((S.decode own).Pin j)

theorem Placed.live_iff {r : ℕ} {P : Input F x y h D T r g W}
    {S : Scheme F} {z : S.format.obj} {t : S.Presentation z P.diagram}
    {addr : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
    (H : P.Placed t addr tone mobile) (w : B S.m × B S.h) :
    live S ((z w.1).2 w.2) ↔ w ∈ Set.range addr := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨v, hv⟩ := (P.occupied_slot t (w.1, w.2, j)).mp hj
    exact ⟨P.grid.cell v, by rw [← H.location v, hv]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨v, _, hv⟩ := mem_image.mp c.property
    have he : P.grid.cell v = c := Subtype.ext hv
    rw [← he, ← H.location v]
    exact ⟨(t.vertex v).2.2, (P.occupied_slot t _).mpr ⟨v, rfl⟩⟩

variable (S : Scheme F)

local notation "Cfg" => design S g ℓ D b d p l
local notation "colorAt" => finiteName ((S.d + 1) * (2 * (Surface.Local.Design.U Cfg) + 2) + 1)

/-- The data of an occupied occurrence, using only its own pattern,
short colors, and the patterns at neighboring hosts. -/
def viewStart (hK : Ready K ℓ D g (p ^ l) b d) (own : B S.ℓ)
    (tone : Fin (Cfg).R) (keyTone : Fin (Cfg).Q) (near : B S.d → B S.ℓ)
    (colors : B S.d → Fin (Cfg).R) (mobile : B S.k → Bool)
    (shape : Shape (probes ℓ D) b d) : B S.ℓ × (Cfg).row F (B S.k) :=
  let v := localSeed (S.decode own) tone.val (fun j => S.decode (near j))
    (fun j => (colors j).val) mobile
  let stamp : Stamp (Cfg).Q (Cfg).waves (Cfg).U := (keyTone, none)
  let tile := v.tile hK (finiteName S.k) colorAt stamp shape
  (own, some (tone, keyTone, (fun i : Fin (Cfg).M => (tile.rows[i.val]?.map Entry.pos).getD 0), tile))

variable {S} (P : Input F x y h D T (d * b) g W) {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
  (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "world" => P.localWorld A sc hK s
local notation "frame" => P.start A sc hK s
local notation "schedulingTone" => A.tone (2 * (Surface.Local.Design.U Cfg) + 2)
local notation "aliasTone" => A.tone (horizon (Surface.Local.Design.U Cfg) (Surface.Local.Design.waves Cfg) 0)

theorem start_away (w : B S.m × B S.h) (hw : w ∉ Set.range A.coord) :
    (world).stored frame w = ((z w.1).2 w.2, none) := by
  unfold Scenario.stored
  rw [Palette.records_away _ _ _ _ _ hw]
  rfl

variable {t : S.Presentation z P.diagram} {mobile : S.Vtx → Bool}
  (H : P.Placed t A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val) mobile)
include H

private theorem edge_start :
    seamName colorAt ∘ P.grid.seamRank = (P.scheduling A sc).edge := by
  have h (v : P.Occupied) : colorAt (P.grid.cellRank v) = (P.scheduling A sc).mark v := by
    change colorAt (P.hostRank v.val.1) = schedulingTone (A.coord v).1
    rw [H.color]
    exact Fin.ext (Nat.mod_eq_of_lt (schedulingTone (A.coord v).1).isLt)
  funext j
  simp only [Function.comp_apply, Grid.seamRank, seamName, Nat.unpair_pair, h]
  rfl

theorem start_at (hr : P.LocalRanks) (c : P.Occupied) :
    let i := A.coord c
    (world).stored frame i = viewStart S hK ((z i.1).2 i.2)
      (schedulingTone i.1) (aliasTone i.1) (fun j => (z ((z i.1).1 j)).2 i.2)
      (fun j => schedulingTone ((z i.1).1 j)) (fun j => mobile (i.1, i.2, j)) (s c) := by
  intro i
  have info : (frame).info (world).size c = {(P.bootMark A sc c, .inl ((P.kit sc hK c).program.labels))} := by
    unfold Frame.info catalog
    rw [show (frame).stage.footprint c = {.inl c} from rfl, image_singleton]
    rfl
  have tile := P.initial_tile sc hK hr (finiteName S.k) colorAt (P.bootMark A sc) s c
  rw [H.seed_eq hr c, initialTile, P.edge_start A sc H] at tile
  unfold Scenario.stored
  erw [(world).π.records_at (world).c (world).pos (frame).record ((frame).info (world).size) c]
  unfold Record.tile
  rw [info]
  dsimp only [viewStart]
  erw [tile]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Exterior widths and port order at the named collectors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Coloring Assembly Sphere
open scoped Classical

namespace Assembly.Scheme
variable {F : Type} (S : Scheme F)

/-- Width of the exposed part of a requested station and side. -/
def extWidth (own : B S.ℓ) (slot : Option (B S.k)) (b : Bool) :=
  slot.elim 0 fun j => Fintype.card {i : (S.decode own).Pin j //
    (S.decode own).peer j i.1 = none ∧ (S.decode own).direction j i.1 = b}

private abbrev Outside (r : S.format.obj) (v : S.Vtx) (b : Bool) :=
  {w : S.exposed r // w.val.1.1 = v ∧ S.direction r w.val.1 = b}

private theorem extWidth_eq (r : S.format.obj) (v : S.Vtx) (b : Bool) :
    S.extWidth ((r v.1).2 v.2.1) (some v.2.2) b = Fintype.card (S.Outside r v b) := by
  let Y := {i : S.LocalPin r v // (S.pattern r v).peer v.2.2 i.1 = none ∧
      (S.pattern r v).direction v.2.2 i.1 = b}
  let f (i : Y) : S.Outside r v b :=
    ⟨⟨S.port r v i.val, by simp [port, peer, i.property.1]⟩, rfl, i.property.2⟩
  have bij : Function.Bijective f := by
    constructor
    · intro i j he
      have h₁ : i.val.1 = j.val.1 := congrArg (fun w : S.Outside r v b => w.val.val.1.2) he
      have h₂ : i.val.2.val = j.val.2.val := congrArg (fun w : S.Outside r v b => w.val.val.2.val) he
      exact Subtype.ext (Sigma.ext h₁ ((Fin.heq_ext_iff (congrArg _ h₁)).mpr h₂))
    · rintro ⟨⟨⟨⟨u, i⟩, j⟩, he⟩, hv, hd⟩
      change u = v at hv
      subst u
      have hp : (S.pattern r v).peer v.2.2 i = none := by simpa [peer] using he
      exact ⟨⟨⟨i, j⟩, hp, hd⟩, rfl⟩
  exact Fintype.card_congr (Equiv.ofBijective f bij)

namespace Presentation
variable {S} [Field F] {x y : Wire} {G : Diagram F x y} {r : S.format.obj}
  (p : S.Presentation r G) (hd : p.Directed)
include hd

private theorem side_length {α : Type} (v : G.V) (b : Bool) (lift : α → slots x ⊕ slots y)
    (l : List α) (hi : Function.Injective lift) (side : ∀ a, (lift a).isRight = b)
    (onto : ∀ j, j.isRight = b → ∃ a, lift a = j)
    (hn : l.Nodup) (hm : ∀ a, a ∈ l ↔ Packing.portEnd G (lift a) = v) :
    l.length = Fintype.card (S.Outside r (p.vertex v) b) := by
  have dir (i : slots x ⊕ slots y) : S.direction r (p.boundary i).val.1 = i.isRight := by
    cases i <;> exact hd _
  let f (i : Fin l.length) : S.Outside r (p.vertex v) b :=
    ⟨p.boundary (lift (l.get i)), by rw [Sphere.Payload.owner, (hm _).mp (l.get_mem i)], (dir _).trans (side _)⟩
  have bij : Function.Bijective f := by
    constructor
    · intro i j he
      have eq : l.get i = l.get j := hi (p.boundary.injective (congrArg Subtype.val he))
      rcases lt_trichotomy i j with lt|rfl|gt
      · exact ((List.pairwise_iff_get.mp hn) i j lt eq).elim
      · rfl
      · exact ((List.pairwise_iff_get.mp hn) j i gt eq.symm).elim
    · rintro ⟨w, hv, hb⟩
      obtain ⟨j, rfl⟩ := p.boundary.surjective w
      obtain ⟨a, rfl⟩ := onto j ((dir j).symm.trans hb)
      rw [Sphere.Payload.owner] at hv
      obtain ⟨i, rfl⟩ := List.get_of_mem ((hm a).mpr (p.vertex.injective hv))
      exact ⟨i, rfl⟩
  exact (Fintype.card_fin _).symm.trans (Fintype.card_congr (Equiv.ofBijective f bij))

theorem exterior_width (v : G.V) (b : Bool) :
    cond b (G.extRight v).length (G.extLeft v).length =
      S.extWidth ((r (p.vertex v).1).2 (p.vertex v).2.1) (some (p.vertex v).2.2) b := by
  rw [S.extWidth_eq]
  cases b
  · exact p.side_length hd v false Sum.inl _ Sum.inl_injective (fun _ => rfl)
      (by rintro (a|b) <;> simp) (G.extLeft_nodup v) (G.mem_extLeft v)
  · exact p.side_length hd v true Sum.inr _ Sum.inr_injective (fun _ => rfl)
      (by rintro (a|b) <;> simp) (G.extRight_nodup v) (G.mem_extRight v)

end Presentation
end Assembly.Scheme

namespace Rounds.Input
open Surface Routing.Private
open Sphere.Layout (Place item)

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ H U : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)
  (p : P.Tools K ℓ m) (s : P.Occupied → Shape (SphereScale.probes ℓ D) b d)
  {z : P.Configuration p} (hz : (P.plant p s).Reach m (2 * g) H U z)
  {S : Scheme F} {r : S.format.obj} {portal : S.Presentation r P.diagram}
  {loc : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
  (placed : P.Placed portal loc tone mobile)
include placed

/-- An exterior wire stays with both of its station's ordered lists in the same cell. -/
theorem keeps (e : slots x ⊕ slots y) :
    let v := Packing.portEnd P.diagram e
    ∃ i : Place z.scene.cell, loc i.1 = ((portal.vertex v).1, (portal.vertex v).2.1) ∧
      (P.inputPorts p s hz).ports i = P.diagram.extLeft v ∧
      (P.outputPorts p s hz).ports i = P.diagram.extRight v := by
  intro v
  let i := P.draw p s hz e
  have name : (item z.scene.cell i).label.name = some v := P.draw_name p s hz e
  have pos : P.grid.cell v = i.1 := (P.reached_name p s hz (List.get_mem _ i.2) name).2
  refine ⟨i, by rw [← pos, placed.location], ?_⟩
  change (item z.scene.cell i).label.name.elim [] P.diagram.extLeft = _ ∧
    (item z.scene.cell i).label.name.elim [] P.diagram.extRight = _
  simp only [name, Option.elim_some, and_self]

theorem portsWidth (hd : portal.Directed) (i : Place z.scene.cell) (bit : Bool) :
    cond bit ((P.outputPorts p s hz).ports i).length ((P.inputPorts p s hz).ports i).length =
      S.extWidth ((r (loc i.1).1).2 (loc i.1).2)
        ((item z.scene.cell i).label.name.map (finiteName S.k ∘ P.stationRank)) bit := by
  let n := (item z.scene.cell i).label.name
  change cond bit (n.elim [] P.diagram.extRight).length (n.elim [] P.diagram.extLeft).length =
    S.extWidth _ (n.map _) bit
  cases he : n with
  | none => cases bit <;> rfl
  | some v =>
    have pos : P.grid.cell v = i.1 := (P.reached_name p s hz (List.get_mem _ i.2) he).2
    have name : finiteName S.k (P.stationRank v) = (portal.vertex v).2.2 := by
      rw [placed.name]
      exact Fin.ext (Nat.mod_eq_of_lt (portal.vertex v).2.2.isLt)
    simp only [Option.elim_some, Option.map_some, Function.comp_apply, name, ← pos, ← placed.location]
    exact portal.exterior_width hd v bit

end Rounds.Input
end OAI.LinearAlgebra.MatrixExponent
end

/-! # The records consumed by the printer at the end of the waves -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {h g ℓ D T b d p l j : ℕ} {W : ℝ} (S : Scheme F)

local notation "Cfg" => design S g ℓ D b d p l

abbrev panelKeys (a : Surface.Local.Design) := Stamp a.Q a.waves a.U

/-- Retain the initial exterior widths and the final station and seam data. -/
def panelFaces (menu : (Cfg).Menu F (B S.k) (B S.ℓ) j) (i : B j) :
    Option (Print.Face F (d * b) d (Cfg).R (panelKeys Cfg) (B S.k)) :=
  (menu i).2.map fun v => ⟨S.extWidth (menu i).1, v.1, v.2.2.2⟩

def printMenu (menu : (Cfg).Menu F (B S.k) (B S.ℓ) j) {M r t : ℕ}
    (ha : d * b = M * r) (hb : d = M * t) (i : B j) :
    Option (Print.Face F (M * r) (M * t) (Cfg).R (panelKeys Cfg) (B S.k)) :=
  cast (congrArg₂ (fun v w => Option (Print.Face F v w (Cfg).R (panelKeys Cfg) (B S.k))) ha hb)
    (panelFaces S menu i)

variable {S} (P : Input F x y h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "kit" => P.kit sc hK
local notation "world" => P.localWorld A sc hK s

abbrev finalSource (f : (world).At (Cfg).waves) := P.shared kit s f.reach sc.Rpos

theorem panelBounds (f : (world).At (Cfg).waves) :
    P.FinalBounds (P.finalSource A sc hK s f) ℓ (p ^ l) :=
  P.final_bounds kit sc s f.stage f.reach f.stopped

def panelExt (i : P.Occupied) := S.extWidth ((z (A.coord i).1).2 (A.coord i).2)

def panelIndex (v : P.Occupied) : (P.selectors kit).state v ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

def panelFace (f : (world).At (Cfg).waves) (i : (world).V) :
    Print.Face F (d * b) d (Cfg).R (panelKeys Cfg) (B S.k) :=
  ⟨P.panelExt A i, (world).π.mark i, f.record.tile (world).π.edge (f.info (world).size) i⟩

theorem panel_read {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j}
    (f : (world).Code (Cfg).waves menu) (i : B S.m × B S.h) :
    panelFaces S menu ((f.tape i.1).2 i.2) = (world).atlas.fill (P.panelFace A sc hK s f.frame) i := by
  unfold panelFaces
  rw [f.read]
  unfold Scenario.stored
  by_cases hi : i ∈ Set.range (world).atlas.coord
  · obtain ⟨v, rfl⟩ := hi
    erw [Palette.records_at, Atlas.fill_at]
    rfl
  · erw [Palette.records_away _ _ _ _ _ hi, Atlas.fill_away _ _ hi]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end
