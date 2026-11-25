import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Ledger
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Owners
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.View

/-!
# Ordering initial data by local keys

Station numbers only need to distinguish one occupied cell, and host
numbers one closed neighborhood. A packet is then identified by its
two endpoint keys and its quotient index in the parallel bundle.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Packing
open scoped Classical
variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W)

structure LocalRanks : Prop where
  supplied : P.ranks.isSome
  stations : ∀ a b, P.place a = P.place b → P.stationRank a = P.stationRank b → a = b
  hosts : ∀ u, Set.InjOn P.hostRank (insert u (P.adj u) : Finset P.V)

def atHost (c : P.Occupied) (v : P.diagram.V) :=
  (P.place v).2 = c.val.2 ∧ (P.place v).1 ∈ insert c.val.1 (P.adj c.val.1)

def incidentPacket (c : P.Occupied) (e : P.Edges) :=
  P.grid.cell (P.grid.src e) = c ∨ P.grid.cell (P.grid.dst e) = c

theorem endpoints_atHost (hr : 0 < r) (c : P.Occupied) (e : P.Edges) (he : P.incidentPacket c e) :
    P.atHost c (P.grid.src e) ∧ P.atHost c (P.grid.dst e) := by
  obtain ⟨block, edge⟩ := P.contact hr e
  rcases he with h|h
  · have h' : P.place (P.grid.src e) = c.val := congrArg Subtype.val h
    rw [h'] at edge block
    simp only [atHost, h', mem_insert]
    exact ⟨⟨True.intro, .inl True.intro⟩, block, edge⟩
  · have h' : P.place (P.grid.dst e) = c.val := congrArg Subtype.val h
    rw [h'] at edge block
    simp only [atHost, h', mem_insert]
    exact ⟨⟨block.symm, edge.imp Eq.symm (P.sym _ _)⟩, True.intro, .inl True.intro⟩

variable {P}

theorem LocalRanks.node (H : P.LocalRanks) {c : P.Occupied} {a b : P.diagram.V}
    (ha : P.atHost c a) (hb : P.atHost c b) (he : P.nodeRank a = P.nodeRank b) : a = b := by
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.mp he
  exact H.stations a b (Prod.ext (H.hosts _ ha.2 hb.2 h₁) (ha.1.trans hb.1.symm)) h₂

theorem LocalRanks.station (H : P.LocalRanks) (c : P.Occupied) :
    Set.InjOn P.grid.stationRank (P.grid.stations c) := by
  intro a ha b hb h
  simp only [Grid.stations, mem_coe, mem_filter, mem_univ, true_and] at ha hb
  exact H.stations a b (congrArg Subtype.val (ha.trans hb.symm)) h

variable (P)

private def first (hr : 0 < r) (e : P.Edges) := P.packets.bits.symm (e, ⟨0, hr⟩)

private theorem first_eq (hr : 0 < r) (e : P.Edges) : (P.packets.bits (P.first hr e)).1 = e :=
  congrArg Prod.fst (P.packets.bits.apply_symm_apply _)

theorem packetRank_eq (hr : 0 < r) (hs : P.ranks.isSome) (e : P.diagram.E) :
    P.packetRank (P.packets.bits e).1 = Nat.pair (P.nodeRank (P.diagram.source e))
      (Nat.pair (P.nodeRank (P.diagram.target e)) (ordinal P.diagram e / r)) := by
  let u := P.first hr (P.packets.bits e).1
  have hp : (P.packets.bits u).1 = (P.packets.bits e).1 := P.first_eq hr _
  have h₁ : P.diagram.source u = P.diagram.source e := by rw [← P.packets.left, hp, P.packets.left]
  have h₂ : P.diagram.target u = P.diagram.target e := by rw [← P.packets.right, hp, P.packets.right]
  have he := (P.packets_numbered.2 u e h₁ h₂).mp hp
  unfold packetRank
  rw [dite_eq_left (And.intro hs hr)]
  dsimp only
  rw [P.packets.left, P.packets.right, ← he]
  rfl

variable {P}

theorem LocalRanks.packet (H : P.LocalRanks) (hr : 0 < r) (c : P.Occupied) :
    Set.InjOn P.grid.packetRank {e | P.incidentPacket c e} := by
  intro i hi j hj he
  obtain ⟨a, b⟩ := P.endpoints_atHost hr c i hi
  obtain ⟨a', b'⟩ := P.endpoints_atHost hr c j hj
  change P.packetRank i = P.packetRank j at he
  unfold packetRank at he
  simp only [dite_eq_left (And.intro H.supplied hr), Nat.pair_eq_pair] at he
  have hs := H.node a a' he.1
  have ht := H.node b b' he.2.1
  let u := P.first hr i
  let v := P.first hr j
  have h₁ : P.diagram.source u = P.diagram.source v := by
    rw [← P.packets.left u, ← P.packets.left v, P.first_eq, P.first_eq]
    exact hs
  have h₂ : P.diagram.target u = P.diagram.target v := by
    rw [← P.packets.right u, ← P.packets.right v, P.first_eq, P.first_eq]
    exact ht
  have hh := (P.packets_numbered.2 u v h₁ h₂).mpr he.2.2
  simpa only [u, v, first_eq] using hh

theorem LocalRanks.mark (H : P.LocalRanks) (hr : 0 < r) (c : P.Occupied) (i : P.grid.Index c) :
    Set.InjOn P.grid.packetRank (P.grid.mark c i) :=
  (H.packet hr c).mono (fun _ h => P.grid.touches c i h)

theorem LocalRanks.seam (H : P.LocalRanks) (hr : 0 < r) (c : P.Occupied) :
    Set.InjOn P.grid.seamRank (P.grid.ports c) := by
  let next (v : P.Occupied) := v.val.2 = c.val.2 ∧ v.val.1 ∈ insert c.val.1 (P.adj c.val.1)
  have eq {u v : P.Occupied} (hu : next u) (hv : next v) (h : P.grid.cellRank u = P.grid.cellRank v) :
      u = v := Subtype.ext (Prod.ext (H.hosts _ hu.2 hv.2 h) (hu.1.trans hv.1.symm))
  have inside (i : P.grid.Seam) (hi : i ∈ P.grid.ports c) : next i.val.1 ∧ next i.val.2 := by
    obtain ⟨e, he, he'⟩ := i.property.2
    simp only [Grid.ports, mem_filter, mem_univ, true_and, ← he, ← he'] at hi
    rw [← he, ← he']
    exact P.endpoints_atHost hr c e hi
  intro i hi j hj e
  obtain ⟨a, b⟩ := inside i hi
  obtain ⟨a', b'⟩ := inside j hj
  obtain ⟨e, e'⟩ := Nat.pair_eq_pair.mp e
  exact Subtype.ext (Prod.ext (eq a a' e) (eq b b' e'))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
open Finset
open scoped Classical
theorem number_idxOf {A : Type} {s : Finset A} {f : A → ℕ} (hf : Set.InjOn f s) (x : s) :
    ((number f s).symm x).val = ((s.image f).sort (· ≤ ·)).idxOf (f x.val) := by
  let g i := f (number f s i).val
  have h : (List.ofFn g).Nodup := by rw [number_keys hf]; exact Finset.sort_nodup _ _
  have h' := h.idxOf_getElem ((number f s).symm x).val
    (by simp : ((number f s).symm x).val < (List.ofFn g).length)
  simp only [List.getElem_ofFn] at h'
  rw [← number_keys hf]
  simpa [g] using h'.symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

/-! # Reading a parallel bundle using only its endpoint keys and offsets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Packing
open scoped Classical

abbrev Peer := Bool × Option (ℕ × ℕ)
abbrev Line := (ℕ × ℕ) × ℕ

def line (v i : ℕ) (p : Peer) : Option Line :=
  p.2.map fun t => if p.1 then ((t.1, v), t.2) else ((v, t.1), i)

structure StationView (F : Type) where
  table : Table F
  mobile : Bool
  route : List Peer

def StationView.pin {F : Type} (v : StationView F) (i : ℕ) : Peer :=
  v.route[i]?.getD (false, none)

def StationView.line {F : Type} (v : StationView F) (k i : ℕ) := Input.line k i (v.pin i)

def rankEdge (i : Line) := Nat.pair i.1.1 (Nat.pair i.1.2 i.2)

variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ} (P : Input F x y h D T r g W)

def inspect (v : P.diagram.V) : StationView F where
  table := P.diagram.table v
  mobile := decide (P.mobile v)
  route := List.ofFn (fun i => ((P.diagram.peer v i).1,
    (P.diagram.peer v i).2.map (Prod.map P.nodeRank id)))

theorem inspect_pin (v : P.diagram.V) (i : Fin (P.diagram.arity v)) :
    (P.inspect v).pin i = ((P.diagram.peer v i).1, (P.diagram.peer v i).2.map (Prod.map P.nodeRank id)) := by
  simp [inspect, StationView.pin]

def wireKey (e : P.diagram.E) : Line :=
  ((P.nodeRank (P.diagram.source e), P.nodeRank (P.diagram.target e)), P.diagram.srcOffset e)

private theorem at_port (v : P.diagram.V) (j : Transcript.Ports (P.diagram.table v)) :
    let G := P.diagram
    let i := Transcript.positions (.pair (G.table v).1 (G.table v).2.1) j
    (P.inspect v).line (P.nodeRank v) i.val =
      (Transcript.wires G v j).elim (fun _ => none) (fun e => some (P.wireKey e)) := by
  intro G i
  unfold StationView.line
  rw [inspect_pin P v i]
  have h : G.peer v i = G.portPeer v j := by simp [Diagram.peer, i]
  rw [h]
  cases j with
  | inl j =>
    cases he : G.src ⟨v, j⟩ with
    | inl a => simp [Diagram.portPeer, Transcript.wires, he, line]
    | inr e =>
      have h : G.src.symm (.inr e) = ⟨v, j⟩ := G.src.symm_apply_eq.mpr he.symm
      simp only [Diagram.portPeer, Transcript.wires, he, line, Sum.map_inr, Sum.elim_inr, Option.map_some,
        Bool.false_eq_true, ↓reduceIte, id_eq]
      unfold wireKey Diagram.source Diagram.srcOffset
      rw [h]
      rfl
  | inr j =>
    cases he : G.dst ⟨v, j⟩ with
    | inl a => simp [Diagram.portPeer, Transcript.wires, he, line]
    | inr e =>
      have h : G.dst.symm (.inr e) = ⟨v, j⟩ := G.dst.symm_apply_eq.mpr he.symm
      simp only [Diagram.portPeer, Transcript.wires, he, line, Sum.map_inr, Sum.elim_inr, Option.map_some,
        ↓reduceIte, id_eq]
      unfold wireKey Diagram.target
      rw [h]
      rfl

theorem inspect_line (v : P.diagram.V) (i : Fin (P.diagram.arity v)) :
    (P.inspect v).line (P.nodeRank v) i =
      (P.diagram.wireAt v i).elim (fun _ => none) (fun e => some (P.wireKey e)) := by
  let a := Transcript.positions (.pair (P.diagram.table v).1 (P.diagram.table v).2.1)
  have h := P.at_port v (a.symm i)
  dsimp only at h
  rw [show Transcript.positions (.pair (P.diagram.table v).1 (P.diagram.table v).2.1) (a.symm i) = i from a.apply_symm_apply i] at h
  exact h

theorem has_slot (v : P.diagram.V) (e : P.diagram.E)
    (he : P.diagram.source e = v ∨ P.diagram.target e = v) :
    ∃ i, P.diagram.wireAt v i = .inr e := by
  have go (z : P.diagram.End) (h : P.diagram.station z = v) (hz : P.diagram.endWire z = .inr e) :
      ∃ i, P.diagram.wireAt v i = .inr e := by
    obtain ⟨⟨w, i⟩, hi⟩ := P.diagram.endAt.surjective z
    rw [← hi, P.diagram.station_endAt] at h
    change w = v at h
    subst w
    exact ⟨i, by rw [Diagram.wireAt_eq, hi, hz]⟩
  exact he.elim (fun h => go (.inl (.inr e)) h rfl) (fun h => go (.inr (.inr e)) h rfl)

def earlier (a b : Option Line) : Prop :=
  ∃ i j, a = some i ∧ b = some j ∧ i.1 = j.1 ∧ i.2 < j.2

def StationView.arity (v : StationView F) := wd v.table.1 + wd v.table.2.1

def StationView.ord (v : StationView F) (k i : ℕ) :=
  (univ.filter (fun j : Fin v.arity => earlier (v.line k j.val) (v.line k i))).card

theorem inspect_ord (H : P.LocalRanks) (hr : 0 < r) (v : P.diagram.V) (i : Fin (P.diagram.arity v))
    {e : P.diagram.E} (he : P.diagram.wireAt v i = .inr e) :
    (P.inspect v).ord (P.nodeRank v) i = ordinal P.diagram e := by
  let earlier' (j : Fin (P.diagram.arity v)) :=
    earlier ((P.inspect v).line (P.nodeRank v) j) ((P.inspect v).line (P.nodeRank v) i)
  let before (f : P.diagram.E) := (P.diagram.source f, P.diagram.target f) =
    (P.diagram.source e, P.diagram.target e) ∧ P.diagram.srcOffset f < P.diagram.srcOffset e
  have inside (t : Fin (P.diagram.arity v)) (f : P.diagram.E) (hf : P.diagram.wireAt v t = .inr f) :
      P.atHost (P.grid.cell v) (P.diagram.source f) ∧ P.atHost (P.grid.cell v) (P.diagram.target f) := by
    have h := P.endpoints_atHost hr (P.grid.cell v) (P.packets.bits f).1
      (by simpa [incidentPacket, grid, P.packets.left, P.packets.right] using
        (P.diagram.wireAt_incident v t hf).imp (congrArg P.grid.cell) (congrArg P.grid.cell))
    simpa only [grid, P.packets.left, P.packets.right] using h
  have iff' (j) : earlier' j ↔ ∃ f, P.diagram.wireAt v j = .inr f ∧ before f := by
    unfold earlier'
    rw [inspect_line, inspect_line, he]
    cases hf : P.diagram.wireAt v j with
    | inl _ => simp [earlier]
    | inr f =>
      have h₁ := inside _ _ he
      have h₂ := inside _ _ hf
      have hk : (P.wireKey f).1 = (P.wireKey e).1 ↔
          (P.diagram.source f, P.diagram.target f) = (P.diagram.source e, P.diagram.target e) := by
        constructor
        · intro h
          exact Prod.ext (H.node h₂.1 h₁.1 (congrArg Prod.fst h)) (H.node h₂.2 h₁.2 (congrArg Prod.snd h))
        · exact fun h => congrArg (Prod.map P.nodeRank P.nodeRank) h
      simp [earlier, before, hk]
      intro _ _; rfl
  change (univ.filter earlier').card = (univ.filter before).card
  let f (j) (h : j ∈ univ.filter earlier') := ((iff' j).mp (mem_filter.mp h).2).choose
  have spec j h : P.diagram.wireAt v j = .inr (f j h) ∧ before (f j h) :=
    ((iff' j).mp (mem_filter.mp h).2).choose_spec
  refine card_bij f (fun j h => mem_filter.mpr ⟨mem_univ _, (spec j h).2⟩) ?_ ?_
  · intro a ha b hb h
    apply P.diagram.wireAt_inj P.loopless
    rw [(spec a ha).1, (spec b hb).1, h]
  · intro z hz
    have h := (mem_filter.mp hz).2
    obtain ⟨j, hj⟩ := P.has_slot v z (by
      obtain ⟨a, b⟩ := Prod.mk.inj h.1
      rw [a, b]; exact P.diagram.wireAt_incident _ _ he)
    have hm : j ∈ univ.filter earlier' := mem_filter.mpr ⟨mem_univ _, (iff' j).mpr ⟨z, hj, h⟩⟩
    exact ⟨j, hm, Sum.inr.inj ((spec j hm).1.symm.trans hj)⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # An explicit initial record of a planted surface -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Surface Surface.Local Routing.Private
open scoped Classical
variable {F K B A : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m n : ℕ} {W ε : ℝ} (P : Input F x y h D T (d * b) g W) (p : P.Kits K m n ε)

def reference (name : P.diagram.V → A) :
    Reference P.Occupied P.grid.Seam A P.Occupied P.grid.Seam P.diagram.V (P.Parameters p) :=
  ⟨.refl _, .refl _, name, P.key p, P.external p, fun _ => rfl⟩

variable (ha : ∀ v, (P.grid.uses v).card ≤ n)

def stationLabel (j : P.diagram.V) : Stage.Label F (d * b) d :=
  fun x y _ a _ => pathLabel (P.grid.uses j).card (P.diagram.table j) (P.path ha j) x y a

private theorem stationLabel_spec (c : P.Occupied) (i : Fin (P.grid.stations c).card) :
    Stage.Describes (P.key p) (P.external p) [] (Template.originalAt p P.tag c i)
      (P.stationLabel ha (P.grid.label c i)) [] := by
  let j := P.grid.label c i
  constructor
  · change ∅ = (P.tag (n := n) c (.inl j)).reads
    by_cases hm : P.mobile j <;> simp [tag, hm]
  · intro x a _
    change (P.grid.template K P.weight c).stationWeight x.1 i a =
      pathLabel (P.grid.uses j).card (P.diagram.table j) (P.path ha j)
        (P.external p (P.tag (n := n) c (.inl j)).name x).1
        (P.external p (P.tag (n := n) c (.inl j)).name x).2 a.val
    rw [external_original]
    exact P.pathLabel_eq ha K c i _ _

variable (name : P.diagram.V → A) (code : P.Occupied → B) (s : P.Occupied → Shape n b d)

def initialCopy (c : P.Occupied) (i : Fin (P.grid.stations c).card) : Entry F (d * b) d B A :=
  let j := P.grid.label c i
  let u := Template.originalAt p P.tag c i
  ⟨u.pos, u.a, 0, u.label.role, u.label.name.map name, [], P.stationLabel ha j⟩

def initialAux (c : P.Occupied) (i : Option (Fin n)) : Entry F (d * b) d B A :=
  match i with
  | none => ⟨(p c).pos (.inr none), 0, 0, .collector, none, [code c], auxLabel (p c).program (s c) none⟩
  | some j => ⟨(p c).pos (.inr (some j)), ((s c).1 j).val, ((s c).2 j).val, .residue, none, [code c],
      auxLabel (p c).program (s c) (some j)⟩

def originRecord : Record F (d * b) d P.Occupied P.grid.Seam B A where
  rows c := P.initialAux p code s c none ::
    (List.ofFn (fun i => P.initialAux p code s c (some i)) ++ List.ofFn (P.initialCopy p ha name c))
  ports := (P.plant p s).ports
  level := (P.plant p s).scene.level
  footprint c := {code c}

private theorem rel_ofFn {α β : Type} {R : α → β → Prop} {n : ℕ} {f : Fin n → α} {g : Fin n → β}
    (h : ∀ i, R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  simp only [List.forall₂_iff_get, List.length_ofFn, List.get_ofFn, true_and]
  exact fun i _ _ => h ⟨i, by assumption⟩

theorem matches_origin (β : P.Occupied ⊕ ℕ → B) (hb : ∀ c, β (.inl c) = code c) :
    Matches (P.reference p name).world β (P.plant p s) (P.originRecord p ha name code s) := by
  let R := (P.reference p name).world
  let G := P.originRecord p ha name code s
  refine ⟨fun v => ?_, fun v => ?_, fun _ => rfl, fun v => ?_, fun v j hj => ?_⟩
  · change List.Forall₂ (Represents R β []) ((P.plant p s).scene.cell v).stations (G.rows v)
    rw [plant_stations]
    refine .cons ?_ (List.rel_append (rel_ofFn fun i => ?_) (rel_ofFn fun i => ?_))
    · exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun j hj => by
          change j ∈ {Sum.inl v} at hj; rw [mem_singleton.mp hj]; trivial,
        [.inl v], by simp [hb, initialAux], P.collector_label p s v⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun j hj => by
          change j ∈ {Sum.inl v} at hj; rw [mem_singleton.mp hj]; trivial,
        [.inl v], by simp [hb, initialAux], P.auxiliary_label p s v i⟩
    · have e := P.stationLabel_spec p ha v i
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, [], rfl, e⟩
      · change (P.tag (n := n) v (.inl (P.grid.label v i))).role ≠ .collector →
          (P.tag (n := n) v (.inl (P.grid.label v i))).name = none
        by_cases h : P.mobile (P.grid.label v i) <;> simp [tag, h]
      · intro j hj
        rw [← e.1] at hj
        simp at hj
  · change (P.plant p s).ports v = ((P.plant p s).ports v).map id
    rw [List.map_id]
  · change ({.inl v} : Finset _).image β = {code v}
    rw [image_singleton, hb]
  · change j ∈ {Sum.inl v} at hj
    rw [mem_singleton.mp hj]; trivial

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Recovering packet names and station labels from a local port sequence -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Packing
open scoped Classical
variable {F : Type} {x y : Wire} {h D T r g n : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W)

def StationView.address (s : StationView F) (r k i : ℕ) : Option (ℕ × ℕ) :=
  (s.line k i).map fun p => (rankEdge (p.1, s.ord k i / r), s.ord k i % r)

def StationView.packets (s : StationView F) (r k : ℕ) : Finset ℕ :=
  ((List.finRange s.arity).filterMap fun i => (s.address r k i.val).map Prod.fst).toFinset

def StationView.step (s : StationView F) (r k n i : ℕ) : PathStep n r :=
  ((s.pin i).1, (s.address r k i).bind fun p =>
    let j := ((s.packets r k).sort (· ≤ ·)).idxOf p.1
    if h : j < n ∧ p.2 < r then some (⟨j, h.1⟩, ⟨p.2, h.2⟩) else none)

variable (H : P.LocalRanks) (hr : 0 < r) (v : P.diagram.V)
include H hr

theorem inspect_address (i : Fin (P.diagram.arity v)) :
    (P.inspect v).address r (P.nodeRank v) i =
      (P.diagram.wireAt v i).elim (fun _ => none)
        (fun e => some (P.packetRank (P.packets.bits e).1, (P.packets.bits e).2.val)) := by
  unfold StationView.address
  rw [inspect_line]
  cases he : P.diagram.wireAt v i with
  | inl _ => rfl
  | inr e =>
    simp only [Sum.elim_inr, Option.map_some, P.inspect_ord H hr _ _ he,
      P.packets_numbered.1, P.packetRank_eq hr H.supplied, rankEdge, wireKey]

theorem inspect_packets :
    (P.inspect v).packets r (P.nodeRank v) = (P.grid.uses v).image P.packetRank := by
  ext k
  simp only [StationView.packets, List.mem_toFinset, List.mem_filterMap, List.mem_finRange, true_and, mem_image]
  constructor
  · rintro ⟨i, hi⟩
    change Fin (P.diagram.arity v) at i
    rw [P.inspect_address H hr v i] at hi
    cases he : P.diagram.wireAt v i with
    | inl x => simp [he] at hi
    | inr e =>
      exact ⟨_, P.packet_mem v i he, by simpa [he] using hi⟩
  · rintro ⟨p, hp, rfl⟩
    let e := P.packets.bits.symm (p, ⟨0, hr⟩)
    have he : (P.packets.bits e).1 = p := congrArg Prod.fst (P.packets.bits.apply_symm_apply _)
    obtain ⟨i, hi⟩ := P.has_slot v e (by
      rw [← P.packets.left, ← P.packets.right, he]
      exact (mem_filter.mp hp).2)
    exact ⟨i, by rw [P.inspect_address H hr, hi, Sum.elim_inr, Option.map_some, he]⟩

theorem LocalRanks.uses : Set.InjOn P.packetRank (P.grid.uses v) := by
  apply (H.packet hr (P.grid.cell v)).mono
  intro i hi
  exact ((mem_filter.mp hi).2).imp (congrArg P.grid.cell) (congrArg P.grid.cell)

theorem inspect_step (ha : ∀ v, (P.grid.uses v).card ≤ n) (i : Fin (P.diagram.arity v)) :
    (P.inspect v).step r (P.nodeRank v) n i = P.path ha v i := by
  unfold StationView.step
  simp only [inspect_pin, inspect_address P H hr, inspect_packets P H hr]
  cases he : P.diagram.wireAt v i with
  | inl _ => rw [P.path_exterior _ _ _ he]; rfl
  | inr e =>
    rw [P.path_internal _ _ _ he]
    have key := Grid.number_idxOf (H.uses P hr v) ⟨_, P.packet_mem v i he⟩
    have bound := ((Grid.number P.packetRank (P.grid.uses v)).symm ⟨_, P.packet_mem v i he⟩).isLt
    simp only [Sum.elim_inr, Option.bind_some, ← key, dite_eq_left (And.intro (bound.trans_le (ha v))
      (P.packets.bits e).2.isLt)]
    rfl

omit H hr
variable [Field F]

def StationView.label (s : StationView F) (r t n k : ℕ) : Surface.Stage.Label F r t :=
  fun x y _ a _ => pathLabel (s.packets r k).card s.table (fun i => s.step r k n i.val) x y a

theorem inspect_label {b d : ℕ} (P : Input F x y h D T (d * b) g W)
    (H : P.LocalRanks) (hr : 0 < d * b) (ha : ∀ v, (P.grid.uses v).card ≤ n) (v : P.diagram.V) :
    (P.inspect v).label (d * b) d n (P.nodeRank v) = P.stationLabel ha v := by
  have step : (fun i : Fin (P.diagram.arity v) => (P.inspect v).step (d * b) (P.nodeRank v) n i.val) =
      P.path ha v := funext (P.inspect_step H hr _ ha)
  unfold StationView.label
  rw [P.inspect_packets H hr, card_image_iff.mpr (H.uses P hr v)]
  change (fun x y _ a _ => pathLabel _ (P.diagram.table v)
    (fun i : Fin (P.diagram.arity v) => (P.inspect v).step (d * b) (P.nodeRank v) n i.val) x y a) = _
  rw [step]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Recovering every seam and its ordered packets from a cell's stations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere
open scoped Classical
variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}

structure Seed (F : Type) where
  color : ℕ
  rows : List (ℕ × StationView F)

def Seed.use (s : Seed F) (r : ℕ) (v : ℕ × StationView F) :=
  v.2.packets r (Nat.pair s.color v.1)

def Seed.pool (s : Seed F) (r : ℕ) := s.rows.toFinset.biUnion (s.use r)

def homes (e : ℕ) := (e.unpair.1.unpair.1, e.unpair.2.unpair.1.unpair.1)

def seamKey (e : ℕ) := Nat.pair (homes e).1 (homes e).2

def Seed.seams (s : Seed F) (r : ℕ) :=
  ((s.pool r).filter fun e => (homes e).1 ≠ (homes e).2).image seamKey

def Seed.carry (s : Seed F) (r i : ℕ) := (s.pool r).filter fun e => seamKey e = i

variable (P : Input F x y h D T r g W)

def entry (v : P.diagram.V) := (P.stationRank v, P.inspect v)

def seed (c : P.Occupied) : Seed F :=
  ⟨P.hostRank c.val.1, List.ofFn fun i => P.entry (P.grid.label c i)⟩

theorem seed_rows (c : P.Occupied) : (P.seed c).rows.toFinset = (P.grid.stations c).image P.entry := by
  ext v
  simp only [seed, List.mem_toFinset, List.mem_ofFn, mem_image]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, (Grid.number _ _ i).property, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(Grid.number P.grid.stationRank _).symm ⟨i, hi⟩, by simp [Grid.label]⟩

private theorem carried (e : P.Edges) (j : P.grid.Seam) : e ∈ P.grid.carries j ↔
    P.grid.cell (P.grid.src e) = j.val.1 ∧ P.grid.cell (P.grid.dst e) = j.val.2 := by
  simp [Grid.carries]

private theorem belongs (e : P.grid.Seam) (c : P.Occupied) :
    e ∈ P.grid.ports c ↔ e.val.1 = c ∨ e.val.2 = c := by simp [Grid.ports]

variable (H : P.LocalRanks) (hr : 0 < r) (c : P.Occupied)
include H hr

theorem seed_use (v : P.diagram.V) (hv : P.grid.cell v = c) :
    (P.seed c).use r (P.entry v) = (P.grid.uses v).image P.packetRank := by
  subst c
  exact P.inspect_packets H hr v

theorem seed_pool (e : ℕ) :
    e ∈ (P.seed c).pool r ↔ ∃ i, P.incidentPacket c i ∧ P.packetRank i = e := by
  simp only [Seed.pool, seed_rows, mem_biUnion, mem_image]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, he⟩
    have eq : P.grid.cell v = c := by simpa [Grid.stations] using hv
    rw [P.seed_use H hr c v eq] at he
    obtain ⟨i, hi, rfl⟩ := mem_image.mp he
    refine ⟨i, ?_, rfl⟩
    rcases (mem_filter.mp hi).2 with ht|ht
    · exact .inl ((congrArg P.grid.cell ht).trans eq)
    · exact .inr ((congrArg P.grid.cell ht).trans eq)
  · rintro ⟨i, hi, rfl⟩
    have go (v : P.diagram.V) (hv : P.grid.cell v = c) (ht : i ∈ P.grid.uses v) :
        ∃ z, (∃ j ∈ P.grid.stations c, P.entry j = z) ∧ P.packetRank i ∈ (P.seed c).use r z := by
      refine ⟨P.entry v, ⟨v, by simp [Grid.stations, hv], rfl⟩, ?_⟩
      rw [P.seed_use H hr _ _ hv]; exact mem_image_of_mem _ ht
    exact hi.elim (fun h => go _ h (by simp [Grid.uses])) (fun h => go _ h (by simp [Grid.uses]))

theorem packet_homes (e : P.Edges) : homes (P.packetRank e) =
    (P.grid.cellRank (P.grid.cell (P.grid.src e)), P.grid.cellRank (P.grid.cell (P.grid.dst e))) := by
  simp [homes, packetRank, nodeRank, H.supplied, hr, grid]

private theorem seam_nodes {i j : P.Edges} (hi : P.incidentPacket c i) (hj : P.incidentPacket c j)
    (e : seamKey (P.packetRank i) = seamKey (P.packetRank j)) :
    P.grid.cell (P.grid.src i) = P.grid.cell (P.grid.src j) ∧ P.grid.cell (P.grid.dst i) = P.grid.cell (P.grid.dst j) := by
  simp only [seamKey, P.packet_homes H hr, Nat.pair_eq_pair] at e
  obtain ⟨a, b⟩ := P.endpoints_atHost hr c i hi
  obtain ⟨a', b'⟩ := P.endpoints_atHost hr c j hj
  exact ⟨Subtype.ext (Prod.ext (H.hosts _ a.2 a'.2 e.1) (a.1.trans a'.1.symm)),
    Subtype.ext (Prod.ext (H.hosts _ b.2 b'.2 e.2) (b.1.trans b'.1.symm))⟩

theorem packet_seam {i : P.Edges} {e : P.grid.Seam} (hi : i ∈ P.grid.carries e) :
    seamKey (P.packetRank i) = P.grid.seamRank e := by
  obtain ⟨h₁, h₂⟩ := ((P.carried _ _).mp hi)
  simp only [seamKey, P.packet_homes H hr, h₁, h₂, Grid.seamRank]

theorem seed_seams : (P.seed c).seams r = (P.grid.ports c).image P.grid.seamRank := by
  ext i
  simp only [Seed.seams, mem_image, mem_filter, seed_pool P H hr c]
  constructor
  · rintro ⟨_, ⟨⟨e, he, rfl⟩, ne⟩, rfl⟩
    rw [P.packet_homes H hr] at ne
    let v := P.grid.cell (P.grid.src e)
    let w := P.grid.cell (P.grid.dst e)
    let j : P.grid.Seam := ⟨(v, w), fun eq => ne (congrArg P.grid.cellRank eq), e, rfl, rfl⟩
    exact ⟨j, (P.belongs _ _).mpr he, (P.packet_seam H hr ((P.carried _ _).mpr ⟨rfl, rfl⟩)).symm⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨j, hj, hj'⟩ := e.property.2
    have use : P.incidentPacket c j := by
      unfold incidentPacket; rw [hj, hj']; exact (P.belongs _ _).mp he
    refine ⟨_, ⟨⟨j, use, rfl⟩, ?_⟩, P.packet_seam H hr ((P.carried _ _).mpr ⟨hj, hj'⟩)⟩
    obtain ⟨a, b⟩ := P.endpoints_atHost hr c j use
    rw [P.packet_homes H hr]
    intro eq
    apply e.property.1
    rw [← hj, ← hj']
    exact Subtype.ext (Prod.ext (H.hosts _ a.2 b.2 eq) (a.1.trans b.1.symm))

theorem seed_carry (e : P.grid.Seam) (he : e ∈ P.grid.ports c) :
    (P.seed c).carry r (P.grid.seamRank e) = (P.grid.carries e).image P.packetRank := by
  have hit (i : P.Edges) (hi : i ∈ P.grid.carries e) : P.incidentPacket c i := by
    unfold incidentPacket
    rw [((P.carried _ _).mp hi).1, ((P.carried _ _).mp hi).2]
    exact (P.belongs _ _).mp he
  ext x
  simp only [Seed.carry, mem_filter, seed_pool P H hr c, mem_image]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, h⟩
    obtain ⟨j, hj, hj'⟩ := e.property.2
    have hm : j ∈ P.grid.carries e := (P.carried _ _).mpr ⟨hj, hj'⟩
    obtain ⟨a, b⟩ := P.seam_nodes H hr c hi (hit j hm) (h.trans (P.packet_seam H hr hm).symm)
    exact ⟨i, (P.carried _ _).mpr ⟨a.trans hj, b.trans hj'⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hit i hi, rfl⟩, P.packet_seam H hr hi⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Canonical station order from an unordered set of local records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Sphere Finset
open scoped Classical
variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}

def arrange (color : ℕ) (rows : Finset (ℕ × StationView F)) : Seed F :=
  ⟨color, List.ofFn fun i => (Grid.number Prod.fst rows i).val⟩

theorem seed_arrange (P : Input F x y h D T r g W) (H : P.LocalRanks) (c : P.Occupied) :
    P.seed c = arrange (P.hostRank c.val.1) ((P.grid.stations c).image P.entry) := by
  let A := (P.grid.stations c).image P.entry
  let f := Grid.number Prod.fst A
  have inj : Set.InjOn Prod.fst (↑A : Set (ℕ × StationView F)) := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
    exact congrArg P.entry (H.station c hi hj e)
  have h₁ : (P.seed c).rows.Pairwise (fun x y => x.1 < y.1) := by
    apply List.pairwise_ofFn.mpr
    exact fun _ _ h => (Grid.number_lt (H.station c) _ _).mpr h
  have h₂ : (List.ofFn fun i => (f i).val).Pairwise (fun x y => x.1 < y.1) :=
    List.pairwise_ofFn.mpr fun _ _ h => (Grid.number_lt inj _ _).mpr h
  have eqn : (P.seed c).rows = List.ofFn (fun i => (f i).val) := by
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ h k => (h.asymm k).elim) h₁ h₂
    apply (List.perm_ext_iff_of_nodup h₁.nodup h₂.nodup).mpr
    intro x
    rw [← List.mem_toFinset, seed_rows, List.mem_ofFn]
    exact ⟨fun h => ⟨f.symm ⟨x, h⟩, by simp⟩, by rintro ⟨i, rfl⟩; exact (f i).property⟩
  exact congrArg (Seed.mk _) eqn

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Deterministic recovery of the one-species wiring pattern -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Finset Sphere SphereScale
open scoped Classical
variable {F K : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}

def Seed.ordered (s : Seed F) (r : ℕ) := (s.seams r).sort (· ≤ ·)

def Seed.lists (s : Seed F) (r : ℕ) :=
  s.rows.map (s.use r) ++ (s.ordered r).map (s.carry r)

def Seed.names (s : Seed F) (r i : ℕ) := ((s.lists r).getD i ∅).sort (· ≤ ·)

def Seed.agree (s : Seed F) (r : ℕ) {k : ℕ} (w : Fin k → ℕ) (f : Plant.Bits w) : Prop :=
  ∀ i j (u : Fin (w i)) (v : Fin (w j)),
    (s.names r i).getD u 0 = (s.names r j).getD v 0 → f i u = f j v

variable (P : Input F x y h D T r g W) (H : P.LocalRanks) (hr : 0 < r) (c : P.Occupied)
include H hr

theorem ordered_seams : (P.seed c).ordered r = List.ofFn (fun i => P.grid.seamRank (P.grid.seam c i)) := by
  rw [Seed.ordered, P.seed_seams H hr c, ← Grid.number_keys (H.seam hr c)]
  rfl

private theorem seed_lists : (P.seed c).lists r = List.ofFn (fun i => (P.grid.mark c i).image P.packetRank) := by
  unfold Seed.lists
  rw [P.ordered_seams H hr c]
  simp only [seed, List.map_ofFn, ← List.ofFn_fin_append]
  congr 1
  funext i
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left, Grid.mark_label]
    exact P.seed_use H hr c _ (P.grid.label_cell c i)
  | right i =>
    rw [Fin.append_right, Grid.mark_seam]
    exact P.seed_carry H hr c _ (Grid.number _ _ i).property

theorem seed_names (i : P.grid.Index c) :
    (P.seed c).names r i = List.ofFn (fun j => P.packetRank (Grid.number P.packetRank (P.grid.mark c i) j).val) := by
  rw [Seed.names, P.seed_lists H hr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.getD_some]
  exact (Grid.number_keys (H.mark hr c i)).symm

theorem seed_width (i : P.grid.Index c) :
    ((P.seed c).names r i).length = P.grid.width c i := by
  rw [P.seed_names H hr, List.length_ofFn]; rfl

theorem seed_agree (f : Plant.Bits (P.grid.width c)) :
    P.grid.Agree c f ↔ (P.seed c).agree r (P.grid.width c) f := by
  let n (i : P.grid.Index c) := Grid.number P.grid.packetRank (P.grid.mark c i)
  have key (i : P.grid.Index c) (u : Fin (P.grid.width c i)) :
      ((P.seed c).names r i).getD u 0 = P.grid.packetRank (n i u).val := by
    have he : u.val < (P.grid.mark c i).card := u.isLt
    rw [P.seed_names H hr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left he, Option.getD_some]
    rfl
  have read (i : P.grid.Index c) (u : Fin (P.grid.width c i)) :
      Grid.read P.grid.packetRank (P.grid.mark c i) (f i) (n i u).val = f i u := by
    unfold Grid.read
    erw [dite_eq_left (n i u).property]
    exact congrArg (f i) ((n i).symm_apply_apply u)
  constructor
  · intro h i j u v e
    rw [key, key] at e
    have eq : (n i u).val = (n j v).val := H.packet hr c
      (P.grid.touches c i (n i u).property) (P.grid.touches c j (n j v).property) e
    rw [← read i u, ← read j v, ← eq]
    exact h _ _ _ (n i u).property (eq.symm ▸ (n j v).property)
  · intro h i j e he hf
    simp only [Grid.read, dite_eq_left he, dite_eq_left hf]
    apply h
    erw [key, key]
    simp [n]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Choosing a planting program from local data -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g ℓ n m : ℕ} {W : ℝ}

structure Seed.Identifies (s : Seed F) (r : ℕ) (p : Pattern K D g n) : Prop where
  stations : p.1.val = s.rows.length
  ports : p.2.1.val = (s.ordered r).length
  width : ∀ i, (p.2.2.1.val i).val = (s.names r i.val).length
  rule : ∀ x, p.2.2.2 x = if s.agree r _ x then 1 else 0

omit [Field F] [Algebra K F] in
theorem Seed.Identifies.unique {s : Seed F} {r : ℕ} {p q : Pattern K D g n}
    (a : s.Identifies r p) (c : s.Identifies r q) : p = q := by
  obtain ⟨i, j, u, f⟩ := p
  obtain ⟨k, l, v, h⟩ := q
  have e : i = k := Fin.ext (a.stations.trans c.stations.symm)
  subst k
  have e : j = l := Fin.ext (a.ports.trans c.ports.symm)
  subst l
  have e : u = v := Subtype.ext (funext fun i => Fin.ext ((a.width i).trans (c.width i).symm))
  subst v
  have e : f = h := funext fun x => (a.rule x).trans (c.rule x).symm
  rw [e]

variable (P : Input F x y h D T (d * b) g W) (sc : Scales g ℓ D T m b d)

def planAt (K : Type) [Field K] (c : P.Occupied) : Pattern K D g (probes ℓ D) :=
  pattern (P.grid.template K P.weight c) (P.probe_width sc c)
    (P.stations_bound c) (P.ports_bound sc.Rpos c)

omit [Field F] [Algebra K F] in
theorem seed_identifies (hc : P.LocalRanks) (c : P.Occupied) :
    (P.seed c).Identifies (d * b) (P.planAt sc K c) := by
  refine ⟨?_, ?_, fun i => (P.seed_width hc sc.Rpos c i).symm, ?_⟩
  · exact List.length_ofFn.symm
  · rw [P.ordered_seams hc sc.Rpos, List.length_ofFn]; rfl
  · intro f
    change (if P.grid.Agree c f then (1 : K) else 0) = _
    simp only [P.seed_agree hc sc.Rpos c f]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end
