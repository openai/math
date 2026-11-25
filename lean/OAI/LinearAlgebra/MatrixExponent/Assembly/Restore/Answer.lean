import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Travel
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute

/-!
# Assigning canonical slots and outlets

An arbitrary feasible assignment proves the two capacity bounds.
Renumber using the displayed station slots and neighbor indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Encloses
open Coloring Packing History.Reset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {a b x y : Wire} {u N r s : ℕ}
    {L : Fringe x y T} {D : Template F} {A : Attachment D} {raw : A.format.obj}
    {G : HostNet F L D.scheme.h u} {B' : Border F T a b x y} (q : A.Encloses raw G B')
    (e : G.Restore N r s)

abbrev Members (z : G.V × Cell D.scheme.h) := {t // G.park t = z}

def memberKey (z : G.V × Cell D.scheme.h) : Members z ↪ B A.k where
  toFun t := q.slot t
  inj' i j he := Subtype.ext (q.distinct (i.property.trans j.property.symm) he)

omit [Field F] in
include e in
private theorem members_le (z : G.V × Cell D.scheme.h) : Fintype.card (Members z) ≤ r := by
  let f : Members z → Fin r := fun t => e.slot t.val
  have hf : Function.Injective f := fun i j h =>
    Subtype.ext (e.unique (Prod.ext (i.property.trans j.property.symm) h))
  simpa using Fintype.card_le_of_injective f hf

def number (t : T) : Fin r := rank (q.memberKey (G.park t)) (members_le e _) ⟨t, rfl⟩

theorem number_at (t : T) (z : G.V × Cell D.scheme.h) (h : G.park t = z) :
    q.number e t = rank (q.memberKey z) (members_le e z) ⟨t, h⟩ := by subst z; rfl

abbrev Rack (G : HostNet F L D.scheme.h u) (t : T) :=
  {v // ∃ i, L.tensor i = t ∧ (G.far i).1 = v}

omit [Field F] [Fintype T] in
theorem rack_near {t : T} (v : Rack G t) : v.val ∈ G.N (G.park t).1 := by
  obtain ⟨i, hf, he⟩ := v.property
  rw [← he, ← hf]
  exact G.ns _ _ (G.tether i).2.2

abbrev chart := q.core.fullChart q.full

def rackKey (t : T) : Rack G t ↪ Option (B D.scheme.d) where
  toFun v := q.chart.label (G.park t).1 v.val
  inj' i j h := Subtype.ext (q.chart.inj _ (Finset.mem_insert_of_mem (rack_near i))
    (Finset.mem_insert_of_mem (rack_near j)) h)

omit [Field F] [Fintype T] in
include e in
private theorem rack_le (t : T) : Fintype.card (Rack G t) ≤ s := by
  let f : Rack G t → Fin s := fun v => e.pin v.property.choose
  have hf : Function.Injective f := by
    intro v w h
    have hv := v.property.choose_spec
    have hw := w.property.choose_spec
    have he := (e.outlet _ _ (hv.1.trans hw.1.symm)).mp h
    exact Subtype.ext (hv.2.symm.trans ((congrArg Prod.fst he).trans hw.2))
  simpa using Fintype.card_le_of_injective f hf

def pin (i : slots x ⊕ slots y) : Fin s :=
  rank (q.rackKey (L.tensor i)) (rack_le e _) ⟨(G.far i).1, i, rfl, rfl⟩

theorem pin_at (i : slots x ⊕ slots y) (t : T) (h : L.tensor i = t) :
    q.pin e i = rank (q.rackKey t) (rack_le e _) ⟨(G.far i).1, i, h, rfl⟩ := by subst t; rfl

abbrev canonical : G.Restore N r s where
  degree := e.degree
  slot := q.number e
  unique := by
    intro i j h
    obtain ⟨hv, ht⟩ := Prod.mk.inj h
    rw [number_at q e _ _ hv, number_at q e j _ rfl] at ht
    exact congrArg Subtype.val ((rank (q.memberKey _) _).injective ht)
  pin := q.pin e
  outlet := by
    intro i j h
    rw [pin_at q e _ _ h, pin_at q e j _ rfl, (rank (q.rackKey _) _).injective.eq_iff, Subtype.ext_iff]
    have he : (G.far i).2 = (G.far j).2 :=
      (G.tether i).2.1.trans ((congrArg (fun t => (G.park t).2) h).trans (G.tether j).2.1.symm)
    exact ⟨fun k => Prod.ext k he, congrArg Prod.fst⟩
  pins := Restore.pins q.chart e.degree

include q in
theorem place_inj : Function.Injective G.units.place := by
  intro i j h
  apply Sum.inl.inj (β := T)
  apply q.pres.vertex.injective
  rw [q.internal, q.internal, h]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Encloses
end

/-!
# Template and load codes on a restored board

At a site with ports, round the arity up to the existing positive
floor. This only lowers the charge and makes it computable from the
same record as the tensor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing Finset
open scoped Classical

def amount (u n : ℕ) : ℝ := if n = 0 then 0 else max (n : ℝ) u

theorem amount_ge (u n : ℕ) : (n : ℝ) ≤ amount u n := by
  unfold amount; split <;> simp_all

theorem amount_le (u n : ℕ) {c : ℝ} (hc : (n : ℝ) ≤ c) (hs : c = 0 ∨ (u : ℝ) ≤ c) :
    amount u n ≤ c := by
  by_cases hn : n = 0
  · simpa [amount, hn] using hc
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  exact (ite_eq_right hn).le.trans (max_le hc (hs.resolve_left (ne_of_gt (hp.trans_le hc))))

variable {F : Type} [Field F] (S : Scheme F)

abbrev template (m h u : ℕ) : Template F where
  scheme := Script.scheme S m h
  count := (script S).width
  load j := amount u (∑ s, Script.size ((script S).serial.symm j) s)
  park _ := 0
  past _ := 0
  order := .refl _

variable {S} {T : Type} [Fintype T] {a b x y : Wire} {u N r s m : ℕ}
    {L : Fringe x y T} {D : Template F} {A : Attachment D} {raw : A.format.obj}
    {G : HostNet F L D.scheme.h u} {B' : Border F T a b x y} (q : A.Encloses raw G B')
    (e : G.Restore N r s) (hl : ∀ i, G.src i ≠ G.dst i) (E : Directory e.adj m)

local notation "C" => e.route B' q.tether
local notation "f" => e.frame B' q.tether q.place_inj hl
local notation "U" => template A.scheme m D.scheme.h u

abbrev board : Rounds.Board F a b D.scheme.h where
  V := e.Space
  diagram := (C).graph
  place := Prod.swap
  one := Prod.swap_injective
  adj := e.adj
  sym := Tether.adj_symm e.sw G.C G.cs
  edge := e.route_support B' q.tether
  charge v := amount u ((C).graph.arity v)
  cover _ := amount_ge _ _

def name : Cell D.scheme.h × e.Space ↪ B m × B D.scheme.h × B 0 where
  toFun z := (E.host z.2, cellIndex _ z.1, 0)
  inj' _ _ he := Prod.ext ((cellIndex _).injective (congrArg (fun v => v.2.1) he))
    (E.host.injective (congrArg Prod.fst he))

def dataAt (v : Cell D.scheme.h × e.Space) := (f).encode q.pres (fun i j => E.index i.2 j.2) v

def tape (i : B m) (j : B D.scheme.h) : Script A.scheme :=
  Function.extend (name e E) (dataAt q e hl E) (fun _ => Script.vacant A.scheme) (i, j, 0)

def display : (U).format.obj :=
  let label i j := (script A.scheme).serial (tape q e hl E i j)
  (fun i => (E.nav i, label i), fun i =>
    ((decide (i ∈ Set.range E.host), false), fun j => (E.flags i j, E.flags i j), label i))

theorem tape_at (v : Cell D.scheme.h × e.Space) :
    tape q e hl E (E.host v.2) (cellIndex _ v.1) = dataAt q e hl E v :=
  (name e E).injective.extend_apply _ _ v

theorem show_label (v : (U).scheme.Vtx) :
    (U).scheme.pattern (display q e hl E).1 v = Script.pattern (tape q e hl E v.1 v.2.1) :=
  congrArg (fun i => Script.pattern i) ((script A.scheme).serial.symm_apply_apply _)

def written : Written (f) q.pres (display q e hl E).1 where
  vertex := name e E
  index i j := E.index i.2 j.2
  dir := q.directed
  code v := by
    rw [show_label]
    exact congrArg (fun i => Script.pattern i) (tape_at q e hl E v)
  idle v hv := by
    obtain ⟨i, j, k⟩ := v
    have : k = 0 := Fin.eq_zero k
    subst k
    rw [show_label]
    exact congrArg (fun a => Script.pattern a)
      (Function.extend_apply' (dataAt q e hl E) (fun _ => Script.vacant A.scheme) _ hv)
  nav i b := by
    have hi := e.route_support B' q.tether i
    cases b
    · exact Prod.ext (E.nav_link _ _ hi.2) (Prod.ext (congrArg (cellIndex _) hi.1.symm) rfl)
    · exact Prod.ext (E.nav_link _ _ (Tether.adj_symm _ _ G.cs _ _ hi.2))
        (Prod.ext (congrArg (cellIndex _) hi.1) rfl)

def presents : (U).Presents (display q e hl E) (board (D := D) q e) where
  pres := (written q e hl E).presentation
  host := E.host
  vertex _ := rfl
  directed := (written q e hl E).directed
  live _ := decide_eq_true_iff
  closed := E.closed
  reciprocal := E.reciprocal
  edge := E.marks
  core := E.marks
  load v i := by
    change amount u (∑ j, Script.size ((script A.scheme).serial.symm
      ((script A.scheme).serial (tape q e hl E (E.host v) (cellIndex _ i)))) j) = _
    rw [Equiv.symm_apply_apply, tape_at q e hl E (i, v)]
    have ht {X Y : Type} [Fintype X] (l : X → ℝ) (g : X → Y) (hg : Function.Injective g) (x : X) :
        push g l (g x) = l x := by simp [push, hg.eq_iff]
    have hi := ht (board (D := D) q e).charge (board (D := D) q e).place (board (D := D) q e).one (i, v)
    refine Eq.trans ?_ hi.symm
    let w := written q e hl E
    have hc := Fintype.card_congr (w.seating.pin (i, v))
    simp only [Diagram.Port, Scheme.LocalPin, Fintype.card_sigma, Fintype.card_sum, card_slots, Fintype.card_fin] at hc
    refine congrArg (amount u) (Eq.trans ?_ hc.symm)
    exact sum_congr rfl fun j _ => (w.width _ j).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Data at the end of a wire-saving beat -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {D : Template F}

structure Data (A : Attachment D) (N r s u : ℕ) (a b : Wire) where
  T : Type
  [finite : Fintype T]
  x : Wire
  y : Wire
  L : Fringe x y T
  G : HostNet F L D.scheme.h u
  border : Border F T a b x y
  raw : A.format.obj
  q : A.Encloses raw G border
  allocation : G.Restore N r s
  core : ∀ v, (G.C v).card ≤ 3
  loopless : ∀ i, G.src i ≠ G.dst i

attribute [instance] Data.finite

namespace Data
variable {A : Attachment D} {N r s u : ℕ} {a b : Wire} (X Y : Data A N r s u a b)

abbrev e := X.q.canonical X.allocation
abbrev old := X.border.attach X.G.diagram
abbrev p := X.q.pres
abbrev host := X.q.core.post.host
abbrev route := X.e.route X.border X.q.tether
abbrev f := X.e.frame X.border X.q.tether X.q.place_inj X.loopless
abbrev Space := Cell D.scheme.h × X.e.Space

def location : X.old.V → X.G.V × Cell D.scheme.h := Sum.elim X.G.units.place X.G.park
def seat : X.old.V → B A.k := Sum.elim (fun _ => 0) X.q.slot
def letter (v : X.G.V) (k : Cell D.scheme.h) := X.raw.2 (X.host v) (cellIndex _ k)

theorem vertex (w : X.old.V) : X.p.vertex w =
    (X.host (X.location w).1, cellIndex _ (X.location w).2, X.seat w) := by
  cases w
  · exact (X.q.internal _).trans (Prod.ext rfl (Prod.ext (X.q.core.block _) rfl))
  · exact (X.q.frozen _).trans (Prod.ext rfl (Prod.ext (X.q.core.block _) rfl))

theorem token (w : X.old.V) :
    Chain.Frame.token X.p w = (X.letter (X.location w).1 (X.location w).2, X.seat w) := by
  unfold Chain.Frame.token
  rw [X.vertex]
  rfl

theorem exists_iff (v : X.G.V) (k : Cell D.scheme.h) (j : B A.k) :
    (∃ w, X.location w = (v, k) ∧ X.seat w = j) ↔ A.live (X.letter v k) j = true := by
  have eq := X.q.occupied (X.host v, cellIndex _ k, j)
  change A.live (X.letter v k) j = true ↔ _ at eq
  rw [eq]
  constructor
  · rintro ⟨w, he, hs⟩
    exact ⟨w, by rw [X.vertex, he, hs]⟩
  · rintro ⟨w, hw⟩
    rw [X.vertex] at hw
    obtain ⟨ha, hb⟩ := Prod.mk.inj hw
    exact ⟨w, Prod.ext (X.host.injective ha) ((cellIndex _).injective (Prod.mk.inj hb).1), (Prod.mk.inj hb).2⟩

theorem seat_core (w : X.old.V) : X.seat w = 0 ↔ w.isLeft := by
  cases w
  · exact iff_of_true rfl rfl
  · exact iff_of_false (X.q.positive _) Bool.false_ne_true

theorem map_member {v : X.G.V} {v' : Y.G.V} {k : Cell D.scheme.h}
    (he : X.letter v k = Y.letter v' k) (i : Attachment.Encloses.Members (G := X.G) (v, k)) :
    ∃ j : Attachment.Encloses.Members (G := Y.G) (v', k),
      X.q.memberKey _ i = Y.q.memberKey _ j := by
  have hi := (X.exists_iff v k (X.q.slot i.val)).mp ⟨.inr i.val, i.property, rfl⟩
  rw [he] at hi
  obtain ⟨w, hw, hs⟩ := (Y.exists_iff _ _ _).mpr hi
  cases w with
  | inl w => exact (X.q.positive _ hs.symm).elim
  | inr j => exact ⟨⟨j, hw⟩, hs.symm⟩

theorem number_eq {v : X.G.V} {v' : Y.G.V} {k : Cell D.scheme.h}
    (he : X.letter v k = Y.letter v' k) {i : X.T} {j : Y.T}
    (hi : X.G.park i = (v, k)) (hj : Y.G.park j = (v', k)) (h : X.q.slot i = Y.q.slot j) :
    X.e.slot i = Y.e.slot j := by
  change X.q.number X.allocation i = Y.q.number Y.allocation j
  rw [X.q.number_at X.allocation i _ hi, Y.q.number_at Y.allocation j _ hj]
  exact History.Reset.rank_eq (X.map_member Y he) (Y.map_member X he.symm) h

theorem owner_base (w : X.old.V) : (cells (X.route.owner w).2).1 = (X.location w).1 := by
  cases w <;> rfl

theorem owner_block (w : X.old.V) : (X.route.owner w).1 = (X.location w).2 := by cases w <;> rfl

theorem owner_eq {v : X.G.V} {v' : Y.G.V} {k : Cell D.scheme.h} {w : X.old.V} {w' : Y.old.V}
    (he : X.letter v k = Y.letter v' k) (hw : X.location w = (v, k)) (hw' : Y.location w' = (v', k))
    (h : X.seat w = Y.seat w') : (cells (X.route.owner w).2).2 = (cells (Y.route.owner w').2).2 := by
  rcases w with w|i <;> rcases w' with w'|j
  · rfl
  · exact (Y.q.positive _ h.symm).elim
  · exact (X.q.positive _ h).elim
  · exact congrArg (fun t => (Tether.member ((), t) : Tether.Host Unit r s (Tether.width N r s)))
      (X.number_eq Y he hw hw' h)

end Data
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Matching ports and neighbors from equal short labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)

abbrev tag := Chain.Frame.token X.p
abbrev endAt := endpoint X.old
abbrev plug (e : X.old.E) (b : Bool) := (X.p.wirePin e b).1.2
abbrev base (w : X.old.V) := (X.location w).1
abbrev block (w : X.old.V) := (X.location w).2
abbrev port (q : X.old.End) := (X.p.toSeating.ends q).1.2

theorem span_at (q : X.old.End) :
    (X.p.toSeating.ends q).1 = (X.p.vertex (X.old.station q), X.port q) := by
  obtain ⟨⟨w, i⟩, rfl⟩ := X.old.portEquiv.surjective q
  rw [Scheme.Seating.ends_at, Diagram.station_port]
  unfold port
  rw [Scheme.Seating.ends_at]
  rfl

theorem join (e : X.old.E) (t : Bool) :
    ∃ j, (A.decode (X.tag (X.endAt e t)).1).peer (X.tag (X.endAt e t)).2 (X.plug e t) =
        some (j, X.seat (X.endAt e (!t)), X.plug e (!t)) ∧
      X.q.core.post.nav (X.base (X.endAt e t)) j = X.base (X.endAt e (!t)) ∧
      X.block (X.endAt e t) = X.block (X.endAt e (!t)) := by
  have h := X.p.wirePin_peer e t
  have hs (u : Bool) : (X.p.wirePin e u).1 = (X.p.vertex (X.endAt e u), X.plug e u) :=
    Prod.ext (X.p.wirePin_at _ _) rfl
  rw [hs, hs, Scheme.peer] at h
  change ((A.decode (X.tag (X.endAt e t)).1).peer (X.tag (X.endAt e t)).2 (X.plug e t)).map _ = _ at h
  cases hv : (A.decode (X.tag (X.endAt e t)).1).peer (X.tag (X.endAt e t)).2 (X.plug e t) with
  | none => rw [hv] at h; cases h
  | some z =>
    rw [hv, Option.map_some, Option.some.injEq, X.vertex, X.vertex] at h
    obtain ⟨w, he⟩ := Prod.mk.inj h
    obtain ⟨hn, w⟩ := Prod.mk.inj w
    obtain ⟨hb, ht⟩ := Prod.mk.inj w
    refine ⟨z.1, congrArg some (Prod.ext rfl (Prod.ext ht he)), ?_, (cellIndex _).injective hb⟩
    exact X.host.injective ((X.q.core.host_nav _ _).trans hn)

private theorem incident (w : X.old.V) (j : B A.e)
    (hw : 0 < (A.decode (X.tag w).1).width (X.tag w).2 j) :
    ∃ p, X.old.station p = w ∧ X.port p = j := by
  let k : A.scheme.Pin (A.rows X.raw) := ⟨(X.p.vertex w, j), ⟨0, hw⟩⟩
  obtain ⟨p, hp⟩ := X.p.toSeating.ends.surjective k
  have he := congrArg Sigma.fst hp
  rw [X.span_at] at he
  obtain ⟨hv, hs⟩ := Prod.mk.inj he
  exact ⟨p, X.p.vertex.injective hv, hs⟩

theorem map_port {q : X.old.End} {w : Y.old.V} (he : X.tag (X.old.station q) = Y.tag w) :
    ∃ q' : Y.old.End, Y.old.station q' = w ∧ X.port q = Y.port q' ∧ q.isRight = q'.isRight ∧
      (q ∈ Set.range (boundaryEnd X.old) ↔ q' ∈ Set.range (boundaryEnd Y.old)) := by
  have hw := (X.p.toSeating.ends q).2.pos
  rw [X.span_at] at hw
  change 0 < (A.decode (X.tag (X.old.station q)).1).width (X.tag (X.old.station q)).2 (X.port q) at hw
  rw [he] at hw
  obtain ⟨q', hv, hs⟩ := Y.incident w (X.port q) hw
  subst w
  refine ⟨q', rfl, hs.symm, ?_, ?_⟩
  · rw [← X.q.directed q, ← Y.q.directed q', X.span_at, Y.span_at]
    exact congrArg₂ (fun t j => (A.decode t.1).direction t.2 j) he hs.symm
  · rw [← X.p.no_peer, ← Y.p.no_peer, X.span_at, Y.span_at]
    unfold Scheme.peer
    simp only [Option.map_eq_none_iff]
    exact Iff.of_eq (congrArg₂ (fun (t : B A.ℓ × B A.k) j => (A.decode t.1).peer t.2 j = none) he hs.symm)

theorem map_edge (e : X.old.E) (t : Bool) {w : Y.old.V} (he : X.tag (X.endAt e t) = Y.tag w) :
    ∃ (g : Y.old.E) (j : B D.scheme.d),
      Y.endAt g t = w ∧ X.q.core.post.nav (X.base (X.endAt e t)) j = X.base (X.endAt e (!t)) ∧
      Y.q.core.post.nav (Y.base w) j = Y.base (Y.endAt g (!t)) ∧
      X.seat (X.endAt e (!t)) = Y.seat (Y.endAt g (!t)) ∧ ∀ b, X.plug e b = Y.plug g b := by
  obtain ⟨i, hi, hp, ht, hh⟩ := X.map_port Y (q := tip X.old e t) ((congrArg X.tag (station_tip _ _)).trans he)
  rcases Chain.Frame.either i with ⟨v, hv⟩|⟨g, b, rfl⟩
  · obtain ⟨z, hz⟩ := hh.mpr ⟨v, hv.symm⟩
    cases t <;> cases z <;> cases hz
  rw [side_tip, side_tip] at ht
  subst b
  rw [station_tip] at hi
  subst w
  change X.plug e t = Y.plug g t at hp
  obtain ⟨j, hj, ha, _⟩ := X.join e t
  obtain ⟨k, hk, hb, _⟩ := Y.join g t
  rw [he, hp, hk] at hj
  obtain ⟨rfl, hz⟩ := Prod.mk.inj (Option.some.inj hj)
  obtain ⟨hs, hl⟩ := Prod.mk.inj hz.symm
  exact ⟨g, k, rfl, ha, hb, hs, fun b => by cases t <;> cases b <;> assumption⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # Computing tether outlet numbers from displayed neighbors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)

abbrev nav := X.q.core.post.nav
abbrev Edge := slots X.x ⊕ slots X.y

theorem near_side (i : X.Edge) :
    X.endAt (.inr i) i.isRight = .inl (portEnd X.G.diagram i) := by cases i <;> rfl

theorem far_side (i : X.Edge) :
    X.endAt (.inr i) (!i.isRight) = .inr (X.L.tensor i) := by rw [X.q.tether]; cases i <;> rfl

theorem frozen_end (e : X.old.E) (t : Bool) (v : X.T) (h : X.endAt e t = .inr v) :
    ∃ i, e = .inr i ∧ t = !i.isRight ∧ X.L.tensor i = v := by
  rw [X.q.tether]
  rcases e with e|i|j <;> cases t <;>
    first | exact ⟨_, rfl, rfl, Sum.inr.inj h⟩ | exact (Sum.inl_ne_inr h).elim

def SameLabels (v : X.G.V) (w : Y.G.V) :=
  ∀ j, X.q.chart.label v (X.nav v j) = Y.q.chart.label w (Y.nav w j)

theorem SameLabels.symm {v : X.G.V} {w : Y.G.V} (h : X.SameLabels Y v w) :
    Y.SameLabels X w v := fun j => (h j).symm

theorem rack_map {t : X.T} {t' : Y.T} (ht : X.tag (.inr t) = Y.tag (.inr t'))
    (h : X.SameLabels Y (X.G.park t).1 (Y.G.park t').1)
    (v : Attachment.Encloses.Rack X.G t) :
    ∃ w : Attachment.Encloses.Rack Y.G t', X.q.rackKey t v = Y.q.rackKey t' w := by
  obtain ⟨i, hi, he⟩ := v.property
  have hp : X.endAt (.inr i) (!i.isRight) = .inr t := (X.far_side i).trans (congrArg Sum.inr hi)
  obtain ⟨g, j, hg, ha, hb, _⟩ := X.map_edge Y (.inr i) (!i.isRight) ((congrArg X.tag hp).trans ht)
  obtain ⟨q, rfl, hs, hv⟩ := Y.frozen_end g _ _ hg
  rw [hp, Bool.not_not, X.near_side] at ha
  rw [hs, Bool.not_not, Y.near_side] at hb
  refine ⟨⟨(Y.G.far q).1, q, hv, rfl⟩, ?_⟩
  change X.nav (X.G.park t).1 j = (X.G.far i).1 at ha
  change Y.nav (Y.G.park t').1 j = (Y.G.far q).1 at hb
  exact (congrArg _ (ha.trans he).symm).trans ((h j).trans (congrArg _ hb))

theorem outlet_eq (i : X.Edge) (j : Y.Edge)
    (hh : X.tag (.inr (X.L.tensor i)) = Y.tag (.inr (Y.L.tensor j)))
    (hl : X.SameLabels Y (X.G.park (X.L.tensor i)).1 (Y.G.park (Y.L.tensor j)).1)
    (he : X.q.chart.label (X.G.park (X.L.tensor i)).1 (X.G.far i).1 =
      Y.q.chart.label (Y.G.park (Y.L.tensor j)).1 (Y.G.far j).1) :
    X.e.pin i = Y.e.pin j := by
  change X.q.pin X.allocation i = Y.q.pin Y.allocation j
  unfold Attachment.Encloses.pin
  exact History.Reset.rank_eq (X.rack_map Y hh hl) (Y.rack_map X hh.symm (SameLabels.symm _ _ hl)) he

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # The parent of each site of a directed path -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring Chain.Frame
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X : Data A N r s u a b)
local notation "W" => Tether.width N r s
local notation "H" => X.route.graph

abbrev part (v : X.Space) := (cells v.2).2
abbrev home (v : X.Space) := (cells v.2).1

def which (e : X.old.E) (k : ℕ) :=
  match e with
  | .inl _ => decide (k ≠ 0)
  | .inr i =>
    if (if i.isRight then Tether.Plan.length W s - k else k) ≤ Nat.clog 2 W + 1 then i.isRight else !i.isRight

theorem node_home (e : X.old.E) (k : ℕ) : X.home (X.route.node e k) = X.base (X.endAt e (X.which e k)) := by
  rcases e with e|i
  · change X.home (if k = 0 then _ else _) = X.base (X.endAt _ (decide (k ≠ 0)))
    by_cases h : k = 0
    · rw [ite_eq_left h, decide_eq_false (not_not.mpr h)]; rfl
    · rw [ite_eq_right h, decide_eq_true h]; rfl
  · change (cells (X.e.travel i k).2).1 = _
    rw [travel_base, which]
    by_cases h : (if i.isRight then Tether.Plan.length W s - k else k) ≤ Nat.clog 2 W + 1
    · rw [ite_eq_left h, ite_eq_left h, X.near_side]; rfl
    · rw [ite_eq_right h, ite_eq_right h, X.far_side]; rfl

theorem node_block (e : X.old.E) (k : ℕ) (z : Bool) :
    (X.route.node e k).1 = X.block (X.endAt e z) := by
  obtain ⟨_, _, _, hg⟩ := X.join e false
  have eq : X.block (X.endAt e false) = X.block (X.endAt e true) := hg
  have hb (t : Bool) : X.block (X.endAt e t) = X.block (X.endAt e z) := by
    cases z <;> cases t <;> first | rfl | exact eq | exact eq.symm
  rcases e with e|i
  · change (if k = 0 then (X.e.oldCore e).1 else (X.e.oldCore e).2).1 = _
    split <;> first | exact hb false | exact hb true
  · refine Eq.trans ?_ (hb i.isRight)
    rw [X.near_side]
    change (X.e.travel i k).1 = (X.G.far i).2
    unfold HostNet.Restore.travel Tether.Plan.walk
    split_ifs <;> rfl

theorem distinct (e : X.old.E) : Function.Injective (fun z => X.base (X.endAt e z)) := by
  have hn : X.base (X.endAt e false) ≠ X.base (X.endAt e true) := by
    rcases e with e|q
    · change (X.G.units.place (X.G.diagram.source e)).1 ≠ (X.G.units.place (X.G.diagram.target e)).1
      rw [X.G.units.left, X.G.units.right]
      exact X.loopless _
    · have hc : X.base (X.endAt (.inr q) q.isRight) ≠ X.base (X.endAt (.inr q) (!q.isRight)) := by
        rw [X.near_side, X.far_side]
        intro hh
        exact (X.G.tether q).1 ((congrArg X.G.frozen hh).mpr (X.G.kept _))
      cases q <;> first | exact hc | exact hc.symm
  intro t z h
  cases t <;> cases z <;> first | rfl | exact (hn h).elim | exact (hn h.symm).elim

theorem root_home (z : X.Space) : X.home (X.f.root z) = X.home z := by
  rcases z with ⟨k, (w|⟨⟨w, t⟩, p⟩)|⟨w|⟨⟨w, t⟩, p⟩, j⟩⟩ <;> rfl

theorem leg_eq (i : X.route.Edge) (b : Bool) : X.f.leg i b = X.which i.1 (point i b) := by
  apply X.distinct
  have h := congrArg X.home (X.f.anchor (tip H i b))
  rw [X.root_home, station_tip, endpoint_node, ref_tip, station_tip] at h
  exact ((X.owner_base _).symm.trans h.symm).trans (X.node_home i.1 _)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # Matching a path between two local computations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)

structure Link (e : X.old.E) (g : Y.old.E) : Prop where
  tags : ∀ z, X.tag (X.endAt e z) = Y.tag (Y.endAt g z)
  group : ∀ z, X.block (X.endAt e z) = Y.block (Y.endAt g z)
  port : ∀ z, X.plug e z = Y.plug g z
  labels : ∀ z, X.SameLabels Y (X.base (X.endAt e z)) (Y.base (Y.endAt g z))
  paired : ∀ z, LocalPair X.q.chart Y.q.chart (X.base (X.endAt e z)) (X.base (X.endAt e (!z)))
    (Y.base (Y.endAt g z)) (Y.base (Y.endAt g (!z)))

theorem seat_tag (w : X.old.V) : X.seat w = (X.tag w).2 := (congrArg Prod.snd (X.token w)).symm

variable {X Y} {e : X.old.E} {g : Y.old.E}

theorem Link.kind (h : X.Link Y e g) (z : Bool) : (X.endAt e z).isLeft = (Y.endAt g z).isLeft := by
  have ht : X.seat (X.endAt e z) = Y.seat (Y.endAt g z) := by rw [X.seat_tag, Y.seat_tag, h.tags]
  have hh : (X.endAt e z).isLeft = true ↔ (Y.endAt g z).isLeft = true := by
    rw [← X.seat_core, ← Y.seat_core, ht]
  exact Bool.eq_iff_iff.mpr hh

theorem Link.cases (h : X.Link Y e g) :
    (∃ i j, e = .inl i ∧ g = .inl j) ∨ (∃ i j, e = .inr i ∧ g = .inr j ∧ i.isRight = j.isRight) := by
  have ha := h.kind false
  have hb := h.kind true
  rcases e with e|i|j <;> rcases g with e'|i'|j' <;>
    first | exact .inl ⟨_, _, rfl, rfl⟩ | exact .inr ⟨_, _, rfl, rfl, rfl⟩ | cases ha <;> cases hb

theorem Link.turns (h : X.Link Y e g) : X.route.turns e = Y.route.turns g := by
  rcases h.cases with ⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl, eq⟩ <;> rfl

theorem Link.which (h : X.Link Y e g) (k : ℕ) : X.which e k = Y.which g k := by
  rcases h.cases with ⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl, eq⟩
  · rfl
  · simp only [Data.which, eq]

theorem Link.part (h : X.Link Y e g) (k : ℕ) : X.part (X.route.node e k) = Y.part (Y.route.node g k) := by
  rcases h.cases with ⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl, dir⟩
  · change X.part (if k = 0 then _ else _) = Y.part (if k = 0 then _ else _)
    split_ifs <;> rfl
  · have ht := h.tags (!i.isRight)
    have hg := h.group (!i.isRight)
    have ha := h.labels (!i.isRight)
    have hf := h.paired i.isRight
    have hb := h.paired (!i.isRight)
    rw [Bool.not_not] at hb
    rw [X.near_side, X.far_side, dir, Y.near_side, Y.far_side] at hf hb
    rw [X.far_side, dir, Y.far_side] at ht hg ha
    have hp := X.outlet_eq Y i j ht ha hb.label
    have eq : X.e.slot (X.L.tensor i) = Y.e.slot (Y.L.tensor j) := by
      simp only [Data.tag, X.token, Y.token] at ht
      obtain ⟨hc, hs⟩ := Prod.mk.inj ht
      change (X.G.park (X.L.tensor i)).2 = (Y.G.park (Y.L.tensor j)).2 at hg
      change X.letter _ (X.G.park (X.L.tensor i)).2 = Y.letter _ (Y.G.park (Y.L.tensor j)).2 at hc
      rw [← hg] at hc
      exact X.number_eq Y hc rfl (Prod.ext rfl hg.symm) hs
    exact travel_suffix X.e Y.e X.q.chart Y.q.chart rfl rfl i j hf hb eq hp dir k

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # A local view sufficient for restoration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)

structure View (v : X.G.V) (w : Y.G.V) (k : Cell D.scheme.h) where
  sees : X.G.V → Y.G.V → Prop
  self : sees v w
  nav : ∀ j, sees (X.nav v j) (Y.nav w j)
  letter : ∀ x y, sees x y → X.letter x k = Y.letter y k
  labels : ∀ x y, sees x y → X.SameLabels Y x y
  pair : ∀ x y t l, sees x y → sees t l → LocalPair X.q.chart Y.q.chart x t y l

namespace View
variable {X Y} {v : X.G.V} {w : Y.G.V} {k : Cell D.scheme.h} (h : X.View Y v w k)

def symm : Y.View X w v k where
  sees x y := h.sees y x
  self := h.self
  nav := h.nav
  letter _ _ he := (h.letter _ _ he).symm
  labels _ _ he := SameLabels.symm _ _ (h.labels _ _ he)
  pair _ _ _ _ he ht :=
    let t := h.pair _ _ _ _ he ht
    ⟨t.same.symm, t.full.symm, t.label.symm, t.back, t.forth⟩

def sites (x : X.Space) (y : Y.Space) : Prop :=
  x.1 = k ∧ y.1 = k ∧ h.sees (X.home x) (Y.home y) ∧ X.part x = Y.part y

theorem sites_unique {x : X.Space} {y z : Y.Space} (ha : h.sites x y) (hb : h.sites x z) : y = z :=
  Prod.ext (ha.2.1.trans hb.2.1.symm)
    (cells.injective (Prod.ext ((h.pair _ _ _ _ ha.2.2.1 hb.2.2.1).same.mp rfl)
      (ha.2.2.2.symm.trans hb.2.2.2)))

def related (x : X.old.V) (y : Y.old.V) : Prop :=
  X.block x = k ∧ Y.block y = k ∧ h.sees (X.base x) (Y.base y) ∧ X.seat x = Y.seat y

theorem tags {x : X.old.V} {y : Y.old.V} (he : h.related x y) : X.tag x = Y.tag y := by
  simp only [Data.tag, X.token, Y.token]
  change (X.letter (X.base x) (X.block x), _) = (Y.letter (Y.base y) (Y.block y), _)
  rw [he.1, he.2.1, h.letter _ _ he.2.2.1, he.2.2.2]

theorem owners {x : X.old.V} {y : Y.old.V} (he : h.related x y) :
    h.sites (X.route.owner x) (Y.route.owner y) := by
  refine ⟨(X.owner_block _).trans he.1, (Y.owner_block _).trans he.2.1, ?_, ?_⟩
  · change h.sees (cells _).1 (cells _).1
    rw [X.owner_base, Y.owner_base]; exact he.2.2.1
  · exact X.owner_eq Y (h.letter _ _ he.2.2.1) (Prod.ext rfl he.1) (Prod.ext rfl he.2.1) he.2.2.2

theorem vertex {x : X.old.V} (hv : X.base x = v) (hk : X.block x = k) :
    ∃ y : Y.old.V, Y.base y = w ∧ h.related x y := by
  have hh := (X.exists_iff v k (X.seat x)).mp ⟨x, Prod.ext hv hk, rfl⟩
  rw [h.letter _ _ h.self] at hh
  obtain ⟨y, hy, hs⟩ := (Y.exists_iff w k _).mpr hh
  have hy₁ : Y.base y = w := congrArg Prod.fst hy
  exact ⟨y, hy₁, hk, congrArg Prod.snd hy, by rw [hv, hy₁]; exact h.self, hs.symm⟩

theorem link (e : X.old.E) (t : Bool) (hv : X.base (X.endAt e t) = v) (hk : X.block (X.endAt e t) = k) :
    ∃ g : Y.old.E, X.Link Y e g ∧ ∀ b, h.related (X.endAt e b) (Y.endAt g b) := by
  obtain ⟨y, hy, hh⟩ := h.vertex hv hk
  obtain ⟨g, j, hg, hx, hy', hs, hp⟩ := X.map_edge Y e t (h.tags hh)
  subst y
  have ht : h.related (X.endAt e (!t)) (Y.endAt g (!t)) := by
    obtain ⟨_, _, _, hx'⟩ := X.join e t
    obtain ⟨_, _, _, hz⟩ := Y.join g t
    refine ⟨hx'.symm.trans hh.1, hz.symm.trans hh.2.1, ?_, hs⟩
    rw [← hx, ← hy', hv, hy]
    exact h.nav j
  have hr (b : Bool) : h.related (X.endAt e b) (Y.endAt g b) := by cases t <;> cases b <;> assumption
  exact ⟨g, ⟨fun z => h.tags (hr z), fun z => (hr z).1.trans (hr z).2.1.symm, hp,
    fun z => h.labels _ _ (hr z).2.2.1, fun z => h.pair _ _ _ _ (hr z).2.2.1 (hr (!z)).2.2.1⟩, hr⟩

theorem node {e : X.old.E} {g : Y.old.E} (l : X.Link Y e g)
    (hr : ∀ b, h.related (X.endAt e b) (Y.endAt g b)) (i : ℕ) :
    h.sites (X.route.node e i) (Y.route.node g i) := by
  refine ⟨(X.node_block e i false).trans (hr false).1, (Y.node_block g i false).trans (hr false).2.1, ?_, l.part _⟩
  rw [X.node_home, Y.node_home, l.which]
  exact (hr _).2.2.1

end View
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # Comparing the original stations and visible relays of two boards -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring Chain.Frame
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} {X Y : Data A N r s u a b}
  {v : X.G.V} {w : Y.G.V} {k : Cell D.scheme.h}
  {x : X.Space} {y : Y.Space}
local notation "W" => Tether.width N r s

private def trunk (x : Tether.Host Unit r s W) : Tether.Host Unit r s W :=
  (Detour.owner x).elim Tether.core (fun p => Tether.member p.1)

private theorem root_part (x : X.Space) : X.part (X.f.root x) = trunk (X.part x) := by
  rcases x with ⟨i, (v|⟨⟨v, t⟩, p⟩)|⟨v|⟨⟨v, t⟩, p⟩, j⟩⟩ <;> rfl

namespace View
variable (h : X.View Y v w k)

theorem flip (hs : h.sites x y) : h.symm.sites y x :=
  ⟨hs.2.1, hs.1, hs.2.2.1, hs.2.2.2.symm⟩

theorem homes (hs : h.sites x y) : X.home x = v ↔ Y.home y = w :=
  (h.pair _ _ _ _ hs.2.2.1 h.self).same

theorem roots (hs : h.sites x y) : h.sites (X.f.root x) (Y.f.root y) := by
  refine ⟨hs.1, hs.2.1, ?_, ?_⟩
  · rw [root_home, root_home]; exact hs.2.2.1
  · rw [root_part, root_part, hs.2.2.2]

theorem member (hs : h.sites x y) (hv : X.home x = v) {i : X.old.V} (he : X.route.owner i = x) :
    ∃ j, Y.route.owner j = y ∧ X.tag i = Y.tag j := by
  have hg : X.base i = v := (X.owner_base i).symm.trans ((congrArg X.home he).trans hv)
  have hk : X.block i = k := (X.owner_block i).symm.trans ((congrArg Prod.fst he).trans hs.1)
  obtain ⟨j, _, hj⟩ := h.vertex hg hk
  exact ⟨j, h.sites_unique (he ▸ h.owners hj) hs, h.tags hj⟩

theorem occupies (hs : h.sites x y) (hv : X.home x = v) :
    x ∈ Set.range X.route.owner ↔ y ∈ Set.range Y.route.owner := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj, _⟩ := h.member hs hv hi
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi, _⟩ := h.symm.member (h.flip hs) ((h.homes hs).mp hv) hj
    exact ⟨i, hi⟩

theorem initial (hs : h.sites x y) (hv : X.home x = v) :
    Function.extend X.route.owner X.tag (fun _ => (0, 0)) (X.f.root x) =
    Function.extend Y.route.owner Y.tag (fun _ => (0, 0)) (Y.f.root y) := by
  have eq := h.roots hs
  have hr := (X.root_home x).trans hv
  by_cases he : X.f.root x ∈ Set.range X.route.owner
  · obtain ⟨i, hi⟩ := he
    obtain ⟨j, hj, hp⟩ := h.member eq hr hi
    rw [← hi, ← hj, X.f.one.extend_apply, Y.f.one.extend_apply, hp]
  · rw [Function.extend_apply' _ _ _ he, Function.extend_apply' _ _ _ (mt (h.occupies eq hr).mpr he)]

theorem segment (i : X.route.Edge) (b : Bool) (hv : X.home (endpoint X.route.graph i b) = v)
    (hk : (endpoint X.route.graph i b).1 = k) :
    ∃ j : Y.route.Edge, ∀ t,
      h.sites (endpoint X.route.graph i t) (endpoint Y.route.graph j t) ∧
      X.f.lane X.p (tip X.route.graph i t) = Y.f.lane Y.p (tip Y.route.graph j t) := by
  have ha := X.node_home i.1 (point i b)
  have hb := X.node_block i.1 (point i b) (X.which i.1 (point i b))
  rw [endpoint_node] at hv hk
  obtain ⟨g, hg, hr⟩ := h.link i.1 _ (ha.symm.trans hv) (hb.symm.trans hk)
  let j : Y.route.Edge := ⟨g, i.2.cast (congrArg (· + 1) hg.turns)⟩
  refine ⟨j, fun t => ?_⟩
  have ht : point i t = point j t := rfl
  have hl : X.f.leg i t = Y.f.leg j t := by rw [X.leg_eq, Y.leg_eq, ← ht, hg.which]
  constructor
  · rw [endpoint_node, endpoint_node, ← ht]
    exact h.node hg hr _
  · rw [lane, lane, old_tip, old_tip, side_tip, side_tip, hl]
    exact congrArg (fun q => Chain.Frame.pair A.e (t, q)) (hg.port _)

theorem exterior (i : slots a ⊕ slots b) (hs : h.sites x y) (hv : X.home x = v)
    (hi : X.route.graph.station (boundaryEnd X.route.graph i) = x) :
    ∃ j, Y.route.graph.station (boundaryEnd Y.route.graph j) = y ∧
      X.f.lane X.p (boundaryEnd X.route.graph i) = Y.f.lane Y.p (boundaryEnd Y.route.graph j) := by
  have hx : X.route.owner (X.old.station (boundaryEnd X.old i)) = x := by cases i <;> exact hi
  obtain ⟨z, hz, ht⟩ := h.member hs hv hx
  obtain ⟨_, he, ha, hb, hm⟩ := X.map_port Y ht
  obtain ⟨j, rfl⟩ := hm.mp ⟨i, rfl⟩
  refine ⟨j, ?_, ?_⟩
  · have he := (congrArg Y.route.owner he).trans hz
    cases j <;> exact he
  · rw [lane, lane, old_boundary, old_boundary]
    apply congrArg (Chain.Frame.pair A.e)
    exact Prod.ext (by cases i <;> cases j <;> exact hb) ha

end View
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # Independence of a restored record from remote names -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data.View
open Packing Coloring Chain.Frame
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} {X Y : Data A N r s u a b}
  {v : X.G.V} {w : Y.G.V} {k : Cell D.scheme.h}
  {x : X.Space} {y : Y.Space} (h : X.View Y v w k)
  (l : X.Space → X.Space → B 3) (t : Y.Space → Y.Space → B 3)

def Aligned (x : X.Space) (y : Y.Space) : Prop :=
  ∀ z z', h.sites z z' → z.2 ∈ X.e.adj x.2 → z'.2 ∈ Y.e.adj y.2 → l x z = t y z'

theorem reverse (a : h.Aligned l t x y) : h.symm.Aligned t l y x :=
  fun z z' hs ha hb => (a z' z (h.symm.flip hs) hb ha).symm

private theorem adjacent (i : X.route.Edge) (b : Bool) :
    (endpoint X.route.graph i (!b)).2 ∈ X.e.adj (endpoint X.route.graph i b).2 := by
  have he := (X.e.route_support X.border X.q.tether i).2
  cases b
  · exact he
  · exact Tether.adj_symm _ _ X.G.cs _ _ he

theorem reply (hs : h.sites x y) (hv : X.home x = v) (ha : h.Aligned l t x y)
    (q : X.route.graph.End) (hq : X.route.graph.station q = x) :
    X.f.entry X.p l x (X.f.lane X.p q) = Y.f.entry Y.p t y (X.f.lane X.p q) := by
  rcases either q with ⟨i, rfl⟩|⟨e, b, rfl⟩
  · obtain ⟨j, hj, he⟩ := h.exterior i hs hv hq
    rw [← hq, X.f.entry_eq X.p l X.q.directed, he, ← hj, Y.f.entry_eq Y.p t Y.q.directed]
    cases i <;> cases j <;> rfl
  · have hx := (station_tip e b).symm.trans hq
    obtain ⟨g, hg⟩ := h.segment e b ((congrArg X.home hx).trans hv) ((congrArg Prod.fst hx).trans hs.1)
    have hy := h.sites_unique (hx ▸ (hg b).1) hs
    have ht := ha _ _ (hg (!b)).1 (hx ▸ adjacent e b) (hy ▸ adjacent g b)
    rw [← hq, X.f.entry_eq X.p l X.q.directed, (hg b).2, ← (station_tip (G := Y.route.graph) g b).trans hy,
      Y.f.entry_eq Y.p t Y.q.directed, opposite_tip, opposite_tip]
    change (true, true, l _ (X.route.graph.station (tip X.route.graph e (!b))), _) =
      (true, true, t _ (Y.route.graph.station (tip Y.route.graph g (!b))), _)
    simp only [station_tip, hx, hy, ht, (hg (!b)).2]

theorem answer (hs : h.sites x y) (hv : X.home x = v) (ha : h.Aligned l t x y) :
    X.f.encode X.p l x = Y.f.encode Y.p t y := by
  apply Prod.ext
  · exact decide_eq_decide.mpr (h.occupies hs hv)
  refine Prod.ext (h.initial hs hv) ?_
  funext j
  change X.f.entry X.p l x j = Y.f.entry Y.p t y j
  by_cases a : ∃ q, X.f.mark X.p q = (x, j)
  · obtain ⟨q, hq⟩ := a
    obtain ⟨hx, rfl⟩ := Prod.mk.inj hq
    exact h.reply l t hs hv ha q hx
  by_cases b : ∃ q, Y.f.mark Y.p q = (y, j)
  · obtain ⟨q, hq⟩ := b
    obtain ⟨hy, rfl⟩ := Prod.mk.inj hq
    exact (h.symm.reply t l (h.flip hs) ((h.homes hs).mp hv) (h.reverse l t ha) q hy).symm
  rw [entry, entry, dite_eq_right a, dite_eq_right b]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data.View
end
