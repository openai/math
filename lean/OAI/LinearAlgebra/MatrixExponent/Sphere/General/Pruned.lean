import OAI.LinearAlgebra.MatrixExponent.Diagram.Normalize
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Spans
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad

/-! # Endpoints retained by loop removal -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

abbrev LocalLoop (v : G.V) := {e : G.E // G.source e = v ∧ G.target e = v}

variable [Field F]

def embedEnd : G.removeLoops.End ↪ G.End :=
  let c : G.removeLoops.E ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  ((Function.Embedding.refl (slots a)).sumMap c).sumMap ((Function.Embedding.refl (slots b)).sumMap c)

theorem station_embedEnd (p : G.removeLoops.End) :
    G.station (G.embedEnd p) = G.removeLoops.station p := by
  rcases p with (p|p)|(p|p) <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# The local order of a station's ports

Each side begins with its exterior bits. Named internal bundles follow
in the chosen order, with ascending offsets inside each bundle.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Transcript Finset

abbrev View := List Bool × List (List Bool)
abbrev Recipe (F : Type) := View → View → F

structure Panel where
  ext : ℕ
  count : ℕ
  width : Fin count → ℕ

namespace Panel
variable (P : Panel)

def size := ∑ i, P.width i
abbrev Inner := Σ i, Fin (P.width i)
abbrev Port := Fin P.ext ⊕ P.Inner

def wire := Wire.pair (word P.ext) (word P.size)

theorem wd_wire : wd P.wire = P.ext + P.size := by simp [wire, wd, wd_word]

private def bitOrder (n : ℕ) := (positions (word n)).trans (finCongr (wd_word n))

private def serial : Fin P.size ≃ P.Inner :=
  (Fintype.orderIsoFinOfCardEq (Lex P.Inner) (by simp [size, Inner])).toEquiv.trans ofLex

def port : slots P.wire ≃ P.Port :=
  (bitOrder P.ext).sumCongr ((bitOrder P.size).trans P.serial)

def number (i : P.Port) := ((positions P.wire) (P.port.symm i)).val

def block : P.Port → ℕ := Sum.elim (fun _ => 0) (fun i => i.1.val + 1)

theorem block_le (i : P.Port) : P.block i ≤ P.count := by
  cases i with
  | inl _ => exact Nat.zero_le _
  | inr i => exact i.1.isLt

private theorem bitOrder_val (n : ℕ) (i : Fin n) :
    ((positions (word n)) ((bitOrder n).symm i)).val = i.val := by
  simp [bitOrder]

theorem number_ext (i : Fin P.ext) : P.number (.inl i) = i.val := by
  change ((positions (word P.ext)) ((bitOrder P.ext).symm i)).val = _
  exact bitOrder_val _ _

theorem number_inner (i : P.Inner) :
    P.number (.inr i) = P.ext + Processor.start P.width i.1 + i.2.val := by
  change wd (word P.ext) + ((positions (word P.size)) ((bitOrder P.size).symm (P.serial.symm i))).val = _
  rw [wd_word, bitOrder_val, Nat.add_assoc]
  congr 1
  exact Processor.serial_rank _ _ (toLex i)

theorem monotone (i j : P.Port) (h : P.number i ≤ P.number j) : P.block i ≤ P.block j := by
  cases i with
  | inl _ => exact Nat.zero_le _
  | inr i =>
    rw [number_inner] at h
    cases j with
    | inl j => rw [number_ext] at h; have := j.isLt; omega
    | inr j =>
      rw [number_inner] at h
      change i.1.val + 1 ≤ j.1.val + 1
      by_contra! he
      have hj : j.1 < i.1 := Fin.lt_def.mpr (by omega)
      have hh := Processor.start_left P.width _ _ hj
      have := j.2.isLt
      omega

def view (x : Val P.wire) : View :=
  (List.ofFn fun i => bits P.wire x (P.port.symm (.inl i)),
    List.ofFn fun j : Fin P.count => List.ofFn fun i => bits P.wire x (P.port.symm (.inr ⟨j, i⟩)))

def table {F : Type} (Q : Panel) (f : Recipe F) : Table F :=
  ⟨P.wire, Q.wire, fun x y => f (P.view x) (Q.view y)⟩

end Panel
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-! Incidence bijections with independently prescribed local orders. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Transcript Finset Classical

variable {X V E : Type} {f : X → V}

structure Enum (f : X → V) where
  count : V → ℕ
  elem : ∀ v, Fin (count v) ≃ {x // f x = v}

namespace Enum
def any [Fintype X] (f : X → V) : Enum f :=
  ⟨fun v => Fintype.card {x // f x = v}, fun _ => (Fintype.equivFin _).symm⟩

variable (B : Enum f)

def full : (Σ v, Fin (B.count v)) ≃ X :=
  (Equiv.sigmaCongrRight B.elem).trans (Equiv.sigmaFiberEquiv f)

abbrev get (v : V) (i : Fin (B.count v)) := B.full ⟨v, i⟩

def index (x : X) := (B.elem (f x)).symm ⟨x, rfl⟩

theorem owner (v : V) (i : Fin (B.count v)) : f (B.get v i) = v := (B.elem v i).property

@[simp] theorem get_index (x : X) : B.get (f x) (B.index x) = x :=
  congrArg Subtype.val ((B.elem (f x)).apply_symm_apply ⟨x, rfl⟩)

theorem count_eq [Fintype X] (v : V) : B.count v = Fintype.card {x // f x = v} :=
  (Fintype.card_fin _).symm.trans (Fintype.card_congr (B.elem v))

end Enum

structure Side (f : X → V) (g : E → V) where
  ext : Enum f
  inner : Enum g

namespace Side

variable {g : E → V} (S : Side f g) (w : E → ℕ)

abbrev panel (v : V) : Panel :=
  ⟨S.ext.count v, S.inner.count v, fun j => w (S.inner.get v j)⟩

abbrev Bit := Σ e, Fin (w e)

def ports : (Σ v, slots (S.panel w v).wire) ≃ X ⊕ Bit w :=
  (Equiv.sigmaCongrRight fun v => (S.panel w v).port).trans <|
    (Equiv.sigmaSumDistrib _ _).trans <|
      S.ext.full.sumCongr ((Equiv.sigmaAssoc fun v j => Fin (w (S.inner.get v j))).symm.trans
        (Equiv.sigmaCongrLeft (β := fun e => Fin (w e)) S.inner.full))

theorem ports_ext (v : V) (i : Fin (S.ext.count v)) :
    S.ports w ⟨v, (S.panel w v).port.symm (.inl i)⟩ = .inl (S.ext.get v i) := by
  simp [ports, Enum.get, Equiv.sigmaAssoc]

theorem ports_inner (v : V) (i : Fin (S.inner.count v)) (k : Fin (w (S.inner.get v i))) :
    S.ports w ⟨v, (S.panel w v).port.symm (.inr ⟨i, k⟩)⟩ = .inr ⟨S.inner.get v i, k⟩ := by
  simp [ports, Enum.get, Equiv.sigmaAssoc]

theorem owner (i : X ⊕ Bit w) :
    ((S.ports w).symm i).1 = Sum.elim f (fun e => g e.1) i := by
  obtain ⟨⟨v, k⟩, rfl⟩ := (S.ports w).surjective i
  rw [Equiv.symm_apply_apply]
  obtain ⟨j|⟨j, l⟩, rfl⟩ := (S.panel w v).port.symm.surjective k
  · rw [S.ports_ext w v j]; exact (S.ext.owner _ _).symm
  · rw [S.ports_inner w v j l]; exact (S.inner.owner _ _).symm

def peer (i : Bit w) : V × ℕ :=
  let s := (S.ports w).symm (.inr i)
  (s.1, (positions (S.panel w s.1).wire s.2).val)

theorem peer_offset (e : E) : ∃ n : ℕ, ∀ k, S.peer w ⟨e, k⟩ = (g e, n + k.val) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := S.inner.full.surjective e
  refine ⟨S.ext.count v + Processor.start (S.panel w v).width i, fun k => ?_⟩
  change S.peer w ⟨S.inner.get v i, k⟩ = (g (S.inner.get v i), _)
  unfold peer
  rw [← ports_inner, Equiv.symm_apply_apply, S.inner.owner]
  exact congrArg (fun n => (v, n)) ((S.panel w v).number_inner ⟨i, k⟩)

def view (v : V) (x : X → Bool) (y : Bit w → Bool) : View :=
  (List.ofFn (fun i => x (S.ext.get v i)),
    List.ofFn (fun i => List.ofFn (fun k => y ⟨S.inner.get v i, k⟩)))

theorem read (v : V) (x : X → Bool) (z : Bit w → Bool) :
    (S.panel w v).view ((bits (S.panel w v).wire).symm (fun i => Sum.elim x z (S.ports w ⟨v, i⟩))) =
      S.view w v x z := by
  simp only [Panel.view, Equiv.apply_symm_apply, view]
  refine Prod.ext (congrArg List.ofFn (funext fun i => ?_))
    (congrArg List.ofFn (funext fun i => congrArg List.ofFn (funext fun j => ?_)))
  · rw [S.ports_ext w v i]; rfl
  · rw [S.ports_inner w v i j]; rfl

theorem wd_panel [Fintype X] [Fintype E] (v : V) :
    wd (S.panel w v).wire = Fintype.card {x // f x = v} + ∑ e, if g e = v then w e else 0 := by
  rw [Panel.wd_wire]
  change S.ext.count v + (∑ i, w (S.inner.get v i)) = _
  rw [S.ext.count_eq, ← sum_filter, sum_subtype _ (by simp : ∀ e, e ∈ univ.filter (fun e => g e = v) ↔ g e = v) w]
  exact congrArg _ ((S.inner.elem v).sum_comp (fun j => w j.val))

end Side
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# Ordered bundles presented to local concentration

The table label includes any local permutation of its arguments.
The decoder reads only this label, the lengths and directions of
the bundles, and their bits in order. It never reads a remote
vertex name or an exterior wire name.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Restore Restore.Chain.Frame
open scoped Classical

abbrev BundleReader (F : Type) (a e : ℕ) :=
  B a → (B e → ℕ) → (B e → Bool) → (B e → ℕ → Bool) → F

variable {F : Type} {x y : Wire} (G : Diagram F x y) {a e : ℕ} (read : BundleReader F a e)

structure BundleOrder where
  label : G.V → B a
  width : G.V × B e → ℕ
  dir : G.V × B e → Bool
  place : G.End ≃ Σ j, Fin (width j)
  station : ∀ i, (place i).1.1 = G.station i
  direction : ∀ i, dir (place i).1 = i.isRight
  paired : ∀ i j, (place i).1 = (place j).1 →
    (opposite G i).map (fun t => (place t).1) = (opposite G j).map (fun t => (place t).1)
  aligned : ∀ i, (place (tip G i false)).2.val = (place (tip G i true)).2.val
  sample : ∀ v z, read (label v) (fun j => width (v, j)) (fun j => dir (v, j)) z =
    Transcript.sample (G.table v) (fun i =>
      let t := place (G.portEquiv ⟨v, i⟩)
      z t.1.2 t.2.val)

namespace BundleOrder
variable {G read} (o : BundleOrder G read)

def lane (i : G.End) := (o.place i).1.2
def offset (i : G.End) := (o.place i).2.val

theorem position (i : G.End) : (o.place i).1 = (G.station i, o.lane i) := Prod.ext (o.station i) rfl

theorem fills {s : G.V × B e} {n : ℕ} (hn : n < o.width s) :
    ∃ i, (o.place i).1 = s ∧ o.offset i = n := by
  obtain ⟨i, hi⟩ := o.place.surjective ⟨s, ⟨n, hn⟩⟩
  exact ⟨i, by rw [hi], by rw [offset, hi]⟩

theorem size (v : G.V) (s : B e) : o.width (v, s) ≤ G.arity v := by
  let take (t : Fin (o.width (v, s))) : {i // G.station i = v} :=
    ⟨o.place.symm ⟨(v, s), t⟩, by rw [← o.station, Equiv.apply_symm_apply]⟩
  have inj : Function.Injective take := fun _ _ h =>
    eq_of_heq (Sigma.mk.inj (o.place.symm.injective (congrArg Subtype.val h))).2
  simpa only [Fintype.card_fin, G.degree] using Fintype.card_le_of_injective take inj

def peer (s : G.V × B e) :=
  if h : 0 < o.width s then
    (opposite G (o.place.symm ⟨s, ⟨0, h⟩⟩)).map (fun t => (o.place t).1)
  else none

theorem peer_at (i : G.End) :
    o.peer (o.place i).1 = (opposite G i).map (fun t => (o.place t).1) := by
  rw [peer, dite_eq_left (o.place i).2.pos]
  exact o.paired _ _ (by rw [Equiv.apply_symm_apply])

theorem peer_edge (i : G.E) (b : Bool) :
    o.peer (o.place (tip G i b)).1 = some (o.place (tip G i (!b))).1 := by
  rw [peer_at, opposite_tip]; rfl

theorem width_le {s t : G.V × B e} (h : o.peer s = some t) : o.width s ≤ o.width t := by
  by_contra! hn
  obtain ⟨i, hs, hi⟩ := o.fills hn
  rw [← hs, peer_at] at h
  rcases either i with ⟨j, rfl⟩|⟨j, b, rfl⟩
  · cases j <;> cases h
  rw [opposite_tip, Option.map_some, Option.some.injEq] at h
  have hh : o.offset (tip G j b) = o.offset (tip G j (!b)) := by
    cases b <;> first | exact o.aligned _ | exact (o.aligned _).symm
  have ht := (o.place (tip G j (!b))).2.isLt
  exact (Nat.lt_irrefl _ ((hi.symm.trans hh).trans_lt (ht.trans_eq (congrArg o.width h))))

theorem peer_source {s t : G.V × B e} (h : o.peer s = some t) :
    ∃ i b, (o.place (tip G i b)).1 = s ∧ (o.place (tip G i (!b))).1 = t := by
  have hw : 0 < o.width s := by by_contra he; simp [peer, he] at h
  obtain ⟨i, rfl, _⟩ := o.fills hw
  rcases either i with ⟨j, rfl⟩|⟨j, b, rfl⟩
  · rw [peer_at] at h
    cases j <;> cases h
  exact ⟨j, b, rfl, Option.some.inj ((o.peer_edge j b).symm.trans h)⟩

end BundleOrder
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Identifying entire bundles that close at their own station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder
open Coloring Restore Restore.Chain.Frame
open scoped Classical
variable {F : Type} {x y : Wire} {G : Diagram F x y} {a e : ℕ}
    {read : BundleReader F a e} (o : BundleOrder G read)

def turn (v : G.V) (j : B e) : Option (B e) :=
  (o.peer (v, j)).bind fun t => if t.1 = v then some t.2 else none

theorem turn_tip (i : G.E) (b : Bool) :
    o.turn (G.station (tip G i b)) (o.lane (tip G i b)) =
      if G.source i = G.target i then some (o.lane (tip G i (!b))) else none := by
  rw [turn, ← o.position, o.peer_edge, Option.bind_some, o.position]
  cases b <;> simp [station_tip, endpoint, eq_comm]

theorem turn_outer (i : slots x ⊕ slots y) :
    o.turn (G.station (boundaryEnd G i)) (o.lane (boundaryEnd G i)) = none := by
  rw [turn, ← o.position, o.peer_at]
  cases i <;> rfl

theorem loop_tip {v : G.V} (i : G.LocalLoop v) (b : Bool) :
    G.station (tip G i.val b) = v := by
  rw [station_tip, endpoint, i.property.1, i.property.2]
  cases b <;> rfl

theorem loop_turn {v : G.V} (i : G.LocalLoop v) (b : Bool) :
    o.turn v (o.lane (tip G i.val b)) = some (o.lane (tip G i.val (!b))) := by
  simpa only [loop_tip, i.property.1, i.property.2, ite_true] using o.turn_tip i.val b

theorem loop_side {v : G.V} (i : G.LocalLoop v) (b : Bool) :
    o.dir (v, o.lane (tip G i.val b)) = b := by
  simpa only [o.position, loop_tip, side_tip] using o.direction (tip G i.val b)

theorem retain [Field F] (i : G.End) : o.turn (G.station i) (o.lane i) = none ↔ i ∈ Set.range G.embedEnd := by
  constructor
  · intro hi
    rcases either i with ⟨j, rfl⟩|⟨j, b, rfl⟩
    · exact ⟨boundaryEnd G.removeLoops j, by cases j <;> rfl⟩
    · have hj : G.source j ≠ G.target j := by
        intro h
        rw [turn_tip, ite_eq_left h] at hi
        contradiction
      exact ⟨tip G.removeLoops ⟨j, hj⟩ b, by cases b <;> rfl⟩
  · rintro ⟨j, rfl⟩
    rcases either j with ⟨k, rfl⟩|⟨k, b, rfl⟩
    · rw [show G.embedEnd (boundaryEnd G.removeLoops k) = boundaryEnd G k by cases k <;> rfl,
        turn_outer]
    · rw [show G.embedEnd (tip G.removeLoops k b) = tip G k.val b by cases b <;> rfl, turn_tip,
        ite_eq_right k.property]

end OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder
end

/-! # A source-side bit for every local self-loop -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder

open Coloring Restore Restore.Chain.Frame
open scoped Classical

variable {F : Type} {x y : Wire} {G : Diagram F x y} {a e : ℕ}
    {read : BundleReader F a e} (o : BundleOrder G read)

abbrev Closed (width : B e → ℕ) (dir : B e → Bool) (turn : B e → Option (B e)) :=
  {j : Σ i, Fin (width i) // dir j.1 = false ∧ turn j.1 ≠ none}

abbrev loops (v : G.V) :=
  Closed (fun j => o.width (v, j)) (fun j => o.dir (v, j)) (o.turn v)

private def sourceBit (v : G.V) (i : G.LocalLoop v) : o.loops v :=
  let t := tip G i.val false
  ⟨⟨o.lane t, ⟨o.offset t, by
    have h := (o.place t).2.isLt
    change o.offset t < o.width (o.place t).1 at h
    simpa only [o.position, t, loop_tip] using h⟩⟩,
    o.loop_side i false, by simp [t, o.loop_turn]⟩

private theorem sourceBit_bijective (v : G.V) : Function.Bijective (o.sourceBit v) := by
  constructor
  · intro i j h
    have hl : o.lane (tip G i.val false) = o.lane (tip G j.val false) :=
      congrArg (fun b => b.val.1) h
    have hn : o.offset (tip G i.val false) = o.offset (tip G j.val false) :=
      congrArg (fun b => b.val.2.val) h
    have hp : (o.place (tip G i.val false)).1 = (o.place (tip G j.val false)).1 := by
      simp only [o.position, loop_tip, hl]
    have he := o.place.injective (Sigma.ext hp ((Fin.heq_ext_iff (congrArg o.width hp)).mpr hn))
    exact Subtype.ext (tip_inj he).1
  · rintro ⟨⟨l, n⟩, hd, ht⟩
    obtain ⟨i, hi, hn⟩ := o.fills n.isLt
    have hv : G.station i = v := (o.station i).symm.trans (congrArg Prod.fst hi)
    have hl : o.lane i = l := congrArg Prod.snd hi
    have hs : i.isRight = false := by rw [← o.direction, hi]; exact hd
    have hc : o.turn (G.station i) (o.lane i) ≠ none := by rw [hv, hl]; exact ht
    rcases either i with ⟨r, rfl⟩|⟨r, b, rfl⟩
    · exact (hc (o.turn_outer r)).elim
    have hb : b = false := (side_tip r b).symm.trans hs
    subst b
    have hr : G.source r = G.target r := by
      by_contra h
      exact hc (by rw [turn_tip, ite_eq_right h])
    let j : G.LocalLoop v := ⟨r, hv, hr.symm.trans hv⟩
    refine ⟨j, Subtype.ext ?_⟩
    exact Sigma.ext hl ((Fin.heq_ext_iff (congrArg (fun t => o.width (v, t)) hl)).mpr hn)

/-- Index each bit summed by loop contraction by its outgoing lane and offset. -/
def loopBits (v : G.V) : G.LocalLoop v ≃ o.loops v :=
  Equiv.ofBijective (o.sourceBit v) (o.sourceBit_bijective v)

theorem loopBits_lane (v : G.V) (i : G.LocalLoop v) :
    (o.loopBits v i).val.1 = o.lane (tip G i.val false) := rfl

theorem loopBits_offset (v : G.V) (i : G.LocalLoop v) :
    (o.loopBits v i).val.2.val = o.offset (tip G i.val false) := rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder
end

/-! # Placement of the wire ends surviving local loop contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder
open Coloring Restore Restore.Chain.Frame

variable {F : Type} {x y : Wire} {G : Diagram F x y} {a e : ℕ}
    {read : BundleReader F a e} (o : BundleOrder G read)

/-- Removing loops either retains an entire bundle or empties it. -/
def keepWidth (p : G.V × B e) := if o.turn p.1 p.2 = none then o.width p else 0

variable [Field F]

private def keepPlace (i : G.removeLoops.End) : Σ p, Fin (o.keepWidth p) :=
  let t := o.place (G.embedEnd i)
  ⟨t.1, ⟨t.2.val, by
    have h : o.turn t.1.1 t.1.2 = none := by
      rw [show t.1.1 = G.station (G.embedEnd i) from o.station _]
      exact (o.retain _).mpr ⟨i, rfl⟩
    rw [keepWidth, ite_eq_left h]
    exact t.2.isLt⟩⟩

private theorem keepPlace_bijective : Function.Bijective o.keepPlace := by
  constructor
  · intro i j he
    have hp := congrArg Sigma.fst he
    change (o.place (G.embedEnd i)).1 = (o.place (G.embedEnd j)).1 at hp
    have hn : (o.place (G.embedEnd i)).2.val = (o.place (G.embedEnd j)).2.val :=
      congrArg (fun t => t.2.val) he
    exact G.embedEnd.injective (o.place.injective
      (Sigma.ext hp ((Fin.heq_ext_iff (congrArg o.width hp)).mpr hn)))
  · rintro ⟨p, n⟩
    have h : o.turn p.1 p.2 = none := by
      by_contra ht
      have := n.pos
      simp [keepWidth, ht] at this
    obtain ⟨i, hi, hn⟩ := o.fills (show n.val < o.width p by simpa [keepWidth, h] using n.isLt)
    have ht : o.turn (G.station i) (o.lane i) = none := by
      rw [← hi, o.position] at h
      exact h
    obtain ⟨j, rfl⟩ := (o.retain i).mp ht
    exact ⟨j, Sigma.ext hi ((Fin.heq_ext_iff (congrArg o.keepWidth hi)).mpr hn)⟩

/-- Surviving ends retain their entire position, including the bit offset. -/
def keep : G.removeLoops.End ≃ Σ p, Fin (o.keepWidth p) :=
  Equiv.ofBijective o.keepPlace o.keepPlace_bijective

theorem keep_pos (i : G.removeLoops.End) : (o.keep i).1 = (o.place (G.embedEnd i)).1 := rfl

theorem keep_offset (i : G.removeLoops.End) :
    (o.keep i).2.val = (o.place (G.embedEnd i)).2.val := rfl

theorem keep_station (i : G.removeLoops.End) : (o.keep i).1.1 = G.removeLoops.station i :=
  (o.station _).trans (G.station_embedEnd i)

theorem keep_direction (i : G.removeLoops.End) : o.dir (o.keep i).1 = i.isRight := by
  rw [keep_pos, o.direction]
  cases i <;> rfl

theorem keep_paired (i j : G.removeLoops.End) (he : (o.keep i).1 = (o.keep j).1) :
    (opposite G.removeLoops i).map (fun t => (o.keep t).1) =
      (opposite G.removeLoops j).map (fun t => (o.keep t).1) := by
  have hm (q : G.removeLoops.End) : (opposite G.removeLoops q).map (fun t => (o.keep t).1) =
      (opposite G (G.embedEnd q)).map (fun t => (o.place t).1) := by
    rcases q with (q|q)|(q|q) <;> rfl
  rw [hm, hm]
  exact o.paired _ _ he

theorem keep_aligned (i : G.removeLoops.E) :
    (o.keep (tip G.removeLoops i false)).2.val = (o.keep (tip G.removeLoops i true)).2.val :=
  o.aligned i.val

end OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder
end

/-! # Local table values after contracting self-loops -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram

open Assembly.Restore
open scoped Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b) [Field F]

private def extendSide {I : Type} (v : G.V) (x : I ⊕ G.removeLoops.E → Bool)
    (z : G.LocalLoop v → Bool) : I ⊕ G.E → Bool
  | .inl i => x (.inl i)
  | .inr e => if h : G.source e ≠ G.target e then x (.inr ⟨e, h⟩)
    else if hv : G.source e = v ∧ G.target e = v then z ⟨e, hv⟩ else false

private theorem weight_remove (v : G.V) (x : slots a ⊕ G.removeLoops.E → Bool)
    (y : slots b ⊕ G.removeLoops.E → Bool) :
    G.removeLoops.weight v x y = ∑ z : G.LocalLoop v → Bool,
      G.weight v (G.extendSide v x z) (G.extendSide v y z) := by
  unfold removeLoops
  rw [weight_ofLocal]
  · rfl
  · intro w x₁ y₁ x₂ y₂ hx hy
    change (∑ z : G.LocalLoop w → Bool, G.weight w (G.extendSide w x₁ z) (G.extendSide w y₁ z)) =
      ∑ z : G.LocalLoop w → Bool, G.weight w (G.extendSide w x₂ z) (G.extendSide w y₂ z)
    apply Finset.sum_congr rfl
    intro z _
    apply G.local_weight
    · rintro (p|e) hp
      · exact hx (.inl p) hp
      · by_cases h : G.source e ≠ G.target e
        · simpa only [extendSide, dite_eq_left h] using hx (.inr ⟨e, h⟩) hp
        · simp only [extendSide, dite_eq_right h]
    · rintro (p|e) hp
      · exact hy (.inl p) hp
      · by_cases h : G.source e ≠ G.target e
        · simpa only [extendSide, dite_eq_left h] using hy (.inr ⟨e, h⟩) hp
        · simp only [extendSide, dite_eq_right h]

/-- Values on ports at other stations are immaterial. The two ends of
each removed loop share one summation bit. -/
theorem loopTable (v : G.V) (x : G.removeLoops.End → Bool)
    (y : (G.LocalLoop v → Bool) → G.End → Bool)
    (retained : ∀ z p, G.removeLoops.station p = v → y z (G.embedEnd p) = x p)
    (removed : ∀ z (e : G.LocalLoop v) d, y z (tip G e.val d) = z e) :
    Transcript.sample (G.removeLoops.table v) (fun p => x (G.removeLoops.portEquiv ⟨v, p⟩)) =
      ∑ z, Transcript.sample (G.table v) (fun p => y z (G.portEquiv ⟨v, p⟩)) := by
  change G.removeLoops.weight v (x ∘ Sum.inl) (x ∘ Sum.inr) =
    ∑ z, G.weight v (y z ∘ Sum.inl) (y z ∘ Sum.inr)
  rw [weight_remove]
  apply Finset.sum_congr rfl
  intro z _
  apply G.local_weight
  · rintro (p|e) hp
    · exact (retained z (.inl (.inl p)) hp).symm
    · by_cases h : G.source e ≠ G.target e
      · rw [extendSide, dite_eq_left h]
        exact (retained z (.inl (.inr ⟨e, h⟩)) hp).symm
      · have hv : G.source e = v ∧ G.target e = v := ⟨hp, (not_ne_iff.mp h).symm.trans hp⟩
        rw [extendSide, dite_eq_right h, dite_eq_left hv]
        exact (removed z ⟨e, hv⟩ false).symm
  · rintro (p|e) hp
    · exact (retained z (.inr (.inl p)) hp).symm
    · by_cases h : G.source e ≠ G.target e
      · rw [extendSide, dite_eq_left h]
        exact (retained z (.inr (.inr ⟨e, h⟩)) hp).symm
      · have hv : G.source e = v ∧ G.target e = v := ⟨(not_ne_iff.mp h).trans hp, hp⟩
        rw [extendSide, dite_eq_right h, dite_eq_left hv]
        exact (removed z ⟨e, hv⟩ true).symm

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-! # Restricting an ordered bundle presentation to positive-arity stations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder

open Coloring Restore Restore.Chain.Frame

variable {F : Type} {x y : Wire} {G : Diagram F x y} {a e : ℕ}
    {read : BundleReader F a e} (o : BundleOrder G read)

private def forget : G.prune.V × B e ↪ G.V × B e :=
  (Function.Embedding.subtype _).prodMap (Function.Embedding.refl _)

/-- An inhabited bundle already has a positive-arity owner. -/
private def prunePosition : (Σ j, Fin (o.width j)) ≃ (Σ j : G.prune.V × B e, Fin (o.width (forget j))) where
  toFun t := ⟨(⟨t.1.1, t.2.pos.trans_le (o.size _ _)⟩, t.1.2), t.2⟩
  invFun t := ⟨forget t.1, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Scalar stations have no wire ends. All remaining labels, lanes and offsets stay fixed. -/
def prune : BundleOrder G.prune read where
  label v := o.label v.val
  width j := o.width (forget j)
  dir j := o.dir (forget j)
  place := o.place.trans o.prunePosition
  station i := by
    apply Subtype.ext
    cases i <;> exact o.station _
  direction i := o.direction i
  paired i j h := by
    apply (Option.map_injective (forget (G := G) (e := e)).injective)
    have he (t : G.End) : opposite G.prune t = opposite G t := by
      rcases t with (t|t)|(t|t) <;> rfl
    rw [Option.map_map, Option.map_map, he, he]
    exact o.paired i j (congrArg forget h)
  aligned i := o.aligned i
  sample v z := by
    refine (o.sample v.val z).trans ?_
    apply congrArg (Transcript.sample (G.table v.val))
    funext i
    cases i <;> rfl

@[simp] theorem prune_label (v : G.prune.V) : o.prune.label v = o.label v.val := rfl

@[simp] theorem prune_width (v : G.prune.V) (j : B e) :
    o.prune.width (v, j) = o.width (v.val, j) := rfl

@[simp] theorem prune_dir (v : G.prune.V) (j : B e) :
    o.prune.dir (v, j) = o.dir (v.val, j) := rfl

@[simp] theorem prune_lane (i : G.End) : o.prune.lane i = o.lane i := rfl

@[simp] theorem prune_offset (i : G.End) : o.prune.offset i = o.offset i := rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.BundleOrder
end
