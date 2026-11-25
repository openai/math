import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Rounds.Costs

/-!
# Replacing directed wires by chains of equality tests

An old table and arbitrarily many equality tests may occupy a
station simultaneously. Testing consecutive bits on every chain
gives exactly one extension of each original assignment.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Finset
open scoped Classical

variable {F : Type} {x y : Wire} (G : Diagram F x y) (V : Type)

structure Chain where
  owner : G.V → V
  turns : G.E → ℕ
  node : G.E → ℕ → V
  start : ∀ e, node e 0 = owner (G.source e)
  finish : ∀ e, node e (turns e + 1) = owner (G.target e)

namespace Chain
variable {G V} (C : Chain G V)

abbrev Edge := Σ e, Fin (C.turns e + 1)
abbrev Turn := Σ e, Fin (C.turns e)

def before (t : C.Turn) : C.Edge := ⟨t.1, t.2.castSucc⟩
def after (t : C.Turn) : C.Edge := ⟨t.1, t.2.succ⟩
def joint (t : C.Turn) := C.node t.1 (t.2.val + 1)
def first (e : G.E) : C.Edge := ⟨e, 0⟩
def last (e : G.E) : C.Edge := ⟨e, Fin.last _⟩

def src : slots x ⊕ C.Edge → V
  | .inl i => C.owner (G.src.symm (.inl i)).1
  | .inr e => C.node e.1 e.2.val

def dst : slots y ⊕ C.Edge → V
  | .inl i => C.owner (G.dst.symm (.inl i)).1
  | .inr e => C.node e.1 (e.2.val + 1)

def left (p : slots x ⊕ G.E) := p.map id C.first
def right (p : slots y ⊕ G.E) := p.map id C.last

theorem src_left (p : slots x ⊕ G.E) : C.src (C.left p) = C.owner (G.src.symm p).1 := by
  cases p <;> first | rfl | exact C.start _

theorem dst_right (p : slots y ⊕ G.E) : C.dst (C.right p) = C.owner (G.dst.symm p).1 := by
  cases p <;> first | rfl | exact C.finish _

variable [Field F]

def factor (v : V) (a : slots x ⊕ C.Edge → Bool) (b : slots y ⊕ C.Edge → Bool) :=
  (∏ w : {w // C.owner w = v}, G.weight w (a ∘ C.left) (b ∘ C.right)) *
  (∏ t : {t // C.joint t = v}, if b (.inr (C.before t)) = a (.inr (C.after t)) then (1 : F) else 0)

theorem local_factor : Diagram.Local C.src C.dst C.factor := by
  intro v a b a' b' ha hb
  unfold factor
  refine congrArg₂ (· * ·) (prod_congr rfl fun w _ => ?_) (prod_congr rfl fun t _ => ?_)
  · exact G.local_weight _ _ _ _ _
      (fun p hp => ha _ ((C.src_left p).trans ((congrArg C.owner hp).trans w.property)))
      (fun p hp => hb _ ((C.dst_right p).trans ((congrArg C.owner hp).trans w.property)))
  · rw [hb (.inr (C.before t)) t.property, ha (.inr (C.after t)) t.property]

variable [Fintype V]
abbrev graph := Diagram.ofLocal C.src C.dst C.factor

def original : G.End → C.graph.End := Sum.map C.left C.right

theorem station_original (i : G.End) : C.graph.station (C.original i) = C.owner (G.station i) := by
  cases i <;> first | exact C.src_left _ | exact C.dst_right _

private def consistent (z : C.Edge → Bool) := ∀ t, z (C.before t) = z (C.after t)

omit [Fintype V] [Field F] in
private theorem constant (z : C.Edge → Bool) (hz : C.consistent z) (e : C.Edge) :
    z e = z (C.first e.1) := by
  obtain ⟨e, k⟩ := e
  induction k using Fin.induction with
  | zero => rfl
  | succ i hi => exact (hz ⟨e, i⟩).symm.trans hi

private def repeatBits : (G.E → Bool) ≃ {z : C.Edge → Bool // C.consistent z} where
  toFun z := ⟨fun e => z e.1, fun _ => rfl⟩
  invFun z := z.val ∘ C.first
  left_inv _ := rfl
  right_inv z := Subtype.ext (funext fun e => (C.constant z.val z.property e).symm)

private theorem product (a : Val x) (b : Val y) (z : C.Edge → Bool) :
    (∏ v, C.graph.vertex a b z v) =
      if C.consistent z then ∏ v, G.vertex a b (z ∘ C.first) v else 0 := by
  have he (v : V) : C.graph.vertex a b z v =
      C.factor v (Sum.elim (bits x a) z) (Sum.elim (bits y b) z) :=
    Diagram.vertex_ofLocal _ _ _ C.local_factor a b z v
  simp only [he, factor, prod_mul_distrib]
  change (_ * ∏ v, ∏ t : {t // C.joint t = v}, if z (C.before t) = z (C.after t) then (1 : F) else 0) = _
  rw [Fintype.prod_fiberwise C.owner (fun v => G.weight v _ _),
    Fintype.prod_fiberwise C.joint (fun t => if z (C.before t) = z (C.after t) then (1 : F) else 0)]
  by_cases h : C.consistent z
  · rw [ite_eq_left h]
    have hl : Sum.elim (bits x a) z ∘ C.left = Sum.elim (bits x a) (z ∘ C.first) := by
      funext p; cases p <;> rfl
    have hr : Sum.elim (bits y b) z ∘ C.right = Sum.elim (bits y b) (z ∘ C.first) := by
      funext p; cases p with
      | inl _ => rfl
      | inr e => exact C.constant z h (C.last e)
    simp only [show ∀ t, z (C.before t) = z (C.after t) from h, ite_true, prod_const_one, mul_one, hl, hr]
    rfl
  · rw [ite_eq_right h]
    obtain ⟨t, ht⟩ := not_forall.mp h
    rw [prod_eq_zero (mem_univ t) (ite_eq_right ht), mul_zero]

theorem eval : C.graph.eval = G.eval := by
  let : DecidableEq C.Edge := Classical.typeDecidableEq _
  funext a b
  unfold Diagram.eval
  simp only [C.product]
  rw [← sum_filter]
  refine (sum_subtype (p := C.consistent) (F := inferInstance) _ mem_filter_univ (fun z => ∏ v, G.vertex a b (z ∘ C.first) v)).trans ?_
  exact (Fintype.sum_equiv C.repeatBits _ _ (fun _ => rfl)).symm

end Chain
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Original and relay ports on a network of chains -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]

def tip (G : Diagram F x y) (e : G.E) (b : Bool) : G.End :=
  cond b (.inr (.inr e)) (.inl (.inr e))

def endpoint (G : Diagram F x y) (e : G.E) (b : Bool) := cond b (G.target e) (G.source e)

omit [Field F] in
theorem station_tip (e : G.E) (b : Bool) : G.station (tip G e b) = endpoint G e b := by cases b <;> rfl

omit [Field F] in
theorem side_tip (e : G.E) (b : Bool) : (tip G e b).isRight = b := by cases b <;> rfl

omit [Field F] in
theorem tip_inj {e e' : G.E} {b b' : Bool} (h : tip G e b = tip G e' b') : e = e' ∧ b = b' := by
  cases b <;> cases b' <;> cases h <;> exact ⟨rfl, rfl⟩

namespace Chain
variable (C : Chain G V)
local notation "H" => C.graph

def relay (t : C.Turn) (b : Bool) : (H).End :=
  cond b (.inr (.inr (C.before t))) (.inl (.inr (C.after t)))

theorem station_relay (t : C.Turn) (b : Bool) : (H).station (C.relay t b) = C.joint t := by
  cases b <;> rfl

theorem side_relay (t : C.Turn) (b : Bool) : (C.relay t b).isRight = b := by cases b <;> rfl

theorem side_original (e : G.End) : (C.original e).isRight = e.isRight := by cases e <;> rfl

abbrev Place := G.End ⊕ C.Turn × Bool

def use : C.Place → (H).End := Sum.elim C.original (Function.uncurry C.relay)

def parse : (H).End → C.Place
  | .inl (.inl i) => .inl (.inl (.inl i))
  | .inr (.inl i) => .inl (.inr (.inl i))
  | .inl (.inr ⟨e, k⟩) => Fin.cases (.inl (tip G e false)) (fun j => .inr (⟨e, j⟩, false)) k
  | .inr (.inr ⟨e, k⟩) => Fin.lastCases (.inl (tip G e true)) (fun j => .inr (⟨e, j⟩, true)) k

theorem parse_original (e : G.End) : C.parse (C.original e) = .inl e := by
  rcases e with (i|e)|(j|e) <;> first | rfl | simp [original, right, last, parse, tip]

theorem parse_relay (t : C.Turn) (b : Bool) : C.parse (C.relay t b) = .inr (t, b) := by
  cases b
  · exact Fin.cases_succ _
  · simp [relay, before, parse]

def positions : C.Place ≃ (H).End where
  toFun := C.use
  invFun := C.parse
  left_inv
    | .inl e => C.parse_original e
    | .inr (t, b) => C.parse_relay t b
  right_inv := by
    rintro ((i|⟨e, k⟩)|(j|⟨e, k⟩))
    · rfl
    · induction k using Fin.cases with
      | zero => rfl
      | succ k =>
        change C.use (C.parse (C.relay ⟨e, k⟩ false)) = _
        rw [parse_relay]; rfl
    · rfl
    · induction k using Fin.lastCases with
      | last =>
        change C.use (C.parse (C.original (tip G e true))) = _
        rw [parse_original]; rfl
      | cast k =>
        change C.use (C.parse (C.relay ⟨e, k⟩ true)) = _
        rw [parse_relay]; rfl

theorem cases_end (e : (H).End) :
    (∃ q, e = C.original q) ∨ (∃ t b, e = C.relay t b) := by
  obtain ⟨q | ⟨t, b⟩, rfl⟩ := C.positions.surjective e
  · exact .inl ⟨q, rfl⟩
  · exact .inr ⟨t, b, rfl⟩

def value (G : Diagram F x y) (v : G.V) (z : G.End → Bool) :=
  Transcript.sample (G.table v) (fun i => z (G.portEquiv ⟨v, i⟩))

theorem test (v : V) (z : (H).End → Bool) :
    value H v z = (∏ w : {w // C.owner w = v}, value G w (z ∘ C.original)) *
      if ∀ t, C.joint t = v → z (C.relay t true) = z (C.relay t false) then 1 else 0 := by
  change (H).weight v (z ∘ Sum.inl) (z ∘ Sum.inr) = _
  rw [Diagram.weight_ofLocal _ _ _ C.local_factor]
  apply congrArg₂ (· * ·)
  · rfl
  · change (∏ t : {t // C.joint t = v}, if z (C.relay t true) = z (C.relay t false) then (1 : F) else 0) = _
    split
    · rename_i h
      exact prod_eq_one (fun t _ => ite_eq_left (h _ t.property))
    · rename_i h
      push Not at h
      obtain ⟨t, hv, ht⟩ := h
      exact prod_eq_zero (mem_univ ⟨t, hv⟩) (ite_eq_right ht)

end Chain
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# Anchors for reading labels at relay sites

All routes joining the same ordered pair follow the same simple
path. Each intermediate site belongs to the tree of just one old
station, whose span numbers therefore identify every passing wire.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Chain
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  (C : Chain G V)

structure Frame where
  root : V → V
  one : Function.Injective C.owner
  fix : ∀ v, root (C.owner v) = C.owner v
  agrees : ∀ e e', G.source e = G.source e' → G.target e = G.target e' →
    C.turns e = C.turns e' ∧ C.node e = C.node e'
  simple : ∀ e i j, i ≤ C.turns e + 1 → j ≤ C.turns e + 1 → C.node e i = C.node e j → i = j
  atJoint : ∀ t, root (C.joint t) = C.owner (G.source t.1) ∨ root (C.joint t) = C.owner (G.target t.1)

namespace Frame
variable {C} (f : C.Frame)

def side (t : C.Turn) := decide (f.root (C.joint t) = C.owner (G.target t.1))

omit [Field F] [Fintype V] in
theorem side_eq (t : C.Turn) : f.root (C.joint t) = C.owner (endpoint G t.1 (f.side t)) := by
  unfold side endpoint
  by_cases h : f.root (C.joint t) = C.owner (G.target t.1)
  · simp [h]
  · simp only [decide_eq_false h, Bool.cond_false]
    exact (f.atJoint t).resolve_right h

omit [Field F] [Fintype V] in
theorem away (t : C.Turn) : f.root (C.joint t) ≠ C.joint t := by
  intro e
  have h := t.2.isLt
  rcases f.atJoint t with hp|hp
  · have := f.simple t.1 (t.2.val + 1) 0 (by omega) (by omega) (e.symm.trans (hp.trans (C.start _).symm))
    omega
  · have := f.simple t.1 (t.2.val + 1) (C.turns t.1 + 1) (by omega) le_rfl
      (e.symm.trans (hp.trans (C.finish _).symm))
    omega

omit [Field F] [Fintype V] in
include f in
theorem joints {t t' : C.Turn} (e : t.1 = t'.1) (h : C.joint t = C.joint t') : t = t' := by
  obtain ⟨i, j⟩ := t
  obtain ⟨k, l⟩ := t'
  change i = k at e
  subst k
  have eq := f.simple i (j.val + 1) (l.val + 1) (by omega) (by omega) h
  rw [show j = l by apply Fin.ext; omega]

def fromTurn (t : C.Turn) := tip G t.1 (f.side t)

def ref (p : C.graph.End) := (C.parse p).elim id (fun t => f.fromTurn t.1)

theorem orig (p : G.End) : f.ref (C.original p) = p := by rw [ref, parse_original]; rfl

theorem pass (t : C.Turn) (b : Bool) : f.ref (C.relay t b) = f.fromTurn t := by
  rw [ref, parse_relay]; rfl

theorem anchor (p : C.graph.End) : f.root (C.graph.station p) = C.owner (G.station (f.ref p)) := by
  rcases C.cases_end p with ⟨q, rfl⟩|⟨t, b, rfl⟩
  · rw [orig, station_original, f.fix]
  · rw [pass, station_relay, fromTurn, station_tip]; exact f.side_eq t

theorem unique {p q : C.graph.End} (hv : C.graph.station p = C.graph.station q)
    (hd : p.isRight = q.isRight) (hr : f.ref p = f.ref q) : p = q := by
  rcases C.cases_end p with ⟨p, rfl⟩|⟨t, b, rfl⟩ <;> rcases C.cases_end q with ⟨q, rfl⟩|⟨t', b', rfl⟩
  · rw [orig, orig] at hr
    rw [hr]
  · rw [station_original, station_relay] at hv
    exact (f.away t' (hv ▸ f.fix _)).elim
  · rw [station_relay, station_original] at hv
    exact (f.away t (hv.symm ▸ f.fix _)).elim
  · rw [station_relay, station_relay] at hv
    rw [side_relay, side_relay] at hd
    rw [pass, pass] at hr
    rw [f.joints (tip_inj hr).1 hv, hd]

end Frame
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Chain
end

/-! # The old port controlling a directed segment of a path -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Chain.Frame
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  {C : Chain G V} (f : C.Frame)
local notation "H" => C.graph

def point (i : C.Edge) (b : Bool) := cond b (i.2.val + 1) i.2.val

omit [Field F] [Fintype V] in
theorem point_le (i : C.Edge) (b : Bool) : point i b ≤ C.turns i.1 + 1 := by
  cases b <;> first | exact i.2.isLt.le | exact i.2.isLt

theorem endpoint_node (i : C.Edge) (b : Bool) : endpoint H i b = C.node i.1 (point i b) := by
  cases b <;> rfl

def leg (i : C.Edge) (b : Bool) := decide (f.root (C.node i.1 (point i b)) = C.owner (G.target i.1))

omit [Field F] [Fintype V] in
include f in
theorem separate (e : G.E) : C.owner (G.source e) ≠ C.owner (G.target e) := by
  intro h
  have := f.simple e 0 (C.turns e + 1) (by omega) le_rfl ((C.start _).trans (h.trans (C.finish _).symm))
  omega

theorem ref_tip (i : C.Edge) (b : Bool) : f.ref (tip H i b) = tip G i.1 (f.leg i b) := by
  obtain ⟨e, k⟩ := i
  cases b
  · induction k using Fin.cases with
    | zero =>
      change f.ref (C.original (tip G e false)) = tip G e (decide (f.root (C.node e 0) = C.owner (G.target e)))
      rw [orig, C.start, f.fix, decide_eq_false (f.separate e)]
    | succ k => exact f.pass ⟨e, k⟩ false
  · induction k using Fin.lastCases with
    | last =>
      change f.ref (C.original (tip G e true)) =
        tip G e (decide (f.root (C.node e (C.turns e + 1)) = C.owner (G.target e)))
      simp only [orig, C.finish, f.fix, decide_true]
    | cast k => exact f.pass ⟨e, k⟩ true

variable {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G)

def old (z : (H).End) := p.toSeating.ends (f.ref z)

theorem old_tip (i : C.Edge) (b : Bool) : f.old p (tip H i b) = p.wirePin i.1 (f.leg i b) := by
  unfold old
  rw [ref_tip]; rfl

theorem old_here {q q' : (H).End} (h : (H).station q = (H).station q') :
    (f.old p q).1.1 = (f.old p q').1.1 := by
  have hv (e : G.End) : (p.toSeating.ends e).1.1 = p.vertex (G.station e) := by
    obtain ⟨⟨u, i⟩, rfl⟩ := G.portEquiv.surjective e
    rw [Scheme.Seating.ends_at, G.station_port]; rfl
  have e := f.one ((f.anchor q).symm.trans ((congrArg f.root h).trans (f.anchor q')))
  rw [old, old, hv, hv, e]

theorem parallel {e e' : G.E} {t t' : Bool} (hd : p.Directed)
    (h : (p.wirePin e t).1 = (p.wirePin e' t').1) :
    G.source e = G.source e' ∧ G.target e = G.target e' ∧
      ∀ b, (p.wirePin e b).1 = (p.wirePin e' b).1 := by
  have he : t = t' := (p.wirePin_dir hd _ _).symm.trans ((congrArg (S.direction r) h).trans (p.wirePin_dir hd _ _))
  subst t'
  have ht : (p.wirePin e (!t)).1 = (p.wirePin e' (!t)).1 :=
    Option.some.inj ((p.wirePin_peer _ _).symm.trans ((congrArg (S.peer r) h).trans (p.wirePin_peer _ _)))
  have pair (b : Bool) : (p.wirePin e b).1 = (p.wirePin e' b).1 := by cases t <;> cases b <;> assumption
  have eq (b : Bool) := p.vertex.injective ((p.wirePin_at _ _).symm.trans
    ((congrArg Prod.fst (pair b)).trans (p.wirePin_at _ _)))
  exact ⟨eq false, eq true, pair⟩

theorem align {i j : C.Edge} (hu : G.source i.1 = G.source j.1) (hv : G.target i.1 = G.target j.1)
    (hk : i.2.val = j.2.val) (b : Bool) :
    endpoint H i b = endpoint H j b ∧ f.leg i b = f.leg j b := by
  have hp : point i b = point j b := by unfold point; rw [hk]
  have he : C.node i.1 (point i b) = C.node j.1 (point j b) := by rw [(f.agrees _ _ hu hv).2, hp]
  rw [endpoint_node, endpoint_node]
  exact ⟨he, by simp only [leg, he, hv]⟩

theorem other {i j : C.Edge} (b : Bool) (hd : p.Directed)
    (hv : endpoint H i b = endpoint H j b)
    (hs : (f.old p (tip H i b)).1 = (f.old p (tip H j b)).1) :
    endpoint H i (!b) = endpoint H j (!b) ∧
      (f.old p (tip H i (!b))).1 = (f.old p (tip H j (!b))).1 := by
  rw [old_tip, old_tip] at hs
  obtain ⟨hc, ht, hp⟩ := parallel p hd hs
  obtain ⟨hn, he⟩ := f.agrees _ _ hc ht
  rw [endpoint_node, endpoint_node, he] at hv
  have hh := f.simple j.1 _ _ ((point_le i b).trans_eq (congrArg (·+1) hn)) (point_le j b) hv
  have hi : i.2.val = j.2.val := by cases b <;> simpa [point] using hh
  obtain ⟨hz, hl⟩ := f.align hc ht hi (!b)
  rw [old_tip, old_tip, hl]
  exact ⟨hz, hp _⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Chain.Frame
end

/-! # Parallel bits follow a common relay span in order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Chain.Frame
open Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  {C : Chain G V} (f : C.Frame) {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G)
local notation "H" => C.graph

def pair (e : ℕ) : Bool × B e ≃ B (1 + e) := Fintype.equivOfCardEq (by simp [pow_add])

def lane (q : (H).End) := pair S.e (q.isRight, (f.old p q).1.2)

def mark (q : (H).End) := ((H).station q, f.lane p q)

def offset (q : (H).End) := (f.old p q).2.val

theorem equal_mark {q q' : (H).End} (h : f.mark p q = f.mark p q') :
    (H).station q = (H).station q' ∧ q.isRight = q'.isRight ∧ (f.old p q).1 = (f.old p q').1 := by
  obtain ⟨hv, he⟩ := Prod.mk.inj h
  obtain ⟨hs, ht⟩ := Prod.mk.inj ((pair _).injective he)
  exact ⟨hv, hs, Prod.ext (f.old_here p hv) ht⟩

theorem mark_inj {q q' : (H).End} (h : f.mark p q = f.mark p q')
    (hn : f.offset p q = f.offset p q') : q = q' := by
  obtain ⟨hv, hd, hs⟩ := f.equal_mark p h
  exact f.unique hv hd (p.toSeating.ends.injective (Sigma.ext hs ((Fin.heq_ext_iff (congrArg (S.width r) hs)).mpr hn)))

private theorem parallel_bit (hd : p.Directed) (e : G.E) (b : Bool)
    (a : Fin (S.width r (p.wirePin e b).1)) :
    ∃ k, (p.wirePin k b).1 = (p.wirePin e b).1 ∧ (p.wirePin k b).2.val = a.val := by
  obtain ⟨q, hq⟩ := p.toSeating.ends.surjective ⟨(p.wirePin e b).1, a⟩
  have hv : (p.toSeating.ends q).1 = (p.wirePin e b).1 := by rw [hq]
  have dir : q.isRight = b := (hd q).symm.trans ((congrArg (S.direction r) hv).trans (p.wirePin_dir hd e b))
  have inside : S.peer r (p.toSeating.ends q).1 ≠ none := by rw [hv, p.wirePin_peer]; simp
  have hw := congrArg (fun t => t.2.val) hq
  rcases q with (i|k)|(i|k)
  · exact (inside (p.input i)).elim
  · subst b; exact ⟨k, hv, hw⟩
  · exact (inside (p.output i)).elim
  · subst b; exact ⟨k, hv, hw⟩

theorem covers (hd : p.Directed) (q : (H).End) (k : ℕ) (hk : k < S.width r (f.old p q).1) :
    ∃ z, f.mark p z = f.mark p q ∧ f.offset p z = k := by
  rcases C.cases_end q with ⟨e, rfl⟩|⟨t, b, rfl⟩
  · rw [old, orig] at hk
    obtain ⟨j, hj⟩ := p.toSeating.ends.surjective ⟨(p.toSeating.ends e).1, ⟨k, hk⟩⟩
    have hs : (p.toSeating.ends j).1 = (p.toSeating.ends e).1 := by rw [hj]
    have hv : G.station j = G.station e := by
      obtain ⟨⟨a, i⟩, rfl⟩ := G.portEquiv.surjective j
      obtain ⟨⟨b, l⟩, rfl⟩ := G.portEquiv.surjective e
      rw [G.station_port, G.station_port]
      rw [Scheme.Seating.ends_at, Scheme.Seating.ends_at] at hs
      exact p.vertex.injective (congrArg Prod.fst hs)
    have hb : j.isRight = e.isRight := (hd j).symm.trans ((congrArg (S.direction r) hs).trans (hd e))
    refine ⟨C.original j, ?_, ?_⟩
    · simp only [mark, lane, station_original, hv, C.side_original j, C.side_original e, hb, old, orig, hs]
    · rw [offset, old, orig, hj]
  · rw [old, pass] at hk
    obtain ⟨e, hs, hk⟩ := parallel_bit p hd t.1 (f.side t) ⟨k, hk⟩
    obtain ⟨hc, ht, hp⟩ := parallel p hd hs
    obtain ⟨hn, he⟩ := f.agrees e t.1 hc ht
    let u : C.Turn := ⟨e, t.2.cast hn.symm⟩
    have hv : C.joint u = C.joint t := congrFun he (t.2.val + 1)
    have hb : f.side u = f.side t := by unfold side; rw [hv, show G.target u.1 = _ from ht]
    have hu : f.old p (C.relay u b) = p.wirePin e (f.side t) := by rw [old, pass, fromTurn, hb]; rfl
    have hq : f.old p (C.relay t b) = p.wirePin t.1 (f.side t) := by rw [old, pass]; rfl
    refine ⟨C.relay u b, ?_, ?_⟩
    · simp only [mark, lane, station_relay, hv, C.side_relay u b, C.side_relay t b, hu, hq, hs]
    · rw [offset, hu]; exact hk

def opposite (G : Diagram F x y) : G.End → Option G.End
  | .inl (.inr e) => some (tip G e true)
  | .inr (.inr e) => some (tip G e false)
  | _ => none

omit [Field F] in
theorem opposite_tip (e : G.E) (b : Bool) : opposite G (tip G e b) = some (tip G e (!b)) := by cases b <;> rfl

theorem old_boundary (i : slots x ⊕ slots y) :
    f.old p (boundaryEnd H i) = p.toSeating.ends (boundaryEnd G i) := by
  have hi : boundaryEnd H i = C.original (boundaryEnd G i) := by cases i <;> rfl
  rw [hi, old, orig]

omit [Field F] in
theorem either (j : G.End) : (∃ i, j = boundaryEnd G i) ∨ (∃ e b, j = tip G e b) := by
  rcases j with (i|e)|(i|e)
  · exact .inl ⟨.inl i, rfl⟩
  · exact .inr ⟨e, false, rfl⟩
  · exact .inl ⟨.inr i, rfl⟩
  · exact .inr ⟨e, true, rfl⟩

theorem contacts (hd : p.Directed) {q q' : (H).End} (h : f.mark p q = f.mark p q') :
    (opposite H q).map (f.mark p) = (opposite H q').map (f.mark p) := by
  obtain ⟨hv, hb, hs⟩ := f.equal_mark p h
  have ne (i : slots x ⊕ slots y) (e : C.Edge) (b : Bool) :
      (f.old p (boundaryEnd H i)).1 ≠ (f.old p (tip H e b)).1 := by
    rw [old_boundary, old_tip]
    intro he
    have hh := (p.no_peer _).mpr ⟨i, rfl⟩
    rw [he, p.wirePin_peer] at hh
    cases hh
  rcases either q with ⟨i, rfl⟩ | ⟨e, b, rfl⟩ <;> rcases either q' with ⟨j, rfl⟩ | ⟨d, c, rfl⟩
  · cases i <;> cases j <;> rfl
  · exact (ne _ _ _ hs).elim
  · exact (ne _ _ _ hs.symm).elim
  · rw [side_tip, side_tip] at hb
    subst c
    rw [station_tip, station_tip] at hv
    obtain ⟨hx, hy⟩ := f.other p b hd hv hs
    simp only [opposite_tip, Option.map_some, mark, lane, station_tip, side_tip e (!b), side_tip d (!b), hx, hy]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Chain.Frame
end

/-!
# Merging stations in different suffix blocks

No edge joins different blocks. When the original board has no loops
every wire therefore survives the merge, including each newly attached
boundary wire. Pruning a neutral scalar needs no correction.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Finset
open scoped Classical

variable {F X : Type} [Field F] [Fintype X] {a b : Wire}
    {G : Diagram F a b} {f : G.V → X}

def Separated (G : Diagram F a b) (f : G.V → X) :=
  ∀ i, f (G.source i) ≠ f (G.target i)

namespace Separated
variable (h : G.Separated f)

abbrev edges : G.E ≃ G.Between f where
  toFun i := ⟨i, h i⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ends : G.End ≃ (G.coarsen f).End :=
  ((Equiv.refl _).sumCongr h.edges).sumCongr ((Equiv.refl _).sumCongr h.edges)

theorem station (t : G.End) : (G.coarsen f).station (h.ends t) = f (G.station t) := by
  rcases t with (_|_)|(_|_) <;> rfl

omit [Field F] [Fintype X] in
private theorem lift {Y : Type} (t : Y ⊕ G.Between f → Bool) (w : (G.partition f).Inside) :
    (G.partition f).lift t w = t ∘ Sum.map id h.edges := by
  funext i
  rcases i with i|i
  · rfl
  have he : (G.partition f).edges.symm i = .inl (h.edges i) :=
    (G.partition f).edges.symm_apply_eq.mpr rfl
  change Sum.elim (t ∘ .inr) _ ((G.partition f).edges.symm i) = _
  rw [he]
  rfl

theorem weight (q : X) (w : (G.coarsen f).End → Bool) :
    (G.coarsen f).weight q (w ∘ .inl) (w ∘ .inr) =
      ∏ v : {v // f v = q}, G.weight v (w ∘ h.ends ∘ .inl) (w ∘ h.ends ∘ .inr) := by
  let _ : IsEmpty ((G.partition f).hidden q) := ⟨fun i => h i.val.val i.val.property⟩
  rw [Clustering.weight_collapse, Fintype.sum_unique]
  simp only [h.lift]
  rfl

include h in
theorem zero (v : G.V) (hv : (G.coarsen f).arity (f v) = 0) : G.arity v = 0 := by
  by_contra! hn
  have hdeg : 0 < Fintype.card {q : G.End // G.station q = v} := by rw [G.degree v]; omega
  obtain ⟨q, hq⟩ := Classical.choice (Fintype.card_pos_iff.mp hdeg)
  have hc : 0 < Fintype.card {z // (G.coarsen f).station z = f v} :=
    Fintype.card_pos_iff.mpr ⟨⟨h.ends q, by rw [h.station, hq]⟩⟩
  rw [(G.coarsen f).degree (f v), hv] at hc
  exact lt_irrefl _ hc

include h in
theorem prune_eval (neutral : ∀ v, G.arity v = 0 → ∀ t, Transcript.sample (G.table v) t = 1) :
    (G.coarsen f).prune.eval = G.eval := by
  let K := G.coarsen f
  have hz (q : X) (hq : ¬ 0 < K.arity q) (u : Val a) (v : Val b) (z : K.E → Bool) :
      K.vertex u v z q = 1 := by
    let w : K.End → Bool := Sum.elim (Sum.elim (bits a u) z) (Sum.elim (bits b v) z)
    change (G.coarsen f).weight q (w ∘ .inl) (w ∘ .inr) = 1
    rw [h.weight]
    refine prod_eq_one fun i _ => ?_
    have he : G.arity i = 0 := h.zero i (i.2.symm ▸ Nat.eq_zero_of_not_pos hq)
    exact neutral i he (fun j => w (h.ends (G.portEquiv ⟨i.val, j⟩)))
  refine Eq.trans ?_ (G.eval_coarsen f)
  funext u v
  change K.prune.eval u v = K.eval u v
  unfold eval
  apply sum_congr rfl
  intro z _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v => 0 < K.arity v) (K.vertex u v z)]
  rw [show (∏ q : {q // ¬0 < K.arity q}, K.vertex u v z q) = 1 from
    prod_eq_one fun q _ => hz _ q.2 _ _ _, mul_one]
  rfl

end Separated
end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Local choice of bins

Each colony uses only its own suffix-indexed charge vector.
Padding empty suffixes by zero preserves the quadratic estimate.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Cells
open Finset Packing
open scoped Classical

variable {D T : ℕ} {U X Y : Type} [Fintype U] [Fintype X] [Fintype Y]

private theorem per_cell (l : U → ℝ) (hD : 0 < D) (hl : ∀ u, 0 ≤ l u)
    (hm : ∑ u, l u ≤ (D : ℝ) * T) :
    ∃ b : U → Fin D, ∑ i, (push b l i) ^ 2 ≤ (∑ u, (l u) ^ 2) + 2 * T*∑ u, l u := by
  obtain ⟨b, hb⟩ := bins (fun _ : U => ()) l D T hD hl (by simpa [push] using hm)
  refine ⟨b, ?_⟩
  have eq (i : Fin D) : push (fun x => ((), b x)) l ((), i) = push b l i := by
    apply sum_congr rfl
    intro j _
    by_cases h : b j = i <;> simp [h]
  rw [Fintype.sum_prod_type] at hb
  simpa only [Fintype.sum_unique, eq] using hb

def chooseBin (D T : ℕ) (hD : 0 < D) (l : U → ℝ) : U → Fin D :=
  if h : (∀ u, 0 ≤ l u) ∧ (∑ u, l u) ≤ (D : ℝ) * T
  then (per_cell l hD h.1 h.2).choose else fun _ => ⟨0, hD⟩

omit [Fintype Y] in
private theorem push_column (b : X → U → Y) (l : X × U → ℝ) (x : X) (i : Y) :
    push (fun p : X × U => (p.1, b p.1 p.2)) l (x, i) = push (b x) (fun u => l (x, u)) i := by
  unfold push
  rw [Fintype.sum_prod_type, sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · simp

private theorem squares (f : X → Y) (l : X → ℝ) (hf : Function.Injective f) :
    (∑ y, (push f l y) ^ 2) = ∑ x, (l x) ^ 2 := by
  rw [← sum_push f (fun x => (l x) ^ 2)]
  apply sum_congr rfl
  intro y _
  by_cases h : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := h
    simp [push, hf.eq_iff]
  · have hn : ∀ x, f x ≠ y := fun x he => h ⟨x, he⟩
    simp [push, hn]

variable {F : Type} {x y : Wire} {h a g : ℕ} {L θ : ℝ} {P : Board F x y h}
    (C : Cells P a g D T L) (row : P.diagram.V → U)

def column (c : C.A) (u : U) := push (fun i => (C.cell i, row i)) P.charge (c, u)
def bin (hD : 0 < D) (v : P.diagram.V) := chooseBin D T hD (C.column row (C.cell v)) (row v)

theorem bin_sq (hD : 0 < D) (hr : Function.Injective (fun i => (C.cell i, row i)))
    (h₁ : ∑ v, P.charge v ≤ L) (h₂ : ∑ v, P.charge v ^ 2 ≤ L * T) :
    ∑ z, (push (C.pack (C.bin row hD)) P.charge z) ^ 2 ≤ 3 * L * T := by
  let f := fun v => (C.cell v, row v)
  let l := push f P.charge
  let b := fun c => chooseBin D T hD (C.column row c)
  have hb (c : C.A) : ∑ i, (push (b c) (C.column row c) i) ^ 2 ≤
      (∑ u, (l (c, u)) ^ 2) + 2 * T*∑ u, l (c, u) := by
    have hp u := push_nonneg f P.charge P.charge_nonneg (c, u)
    have hm : (∑ u, l (c, u)) ≤ (D : ℝ) * T := by
      rw [← push_fst, show l = push f P.charge from rfl, push_comp]
      exact C.mass c
    have h : (∀ u, 0 ≤ C.column row c u) ∧ (∑ u, C.column row c u) ≤ (D : ℝ) * T := ⟨hp, hm⟩
    simp only [b, chooseBin, dite_eq_left h]
    exact (per_cell _ hD h.1 h.2).choose_spec
  let merge := fun p : C.A × U => (p.1, b p.1 p.2)
  change (∑ z, (push (merge ∘ f) P.charge z) ^ 2) ≤ _
  simp only [← push_comp, Fintype.sum_prod_type, merge, push_column]
  refine (sum_le_sum (fun c _ => hb c)).trans ?_
  simp only [sum_add_distrib, ← mul_sum]
  rw [← Fintype.sum_prod_type (fun p => (l p) ^ 2), ← Fintype.sum_prod_type l]
  unfold l
  rw [squares f P.charge hr, sum_push]
  linarith only [h₂, mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (α := ℝ) T)]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Cells
end
