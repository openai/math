import OAI.LinearAlgebra.MatrixExponent.Packing.RestoreCost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Spans
import OAI.LinearAlgebra.MatrixExponent.Rounds.Bins
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress

/-! # A single path through the full and short trees of a tether -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Tether.Plan
open Finset
open scoped Classical

variable {V G I : Type} {r s w : ℕ} {sw : Detour.Switch (End V r s) w}
    (P : Plan sw G I)

abbrev length (w s : ℕ) := Detour.steps w + Nat.clog 2 s

def walk (i : I) (k : ℕ) :=
  if k < Detour.steps w then (P.group i, sw.path (P.ok i) k)
  else P.climb (k - Detour.steps w) i

theorem low (i : I) {k : ℕ} (h : k ≤ Detour.steps w) :
    P.walk i k = (P.group i, sw.path (P.ok i) k) := by
  unfold walk
  rcases h.eq_or_lt with rfl|hk
  · simp [climb]
  · exact ite_eq_left hk

theorem high (i : I) (k : ℕ) : P.walk i (Detour.steps w + k) = P.climb k i := by
  simp [walk]

@[simp] theorem walk_first (i : I) : P.walk i 0 = P.terminal i := by
  rw [low _ _ (Nat.zero_le _), Detour.Switch.path_zero]; rfl

@[simp] theorem walk_last (i : I) : P.walk i (length w s) = P.frozen i := by
  unfold length
  rw [high, climb, Tree.climb_top]; rfl

theorem walk_step (i : I) (k : Fin (length w s)) :
    (P.walk i k.val, P.walk i (k.val + 1)) =
      P.supply ((finSumFinEquiv.symm k).map (fun t => (t, i)) (fun t => (t, i))) := by
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective k
  rw [Equiv.symm_apply_apply]
  rcases t with t|t
  · change (P.walk i t.val, P.walk i (t.val + 1)) = P.cold (t, i)
    rw [low _ _ t.isLt.le, low _ _ t.isLt]; rfl
  · change (P.walk i (Detour.steps w + t.val), P.walk i (Detour.steps w + t.val + 1)) = P.hot (t, i)
    rw [Nat.add_assoc, high, high]; rfl

theorem walk_simple (i : I) {k l : ℕ} (hk : k ≤ length w s) (hl : l ≤ length w s)
    (he : P.walk i k = P.walk i l) : k = l := by
  have cold {j q : ℕ} (hj : j ≤ Detour.steps w) (hq : q ≤ Detour.steps w)
      (h : P.walk i j = P.walk i q) : j = q := by
    rw [low _ _ hj, low _ _ hq] at h
    have e := (Prod.mk.inj h).2
    apply sw.path_inj _ hj hq _ e
    have ho := congrArg Detour.owner e
    rw [sw.path_owner, sw.path_owner] at ho
    cases a : Detour.Switch.side w j <;> cases b : Detour.Switch.side w q <;> simp_all
  have tip {j q : ℕ} (hj : j < Detour.steps w) (hq : Detour.steps w ≤ q)
      (h : P.walk i j = P.walk i q) : False := by
    have ho := congrArg (fun t => Detour.owner t.2) h
    simp only [walk, ite_eq_left hj, ite_eq_right hq.not_gt, climb, sw.path_owner] at ho
    cases e : Detour.Switch.side w j
    · simp [e, Detour.owner] at ho
    · have hu : P.walk i q = P.walk i (Detour.steps w) := by
        rw [walk, ite_eq_right hq.not_gt, low _ _ le_rfl, sw.path_last]
        unfold climb
        have ht : (Sum.inr (P.src i, Tree.tip (P.pin i)) : End V r s) =
            .inr (P.src i, Tree.climb (P.pin i) (q - Detour.steps w)) := by
          simpa [e, Detour.owner] using ho
        rw [ht]
      exact hj.ne (cold hj.le le_rfl (h.trans hu))
  by_cases a : k < Detour.steps w <;> by_cases b : l < Detour.steps w
  · exact cold a.le b.le he
  · exact (tip a (by omega) he).elim
  · exact (tip b (by omega) he.symm).elim
  · simp only [walk, ite_eq_right a, ite_eq_right b, climb, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, true_and] at he
    unfold length at hk hl
    have eq := congrArg Fin.val (Tree.climb_injective (P.pin i)
      (a₁ := ⟨k - Detour.steps w, by omega⟩) (a₂ := ⟨l - Detour.steps w, by omega⟩) he)
    change k - Detour.steps w = l - Detour.steps w at eq
    omega

end OAI.LinearAlgebra.MatrixExponent.Packing.Tether.Plan
end

/-!
# The directed layout of the restored network

Input tethers run from core to border and output tethers run in
reverse. This preserves direction at every surviving port.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
open Assembly.Restore Finset
open scoped Classical

variable {F T : Type} [Fintype T] {a b x y : Wire} {h u D r s : ℕ}
  {L : Fringe x y T} {G : HostNet F L h u} (A : G.Restore D r s)
  (B : Border F T a b x y) (he : L.tensor = B.tensor)

local notation "H" => B.attach G.diagram
local notation "n" => Tether.Plan.length (Tether.width D r s) s

private theorem length_pos : 0 < n := by unfold Tether.Plan.length Detour.steps; omega

def travel (i : slots x ⊕ slots y) (j : ℕ) :=
  A.plan.walk i (if i.isRight then n - j else j)

private theorem travel_start (i : slots x ⊕ slots y) (he : L.tensor = B.tensor) :
    A.travel i 0 = A.owner ((H).source (.inr i)) := by
  cases i with
  | inl i => exact A.plan.walk_first _
  | inr j =>
    change A.plan.walk (.inr j) n = A.toFrozen (B.tensor (.inr j))
    rw [Tether.Plan.walk_last, A.frozen_eq, he]

private theorem travel_last (i : slots x ⊕ slots y) (he : L.tensor = B.tensor) :
    A.travel i n = A.owner ((H).target (.inr i)) := by
  cases i with
  | inl i =>
    change A.plan.walk (.inl i) n = A.toFrozen (B.tensor (.inl i))
    rw [Tether.Plan.walk_last, A.frozen_eq, he]
  | inr j =>
    change A.plan.walk (.inr j) (n - n) = A.plan.terminal (.inr j)
    rw [Nat.sub_self, Tether.Plan.walk_first]

def route : Chain H (Cell h × A.Space) where
  owner := A.owner
  turns := Sum.elim (fun _ => 0) (fun _ => n - 1)
  node := Sum.elim (fun e i => if i = 0 then (A.oldCore e).1 else (A.oldCore e).2) A.travel
  start
    | .inl _ => rfl
    | .inr i => A.travel_start B i he
  finish
    | .inl _ => rfl
    | .inr i => by
      change A.travel i (n - 1 + 1) = _
      rw [Nat.sub_add_cancel length_pos]
      exact A.travel_last B i he

local notation "C" => A.route B he

private def index (i : slots x ⊕ slots y) : Fin (n - 1 + 1) ≃ Fin n :=
  (finCongr (Nat.sub_add_cancel length_pos)).trans (if i.isRight then Fin.revPerm else .refl _)

private def into : (C).Edge → A.Wires
  | ⟨.inl e, _⟩ => .inr e
  | ⟨.inr i, j⟩ =>
    .inl ((finSumFinEquiv.symm (index i j)).map (fun k => (k, i)) (fun k => (k, i)))

private def pick : A.Wires → (C).Edge
  | .inr e => ⟨.inl e, ⟨0, Nat.zero_lt_succ _⟩⟩
  | .inl (.inl (j, i)) => ⟨.inr i, (index i).symm (finSumFinEquiv (.inl j))⟩
  | .inl (.inr (j, i)) => ⟨.inr i, (index i).symm (finSumFinEquiv (.inr j))⟩

def arrows : (C).Edge ≃ A.Wires where
  toFun := A.into B he
  invFun := A.pick B he
  left_inv := by
    rintro ⟨e|i, j⟩
    · have hz : (j : Fin 1) = 0 := Fin.eq_zero j
      cases hz; rfl
    · obtain ⟨k, hk⟩ := ((index (D := D) (r := r) (s := s) i).symm).surjective j
      subst j
      obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
      cases k <;> simp [pick, into]
  right_inv := by rintro ((⟨k, i⟩|⟨k, i⟩)|e) <;> simp [pick, into]

theorem links (e : (C).Edge) :
    ((C).src (.inr e), (C).dst (.inr e)) = A.supply (A.arrows B he e) ∨
    ((C).src (.inr e), (C).dst (.inr e)) = (A.supply (A.arrows B he e)).swap := by
  rcases e with ⟨e|i, k⟩
  · have hz : (k : Fin 1) = 0 := Fin.eq_zero k
    cases hz; exact .inl rfl
  · let j : Fin n := index i k
    let g := A.plan.supply ((finSumFinEquiv.symm j).map (fun k => (k, i)) (fun k => (k, i)))
    have eq : g = (A.plan.walk i j.val, A.plan.walk i (j.val + 1)) := (A.plan.walk_step i j).symm
    change (A.travel i k.val, A.travel i (k.val + 1)) = g ∨
      (A.travel i k.val, A.travel i (k.val + 1)) = g.swap
    rw [eq]
    cases i with
    | inl i => exact .inl rfl
    | inr i =>
      right
      have hk : k.val < n - 1 + 1 := k.isLt
      have hp : 0 < n := length_pos
      have eqj : j.val = n - (k.val + 1) := rfl
      change (A.plan.walk _ (n - k.val), A.plan.walk _ (n - (k.val + 1))) =
        (A.plan.walk _ (j.val + 1), A.plan.walk _ j.val)
      rw [eqj, show n - (k.val + 1) + 1 = n - k.val by omega]

theorem simple (hc : ∀ e, (A.oldCore e).1 ≠ (A.oldCore e).2)
    {e : (H).E} {i j : ℕ} (hi : i ≤ (C).turns e + 1) (hj : j ≤ (C).turns e + 1)
    (hij : (C).node e i = (C).node e j) : i = j := by
  cases e with
  | inl e =>
    change i ≤ 1 at hi
    change j ≤ 1 at hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact (hc e hij).elim | exact (hc e hij.symm).elim
  | inr t =>
    change i ≤ n - 1 + 1 at hi
    change j ≤ n - 1 + 1 at hj
    rw [Nat.sub_add_cancel length_pos] at hi hj
    change A.travel t i = A.travel t j at hij
    unfold travel at hij
    split_ifs at hij
    · have := A.plan.walk_simple t (Nat.sub_le _ _) (Nat.sub_le _ _) hij
      omega
    · exact A.plan.walk_simple t hi hj hij

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
end

/-! # All charge estimates for the directed restoration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
open Assembly.Restore Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {a b x y : Wire} {h u D r s : ℕ}
  {L : Fringe x y T} {G : HostNet F L h u} (A : G.Restore D r s)
  (B : Border F T a b x y) (he : L.tensor = B.tensor)
  (cap : ∀ t, ((B.attach G.diagram).arity (.inr t) : ℝ) ≤ L.charge t)

local notation "H" => B.attach G.diagram
local notation "C" => A.route B he

theorem route_support (e : (C).graph.E) :
    ((C).graph.target e).1 = ((C).graph.source e).1 ∧
      ((C).graph.target e).2 ∈ A.adj ((C).graph.source e).2 := by
  let P (z : (Cell h × A.Space) × (Cell h × A.Space)) :=
    z.2.1 = z.1.1 ∧ z.2.2 ∈ A.adj z.1.2
  change P ((C).src (.inr e), (C).dst (.inr e))
  have l := A.support (A.arrows B he e)
  rcases A.links B he e with hh|hh <;> rw [hh]
  · exact ⟨l.1.symm, l.2⟩
  · exact ⟨l.1, Tether.adj_symm _ _ G.cs _ _ l.2⟩

theorem route_loopless (hl : ∀ e, G.src e ≠ G.dst e) (e : (C).graph.E) :
    (C).graph.source e ≠ (C).graph.target e := by
  have hc (e : G.diagram.E) : (A.oldCore e).1 ≠ (A.oldCore e).2 := by
    intro hp
    have h := A.core_injective hp
    rw [G.units.left, G.units.right] at h
    exact hl _ (congrArg Prod.fst h)
  intro hh
  exact Nat.ne_of_lt (Nat.lt_succ_self _) (A.simple B he hc e.2.isLt.le e.2.isLt hh)

theorem route_arity (v : Cell h × A.Space) :
    (C).graph.arity v = exterior H A.owner v + Packing.degree A.supply v := by
  let pair := fun e : (C).Edge => ((C).src (.inr e), (C).dst (.inr e))
  have eq : Packing.degree pair v = Packing.degree A.supply v := by
    simp only [degree_sum]
    apply Fintype.sum_equiv (A.arrows B he)
    intro e
    unfold pair
    rcases A.links B he e with he|he <;> rw [he]
    exact Nat.add_comm _ _
  have push_id {X : Type} [Fintype X] (l : X → ℝ) (x : X) : push id l x = l x := by simp [push]
  have hh := site_arity (C).graph id v
  rw [push_id] at hh
  change ((C).graph.arity v : ℝ) = (exterior H A.owner v : ℝ) + Packing.degree pair v at hh
  rw [eq] at hh
  exact_mod_cast hh

abbrev board : Rounds.Board F a b h where
  V := A.Space
  diagram := (C).graph
  place := Prod.swap
  one := Prod.swap_injective
  adj := A.adj
  sym := Tether.adj_symm A.sw G.C G.cs
  edge := A.route_support B he
  charge := A.charge
  cover v := by
    rw [A.route_arity B he, Nat.cast_add]
    exact add_le_add_left (A.exterior_covers B cap v) _

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
end

/-! # Anchors of the core, contact trees and splitting trees -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
open Assembly.Restore
open scoped Classical

variable {F T : Type} [Fintype T] {a b x y : Wire} {h u D r s : ℕ}
  {L : Fringe x y T} {G : HostNet F L h u} (A : G.Restore D r s)
  (B : Border F T a b x y) (he : L.tensor = B.tensor)

local notation "H" => B.attach G.diagram
local notation "C" => A.route B he

def root (v : Cell h × A.Space) : Cell h × A.Space :=
  (v.1, (Detour.owner v.2).elim Tether.core (fun p => Tether.member p.1))

omit [Fintype T] in
theorem root_owner (v : G.diagram.V ⊕ T) : A.root (A.owner v) = A.owner v := by cases v <;> rfl

omit [Fintype T] in
theorem owner_inj (hp : Function.Injective G.units.place) : Function.Injective A.owner := by
  rintro (v|t) (w|z) e
  · exact congrArg Sum.inl (hp (A.core_injective e))
  · cases (congrArg Prod.snd e)
  · cases (congrArg Prod.snd e)
  · exact congrArg Sum.inr (A.frozen_injective e)

omit [Fintype T] in
theorem root_walk (i : slots x ⊕ slots y) (k : ℕ) :
    A.root (A.plan.walk i k) = A.plan.terminal i ∨ A.root (A.plan.walk i k) = A.plan.frozen i := by
  unfold Tether.Plan.walk
  split
  · unfold root
    simp only [Detour.Switch.path_owner]
    split <;> first | exact .inl rfl | exact .inr rfl
  · exact .inr rfl

omit [Fintype T] in
theorem travel_eq {i j : slots x ⊕ slots y} (hi : i.isRight = j.isRight)
    (hc : portEnd G.diagram i = portEnd G.diagram j) (ht : L.tensor i = L.tensor j) :
    A.travel i = A.travel j := by
  have hf : G.far i = G.far j := congrArg G.units.place hc
  have hp := (A.outlet i j ht).mpr hf
  funext k
  simp only [travel, hi, Tether.Plan.walk, Tether.Plan.climb, plan, ht, hf, hp]

theorem agree (e e' : (H).E) (hv : (H).source e = (H).source e')
    (hw : (H).target e = (H).target e') :
    (C).turns e = (C).turns e' ∧ (C).node e = (C).node e' := by
  rcases e with e|i|j <;> rcases e' with e'|i'|j' <;>
    first | exact (Sum.inl_ne_inr hv).elim | exact (Sum.inr_ne_inl hv).elim |
      exact (Sum.inl_ne_inr hw).elim | exact (Sum.inr_ne_inl hw).elim | skip
  · have es : G.diagram.source e = G.diagram.source e' := Sum.inl.inj hv
    have et : G.diagram.target e = G.diagram.target e' := Sum.inl.inj hw
    exact ⟨rfl, by simp [route, oldCore, es, et]⟩
  · refine ⟨rfl, A.travel_eq (i := .inl i) (j := .inl i') rfl (Sum.inl.inj hv) ?_⟩
    rw [he]; exact Sum.inr.inj hw
  · refine ⟨rfl, A.travel_eq (i := .inr j) (j := .inr j') rfl (Sum.inl.inj hw) ?_⟩
    rw [he]; exact Sum.inr.inj hv

def frame (hp : Function.Injective G.units.place) (hl : ∀ e, G.src e ≠ G.dst e) : (C).Frame where
  root := A.root
  one := A.owner_inj hp
  fix := A.root_owner
  agrees := A.agree B he
  simple := by
    intro e i j hi hj hij
    refine A.simple B he ?_ hi hj hij
    intro e he
    have hh := A.core_injective he
    rw [G.units.left, G.units.right] at hh
    exact hl _ (congrArg Prod.fst hh)
  atJoint := by
    rintro ⟨e|q, j⟩
    · exact Fin.elim0 j
    · let k := if q.isRight then Tether.Plan.length (Tether.width D r s) s - (j.val + 1) else j.val + 1
      have ht := A.root_walk q k
      rw [A.frozen_eq, he] at ht
      cases q
      · exact ht
      · exact ht.symm

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
end

/-!
# Local names for the tether switch

A location splits into its old host and a suffix of bounded size.
Number the switch pins using the channel leading to the remote host
and its suffix. No ordering of the long host addresses is involved.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Packing Coloring Finset
open History.Reset
open scoped Classical

def Template.Encodes.fullChart {F T : Type} [Field F] [Fintype T] {x y : Wire}
    {L : Fringe x y T} {u : ℕ} {D : Template F} {G : HostNet F L D.scheme.h u}
    {r : D.format.obj} (p : D.Encodes r G) (full : D.full = true) : Chart G.N D.scheme.d :=
  chart p.post.nav fun v w he => by
    have hm : w ∈ D.adj G v := by simpa [Template.adj, full] using he
    obtain ⟨i, hi, _⟩ := (p.edge v w).mp hm
    exact ⟨i, p.post.host.injective ((p.host_nav v i).trans hi)⟩

namespace Restore
variable {V V' : Type} {r s w d m D : ℕ}

def ends : Tether.End V r s ≃ V × Tether.End Unit r s where
  toFun
    | .inl v => (v, .inl ())
    | .inr ((v, i), p) => (v, .inr (((), i), p))
  invFun
    | (v, .inl _) => .inl v
    | (v, .inr ((_, i), p)) => .inr ((v, i), p)
  left_inv := by rintro (v|⟨⟨v, i⟩, p⟩) <;> rfl
  right_inv := by rintro ⟨v, _|⟨⟨_, i⟩, p⟩⟩ <;> rfl

def cells : Tether.Host V r s w ≃ V × Tether.Host Unit r s w where
  toFun
    | .inl x => ((ends x).1, .inl (ends x).2)
    | .inr (x, i) => ((ends x).1, .inr ((ends x).2, i))
  invFun
    | (v, .inl x) => .inl (ends.symm (v, x))
    | (v, .inr (x, i)) => .inr (ends.symm (v, x), i)
  left_inv := by rintro (x|⟨x, i⟩) <;> simp
  right_inv := by rintro ⟨v, x|⟨x, i⟩⟩ <;> simp

def bits (r s w : ℕ) := Nat.clog 2 (Fintype.card (Tether.Host Unit r s w))

def suffix (r s w : ℕ) : Tether.Host Unit r s w ↪ B (bits r s w) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin]; exact Nat.le_pow_clog (by decide) _))

def host (e : V ↪ B m) (r s w : ℕ) : Tether.Host V r s w ↪ B (m + bits r s w) :=
  cells.toEmbedding.trans ((e.prodMap (suffix r s w)).trans (Match.rowIndex _ _).symm.toEmbedding)

theorem host_parts (e : V ↪ B m) (x : Tether.Host V r s w) :
    Match.rowIndex _ _ (host e r s w x) = (e (cells x).1, suffix r s w (cells x).2) :=
  (Match.rowIndex _ _).apply_symm_apply _

theorem near_iff (N : V → Finset V) (x y : Tether.End V r s) :
    y ∈ Tether.near N r s x ↔ (ends y).1 ∈ N (ends x).1 ∧ (ends y).2.isLeft ≠ (ends x).2.isLeft := by
  rcases x with v | ⟨⟨v, i⟩, k⟩ <;> rcases y with u | ⟨⟨u, j⟩, l⟩ <;> simp [Tether.near, ends]

variable {N : V → Finset V} (H : Chart N d)

def pinKey (x : Tether.End V r s) :
    ↥(Tether.near N r s x) ↪ Option (B d) × Tether.End Unit r s where
  toFun y := (H.label (ends x).1 (ends y.val).1, (ends y.val).2)
  inj' p q eq := by
    obtain ⟨hl, hp⟩ := Prod.mk.inj eq
    exact Subtype.ext (ends.injective (Prod.ext (H.inj _ (mem_insert_of_mem ((near_iff ..).mp p.property).1)
      (mem_insert_of_mem ((near_iff ..).mp q.property).1) hl) hp))

def pins (hd : ∀ v, (N v).card ≤ D) (x : Tether.End V r s) :
    ↥(Tether.near N r s x) ↪ Fin (Tether.width D r s) :=
  rank (pinKey H x) (by simpa using Tether.near_card N D hd x)

variable {N' : V' → Finset V'} (K : Chart N' d)
  {x : Tether.End V r s} {x' : Tether.End V' r s}

private theorem pin_maps (hs : H.Maps K (ends x).1 (ends x').1) (he : (ends x).2 = (ends x').2)
    (y : ↥(Tether.near N r s x)) :
    ∃ y' : ↥(Tether.near N' r s x'), pinKey H x y = pinKey K x' y' := by
  obtain ⟨hy, hc⟩ := (near_iff ..).mp y.property
  obtain ⟨v, hv, hk⟩ := hs _ hy
  let z := ends.symm (v, (ends y.val).2)
  have hz : ends z = (v, (ends y.val).2) := ends.apply_symm_apply _
  refine ⟨⟨z, (near_iff ..).mpr ?_⟩, ?_⟩
  · rw [hz, ←he]; exact ⟨hv, hc⟩
  · change (_, _) = (K.label _ (ends z).1, (ends z).2)
    rw [hz, hk]

theorem pins_eq (hd : ∀ v, (N v).card ≤ D) (hd' : ∀ v, (N' v).card ≤ D)
    (hs : H.Maps K (ends x).1 (ends x').1) (hs' : K.Maps H (ends x').1 (ends x).1)
    (he : (ends x).2 = (ends x').2)
    (y : ↥(Tether.near N r s x)) (y' : ↥(Tether.near N' r s x'))
    (hk : pinKey H x y = pinKey K x' y') : pins H hd x y = pins K hd' x' y' :=
  rank_eq (pin_maps H K hs he) (pin_maps K H hs' he.symm) hk

end Restore
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Transport of restored adjacency between matching neighborhoods -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Packing Coloring History.Reset Finset
open scoped Classical

variable {V V' : Type} {r s d D : ℕ} {N : V → Finset V}
local notation "W" => Tether.width D r s

def sw (H : Chart N d) (hn : ∀ v u, u ∈ N v → v ∈ N u) (hd : ∀ v, (N v).card ≤ D) :
    Detour.Switch (Tether.End V r s) W :=
  ⟨Tether.near N r s, Tether.near_symm N hn, pins H hd⟩

theorem sw_eq {F T : Type} {a b : Wire} {h u : ℕ} {L : Fringe a b T}
    {G : HostNet F L h u} (H : Chart G.N d) (A : G.Restore D r s) (hpin : A.pins = pins H A.degree) :
    A.sw = sw H G.ns A.degree := by
  unfold HostNet.Restore.sw sw
  rw [hpin]

variable [Fintype V] (C : V → Finset V) (q : Detour.Switch (Tether.End V r s) (Tether.width D r s))

private def branch : Tether.End V r s → Tether.End V r s → Prop
  | .inl v, .inl w => w ∈ C v
  | .inr (i, p), .inr (j, t) => i = j ∧ t ∈ Tree.adj p
  | _, _ => False

private def linked : Tether.Host V r s W → Tether.Host V r s W → Prop
  | .inl x, .inl y => branch C x y
  | .inl x, .inr (y, t) => x = y ∧ t = Tree.root W
  | .inr (x, p), .inl y => x = y ∧ p = Tree.root W
  | .inr (x, p), .inr (y, t) => (x = y ∧ t ∈ Tree.adj p) ∨ ∃ h : y ∈ q.near x,
      Tree.tip (q.pin x ⟨y, h⟩) = p ∧ Tree.tip (q.pin y ⟨x, q.sym _ _ h⟩) = t

private theorem linked_iff (x y : Tether.Host V r s W) :
    y ∈ Tether.adj q C x ↔ linked C q x y := by
  rcases x with x|⟨x, p⟩ <;> rcases y with y|⟨y, t⟩
  · rcases x with x|⟨x, i⟩ <;> rcases y with y|⟨y, j⟩ <;>
      simp [Tether.adj, linked, branch]
    · change Sum.inl y ∈ (C x).image Sum.inl ↔ _
      simp
    · change Sum.inr (y, j) ∉ (C x).image Sum.inl
      simp
    · change Sum.inl y ∉ (Tree.adj i).image (fun k => Sum.inr (x, k))
      simp
    · change Sum.inr (y, j) ∈ (Tree.adj i).image (fun k => Sum.inr (x, k)) ↔ _
      simp [and_comm]
  · simp [Tether.adj, linked, eq_comm]
  · by_cases hp : p = Tree.root W <;> simp [Tether.adj, Detour.Switch.adj, hp, linked, eq_comm]
  · by_cases hp : p = Tree.root W <;> simp [Tether.adj, Detour.Switch.adj, hp, linked]
    all_goals
      refine or_congr (by tauto) ?_
      let : DecidableEq (Tether.End V r s) := Classical.typeDecidableEq _
      exact mem_filter_univ _

variable {C} (H : Chart N d) (hn : ∀ v u, u ∈ N v → v ∈ N u) (hd : ∀ v, (N v).card ≤ D)

/-- All restored neighbors project to the previous closed one-neighborhood. -/
theorem project (hc : ∀ v, C v ⊆ N v) {x y : Tether.Host V r s W}
    (h : y ∈ Tether.adj (sw H hn hd) C x) :
    (cells y).1 ∈ insert (cells x).1 (N (cells x).1) := by
  rw [linked_iff] at h
  rcases x with x|⟨x, p⟩ <;> rcases y with y|⟨y, t⟩
  · rcases x with v|⟨⟨v, i⟩, p⟩ <;> rcases y with u|⟨⟨u, j⟩, t⟩
    · exact mem_insert_of_mem (hc v h)
    · exact h.elim
    · exact h.elim
    · exact mem_insert.mpr (.inl (congrArg (fun z : V × Fin r => z.1) h.1.symm))
  · rw [h.1]; exact mem_insert_self _ _
  · rw [h.1]; exact mem_insert_self _ _
  · rcases h with ⟨rfl, _⟩|⟨hy, _⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem ((near_iff N x y).mp hy).1

variable [Fintype V'] {N' C' : V' → Finset V'} (K : Chart N' d)
  (hn' : ∀ v u, u ∈ N' v → v ∈ N' u) (hd' : ∀ v, (N' v).card ≤ D)

structure LocalPair (v u : V) (v' u' : V') : Prop where
  same : v = u ↔ v' = u'
  full : u ∈ N v ↔ u' ∈ N' v'
  label : H.label v u = K.label v' u'
  forth : H.Maps K v v'
  back : K.Maps H v' v

omit [Fintype V] [Fintype V'] in
theorem LocalPair.pin {v u : V} {v' u' : V'} (h : LocalPair H K v u v' u')
    (x y : Tether.End Unit r s)
    (e : ends.symm (u, y) ∈ Tether.near N r s (ends.symm (v, x)))
    (e' : ends.symm (u', y) ∈ Tether.near N' r s (ends.symm (v', x))) :
    pins H hd _ ⟨_, e⟩ = pins K hd' _ ⟨_, e'⟩ := by
  apply pins_eq
  · simpa using h.forth
  · simpa using h.back
  · simp
  · change (H.label _ _, _) = (K.label _ _, _)
    simp [h.label]

theorem links_eq {v u : V} {v' u' : V'} (h : LocalPair H K v u v' u')
    (h' : LocalPair H K u v u' v') (hc : u ∈ C v ↔ u' ∈ C' v')
    (x y : Tether.Host Unit r s W) :
    cells.symm (u, y) ∈ Tether.adj (sw H hn hd) C (cells.symm (v, x)) ↔
      cells.symm (u', y) ∈ Tether.adj (sw K hn' hd') C' (cells.symm (v', x)) := by
  have heq (i j : Tether.End Unit r s) :
      ends.symm (v, i) = ends.symm (u, j) ↔ ends.symm (v', i) = ends.symm (u', j) := by
    simp [h.same]
  rw [linked_iff, linked_iff]
  rcases x with x|⟨x, p⟩ <;> rcases y with y|⟨y, t⟩
  · rcases x with _|⟨⟨_, i⟩, p⟩ <;> rcases y with _|⟨⟨_, j⟩, t⟩ <;>
      simp [cells, ends, linked, branch, h.same, hc]
  · exact and_congr (heq x y) Iff.rfl
  · exact and_congr (heq x y) Iff.rfl
  · refine or_congr (and_congr (heq x y) Iff.rfl) ?_
    have hm : ends.symm (u, y) ∈ Tether.near N r s (ends.symm (v, x)) ↔
        ends.symm (u', y) ∈ Tether.near N' r s (ends.symm (v', x)) := by simp [near_iff, h.full]
    constructor
    · rintro ⟨e, l, r⟩
      refine ⟨hm.mp e, ?_, ?_⟩
      · exact (congrArg Tree.tip (h.pin H hd K hd' x y e _)).symm.trans l
      · exact (congrArg Tree.tip (h'.pin H hd K hd' y x _ _)).symm.trans r
    · rintro ⟨e, l, r⟩
      refine ⟨hm.mpr e, ?_, ?_⟩
      · exact (congrArg Tree.tip (h.pin H hd K hd' x y _ e)).trans l
      · exact (congrArg Tree.tip (h'.pin H hd K hd' y x _ _)).trans r

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # The base and short address of a moving tether -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Packing History.Reset

variable {V I U : Type} {r s w : ℕ} {q : Detour.Switch (Tether.End V r s) w}
  (P : Tether.Plan q U I)

private def front (i : I) := q.pin (.inl (P.dst i)) ⟨_, P.ok i⟩
private def back (i : I) := q.pin (.inr (P.src i, Tree.tip (P.pin i))) ⟨_, q.sym _ _ (P.ok i)⟩

private def arm (x : Tether.End V r s) (p : Fin w) (k : ℕ) : Tether.Host V r s w :=
  if k ≤ Nat.clog 2 w then .inr (x, Tree.climb p k) else .inl x

private theorem arm_cells (x : Tether.End V r s) (p : Fin w) (k : ℕ) :
    cells (arm x p k) = ((ends x).1, arm (ends x).2 p k) := by
  unfold arm
  split_ifs <;> rfl

private def position (j : Fin r) (x : Fin s) (p p' : Fin w) (k : ℕ) :
    Tether.Host Unit r s w :=
  if k ≤ Nat.clog 2 w + 1 then arm (.inl ()) p (Nat.clog 2 w + 1 - k)
  else if k < Detour.steps w then arm (.inr (((), j), Tree.tip x)) p' (k - (Nat.clog 2 w + 2))
  else .inl (.inr (((), j), Tree.climb x (k - Detour.steps w)))

private theorem split_walk (i : I) (k : ℕ) :
    cells (P.walk i k).2 =
      ((if k ≤ Nat.clog 2 w + 1 then P.dst i else (P.src i).1),
        position (P.src i).2 (P.pin i) (front P i) (back P i) k) := by
  have hc : q.path (P.ok i) k =
      if k ≤ Nat.clog 2 w + 1 then arm (.inl (P.dst i)) (front P i) (Nat.clog 2 w + 1 - k)
      else arm (.inr (P.src i, Tree.tip (P.pin i))) (back P i) (k - (Nat.clog 2 w + 2)) := rfl
  unfold Tether.Plan.walk position
  by_cases h : k < Detour.steps w
  · simp only [ite_eq_left h, hc]
    split_ifs <;> rw [arm_cells] <;> rfl
  · have hn : ¬k ≤ Nat.clog 2 w + 1 := by unfold Detour.steps at h; omega
    simp only [ite_eq_right h, ite_eq_right hn]
    rfl

variable {F T F' T' : Type} {a b a' b' : Wire} {h u h' u' D d : ℕ}
  {L : Fringe a b T} {L' : Fringe a' b' T'}
  {G : HostNet F L h u} {G' : HostNet F' L' h' u'}
  (A : G.Restore D r s) (A' : G'.Restore D r s)
local notation "W" => Tether.width D r s

theorem travel_base (i : slots a ⊕ slots b) (k : ℕ) :
    (cells (A.travel i k).2).1 =
      if (if i.isRight then Tether.Plan.length W s - k else k) ≤ Nat.clog 2 W + 1
      then A.plan.dst i else (A.plan.src i).1 := by
  unfold HostNet.Restore.travel
  rw [split_walk]

theorem travel_suffix (H : Chart G.N d) (H' : Chart G'.N d)
    (pin : A.pins = pins H A.degree) (pin' : A'.pins = pins H' A'.degree)
    (i : slots a ⊕ slots b) (j : slots a' ⊕ slots b')
    (forward : LocalPair H H' (A.plan.dst i) (A.plan.src i).1 (A'.plan.dst j) (A'.plan.src j).1)
    (reverse : LocalPair H H' (A.plan.src i).1 (A.plan.dst i) (A'.plan.src j).1 (A'.plan.dst j))
    (hs : (A.plan.src i).2 = (A'.plan.src j).2) (hp : A.pin i = A'.pin j)
    (hi : i.isRight = j.isRight) (k : ℕ) :
    (cells (A.travel i k).2).2 = (cells (A'.travel j k).2).2 := by
  let x : Tether.End Unit r s := .inl ()
  let y : Tether.End Unit r s := .inr (((), (A.plan.src i).2), Tree.tip (A.pin i))
  have yh : ends.symm ((A'.plan.src j).1, y) = .inr (A'.plan.src j, Tree.tip (A'.pin j)) := by
    unfold y
    rw [hs, hp]
    rfl
  have e : ends.symm ((A.plan.src i).1, y) ∈ Tether.near G.N r s (ends.symm (A.plan.dst i, x)) := A.plan.ok i
  have e' : ends.symm ((A'.plan.src j).1, y) ∈ Tether.near G'.N r s (ends.symm (A'.plan.dst j, x)) := by
    rw [yh]; exact A'.plan.ok j
  have hf := forward.pin H A.degree H' A'.degree x y e e'
  have hb := reverse.pin H A.degree H' A'.degree y x (Tether.near_symm _ G.ns _ _ e)
    (Tether.near_symm _ G'.ns _ _ e')
  simp only [← pin, ← pin', yh] at hf hb
  change front A.plan i = front A'.plan j at hf
  have hb : back A.plan i = back A'.plan j := by
    let z : Tether.End G'.V r s := .inl (A'.plan.dst j)
    have aux (a b : Tether.End G'.V r s) (h : a = b)
        (e : z ∈ Tether.near G'.N r s a) (e' : z ∈ Tether.near G'.N r s b) :
        A'.pins a ⟨z, e⟩ = A'.pins b ⟨z, e'⟩ := by subst b; rfl
    exact hb.trans (aux _ _ yh _ _)
  have out : A.plan.pin i = A'.plan.pin j := hp
  simp only [HostNet.Restore.travel, split_walk, hi, hs, hf, hb, out]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# Reading the full neighborhood from two-step walks

Equality of addresses is needed only once per host. The block
records see the resulting bits and the short edge masks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing History.Reset
open scoped Classical

abbrev radius (d : ℕ) := (d + 1) * 2
abbrev Equalities (d : ℕ) := Format.vec (radius d) (.vec (radius d) .bit)
abbrev Preview (d : ℕ) := Format.pair (Equalities d) (.vec (radius d) (Group.Flags d))

variable {F : Type} {D : Template F}
local notation "d" => D.scheme.d

def preview (D : Template F) (r : D.format.obj) (v : B D.scheme.m) : (Preview D.scheme.d).obj :=
  let walk := Neighborhood.walks 2 (D.nav r) v
  (fun i j => decide (walk i = walk j), fun i => D.flags r (walk i))

def step {V : Type} {n : ℕ} (f : V → B n → V) (v : V) (j : Option (B n)) := j.elim v (f v)

def address {n : ℕ} (i j : Option (B n)) : B (radius n) :=
  (Neighborhood.path_surjective n 2 (i, j, ())).choose

variable [Field F] {T T' : Type} [Fintype T] [Fintype T'] {x y x' y' : Wire} {u u' : ℕ}
  {L : Fringe x y T} {L' : Fringe x' y' T'} {r r' : D.format.obj}
  {G : HostNet F L D.scheme.h u} {G' : HostNet F L' D.scheme.h u'}
  (p : D.Encodes r G) (p' : D.Encodes r' G') (v : G.V) (v' : G'.V)

def hop := step p.post.nav v

theorem follows (i j : Option (B d)) :
    Neighborhood.walks 2 (D.nav r) (p.post.host v) (address i j) =
      p.post.host (hop p (hop p v i) j) := by
  have ht : Neighborhood.path d 2 (address i j) = (i, j, ()) :=
    (Neighborhood.path_surjective d 2 (i, j, ())).choose_spec
  unfold Neighborhood.walks
  rw [ht]
  cases i <;> cases j <;> simp [Neighborhood.run, hop, step, p.host_nav]

structure Agree : Prop where
  names : ∀ i j k l, hop p (hop p v i) j = hop p (hop p v k) l ↔
    hop p' (hop p' v' i) j = hop p' (hop p' v' k) l
  flags : ∀ i, D.flags r (p.post.host (hop p v i)) = D.flags r' (p'.post.host (hop p' v' i))

theorem agree (h : preview D r (p.post.host v) = preview D r' (p'.post.host v')) :
    Agree p p' v v' := by
  constructor
  · intro i j k l
    have he := congrArg (fun t => t.1 (address i j) (address k l)) h
    simpa only [preview, follows, decide_eq_decide, p.post.host.injective.eq_iff, p'.post.host.injective.eq_iff] using he
  · intro i
    have he := congrArg (fun t => t.2 (address i none)) h
    simp only [preview, follows] at he
    exact he

variable {p p' v v'} (h : Agree p p' v v')

include h in
theorem Agree.symm : Agree p' p v' v := ⟨fun i j k l => (h.names i j k l).symm, fun i => (h.flags i).symm⟩

variable (full : D.full = true)

include full in
private theorem links (p : D.Encodes r G) (v w : G.V) :
    w ∈ G.N v ↔ ∃ j, p.post.nav v j = w ∧ (D.flags r (p.post.host v) j).1 = true := by
  have hh := p.edge v w
  simp only [Template.adj, full, ite_true, ← p.host_nav, p.post.host.injective.eq_iff] at hh
  exact hh

include h in
theorem Agree.code (i j l : Option (B d)) :
    (p.fullChart full).label (hop p v i) (hop p (hop p v j) l) =
      (p'.fullChart full).label (hop p' v' i) (hop p' (hop p' v' j) l) :=
  label_eq (h.names i none j l) (fun z => h.names i (some z) j l)

include h full in
theorem Agree.edge (i j l : Option (B d)) :
    hop p (hop p v j) l ∈ G.N (hop p v i) ↔ hop p' (hop p' v' j) l ∈ G'.N (hop p' v' i) := by
  rw [links full p, links full p', h.flags i]
  exact exists_congr fun k => and_congr_left' (h.names i (some k) j l)

include h in
theorem Agree.maps (i : Option (B d)) :
    (p.fullChart full).Maps (p'.fullChart full) (hop p v i) (hop p' v' i) := by
  intro t ht
  obtain ⟨j, rfl, _⟩ := (links full p _ _).mp ht
  exact ⟨_, (h.edge full i i (some j)).mp ht, h.code full i i (some j)⟩

include h in
theorem Agree.pair (i j : Option (B d)) :
    LocalPair (p.fullChart full) (p'.fullChart full) (hop p v i) (hop p v j) (hop p' v' i) (hop p' v' j) :=
  ⟨h.names i none j none, h.edge full i j none, h.code full i j none, h.maps full i, h.symm.maps full i⟩

include h in
theorem Agree.core (i j : Option (B d)) :
    hop p v j ∈ G.C (hop p v i) ↔ hop p' v' j ∈ G'.C (hop p' v' i) := by
  rw [p.core, p'.core, h.flags i]
  apply exists_congr
  intro k
  rw [← p.host_nav, ← p'.host_nav, p.post.host.injective.eq_iff, p'.post.host.injective.eq_iff]
  exact and_congr_left' (h.names i (some k) j none)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end
