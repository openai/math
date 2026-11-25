import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import OAI.LinearAlgebra.MatrixExponent.Packing.Reservations
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule
import OAI.LinearAlgebra.MatrixExponent.Diagram.Present
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Packing.Delivery

section
/-!
# Balanced binary trees gathering a fixed set of ports

Heap position zero is unused. The root has room for an outside
connection and each leaf can connect to a port.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing.Tree
open Finset

abbrev Node (w : ℕ) := Fin (2 ^ (Nat.clog 2 w + 1))

variable {w : ℕ}

def root (w : ℕ) : Node w := ⟨1, by
  have := Nat.one_le_pow (Nat.clog 2 w) 2 (by decide)
  rw [Nat.pow_succ]; omega⟩

def tip (j : Fin w) : Node w := ⟨2 ^ Nat.clog 2 w + j.val, by
  have := Nat.le_pow_clog (by decide : 1 < 2) w
  rw [Nat.pow_succ]; omega⟩

theorem tip_injective : Function.Injective (tip (w := w)) := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

theorem size (hw : 0 < w) : Fintype.card (Node w) ≤ 4 * w := by
  rw [Fintype.card_fin]
  by_cases he : w = 1
  · subst w; decide
  have h := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < w)
  rw [Nat.pred_eq_sub_one] at h
  have hp := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < w)
  rw [show Nat.clog 2 w + 1 = (Nat.clog 2 w - 1) + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ]
  omega

def climb (j : Fin w) (k : ℕ) : Node w :=
  ⟨(tip j).val / 2 ^ k, (Nat.div_le_self _ _).trans_lt (tip j).isLt⟩

@[simp] theorem climb_zero (j : Fin w) : climb j 0 = tip j := by ext; simp [climb]

@[simp] theorem climb_top (j : Fin w) : climb j (Nat.clog 2 w) = root w := by
  apply Fin.ext
  have h := Nat.le_pow_clog (by decide : 1 < 2) w
  unfold climb tip root
  simp only
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private theorem climb_step (j : Fin w) (k : ℕ) :
    (climb j (k + 1)).val = (climb j k).val / 2 := by
  simp only [climb, Nat.pow_succ, Nat.div_div_eq_div_mul]

private theorem below (j : Fin w) {k : ℕ} (hk : k < Nat.clog 2 w) : 1 < (climb j k).val := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hk)
  rw [Nat.pow_succ] at h
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 2))).mpr
  simp only [tip]
  omega

theorem climb_injective (j : Fin w) :
    Function.Injective (fun k : Fin (Nat.clog 2 w + 1) => climb j k.val) := by
  apply StrictAnti.injective
  intro a b hab
  have hh := below j (by omega : a.val < Nat.clog 2 w)
  change (climb j b.val).val < (climb j a.val).val
  refine lt_of_le_of_lt (b := (climb j (a.val + 1)).val) ?_ ?_
  · exact Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.pow_pos (by decide))
  · rw [climb_step]; omega

def adj (p : Node w) : Finset (Node w) := univ.filter fun q =>
  (1 < p.val ∧ q.val = p.val / 2) ∨ (1 < q.val ∧ p.val = q.val / 2)

theorem adj_symm {p q : Node w} (hq : q ∈ adj p) : p ∈ adj q := by
  simpa only [adj, mem_filter, mem_univ, true_and, or_comm] using hq

theorem climb_adj (j : Fin w) {k : ℕ} (hk : k < Nat.clog 2 w) :
    climb j (k + 1) ∈ adj (climb j k) := by
  exact mem_filter.mpr ⟨mem_univ _, .inl ⟨below j hk, climb_step j k⟩⟩

theorem degree (p : Node w) :
    (adj p).card + (if p = root w then 1 else 0) +
      (if 2 ^ Nat.clog 2 w ≤ p.val then 1 else 0) ≤ 3 := by
  let parents : Finset ℕ := if p = root w then ∅ else {p.val / 2}
  let children : Finset ℕ := if 2 ^ Nat.clog 2 w ≤ p.val then ∅ else {2 * p.val, 2 * p.val + 1}
  have sub : (adj p).image Fin.val ⊆ parents ∪ children := by
    rintro _ h
    obtain ⟨q, hq, rfl⟩ := mem_image.mp h
    rcases (mem_filter.mp hq).2 with ⟨hp, he⟩ | ⟨_, he⟩
    · have hn : p ≠ root w := by intro e; simp [e, root] at hp
      exact mem_union_left _ (by simp [parents, hn, he])
    · have hb : q.val < 2 ^ Nat.clog 2 w * 2 := q.isLt
      have hn : ¬2 ^ Nat.clog 2 w ≤ p.val := by omega
      apply mem_union_right
      simp only [children, ite_eq_right hn, mem_insert, mem_singleton]
      omega
  have hc := (card_le_card sub).trans (card_union_le parents children)
  rw [card_image_of_injective _ Fin.val_injective] at hc
  unfold parents children at hc
  have hb : ({2 * p.val, 2 * p.val + 1} : Finset ℕ).card ≤ 2 := card_le_two
  split_ifs at hc ⊢ <;> simp only [card_empty, card_singleton] at hc <;> omega

end OAI.LinearAlgebra.MatrixExponent.Packing.Tree
end

/-! # A fixed contact tree at each terminal -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Detour
open Finset
open scoped Classical

abbrev Hub (X : Type) (w : ℕ) := X ⊕ (X × Tree.Node w)

structure Switch (X : Type) (w : ℕ) where
  near : X → Finset X
  sym : ∀ x y, y ∈ near x → x ∈ near y
  pin : ∀ x, ↥(near x) ↪ Fin w

variable {X : Type} {w : ℕ}

def owner : Hub X w → X := Sum.elim id Prod.fst

def switch (N : X → Finset X) (sym : ∀ x y, y ∈ N x → x ∈ N y)
    (deg : ∀ x, (N x).card ≤ w) : Switch X w where
  near := N
  sym := sym
  pin x := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using deg x))

namespace Switch
variable [Fintype X] (sw : Switch X w)

private def links (x : X) (p : Tree.Node w) : Finset (X × Tree.Node w) :=
  univ.filter fun q => ∃ h : q.1 ∈ sw.near x,
    Tree.tip (sw.pin x ⟨q.1, h⟩) = p ∧ Tree.tip (sw.pin q.1 ⟨x, sw.sym _ _ h⟩) = q.2

private theorem links_card (x : X) (p : Tree.Node w) :
    (sw.links x p).card ≤ if 2 ^ Nat.clog 2 w ≤ p.val then 1 else 0 := by
  split_ifs with h
  · apply card_le_one.mpr
    rintro ⟨y, q⟩ hy ⟨z, r⟩ hz
    obtain ⟨_, h₁, h₂⟩ := (mem_filter.mp hy).2
    obtain ⟨_, h₃, h₄⟩ := (mem_filter.mp hz).2
    have he : y = z := congrArg Subtype.val ((sw.pin x).injective
      (Tree.tip_injective (h₁.trans h₃.symm)))
    subst z
    exact Prod.ext rfl (h₂.symm.trans h₄)
  · apply Nat.le_of_eq
    rw [card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨_, he, _⟩ := (mem_filter.mp hq).2
    apply h
    rw [← he]
    exact Nat.le_add_right _ _

def adj : Hub X w → Finset (Hub X w)
  | .inl x => {.inr (x, Tree.root w)}
  | .inr (x, p) =>
    ((Tree.adj p).image (fun q => .inr (x, q)) ∪ if p = Tree.root w then {.inl x} else ∅) ∪
      (sw.links x p).image Sum.inr

@[simp] theorem adj_outer (x : X) : sw.adj (.inl x) = {.inr (x, Tree.root w)} := rfl

theorem adj_inner (x : X) {p q : Tree.Node w} (h : q ∈ Tree.adj p) :
    Sum.inr (x, q) ∈ sw.adj (.inr (x, p)) :=
  mem_union_left _ (mem_union_left _ (mem_image_of_mem _ h))

theorem adj_bridge (x y : X) (h : y ∈ sw.near x) :
    Sum.inr (y, Tree.tip (sw.pin y ⟨x, sw.sym _ _ h⟩)) ∈
      sw.adj (.inr (x, Tree.tip (sw.pin x ⟨y, h⟩))) :=
  mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, h, rfl, rfl⟩))

theorem adj_symm (p q : Hub X w) (hq : q ∈ sw.adj p) : p ∈ sw.adj q := by
  rcases p with x | ⟨x, p⟩
  · have := mem_singleton.mp hq
    subst q
    simp [adj]
  rcases mem_union.mp hq with h | h
  · rcases mem_union.mp h with h | h
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp h
      exact sw.adj_inner x (Tree.adj_symm hr)
    · split_ifs at h with hp
      · rw [mem_singleton.mp h, hp]
        exact mem_singleton_self _
      · simp at h
  · obtain ⟨⟨y, r⟩, hy, rfl⟩ := mem_image.mp h
    obtain ⟨he, hp, hr⟩ := (mem_filter.mp hy).2
    change Tree.tip _ = r at hr
    rw [← hp, ← hr]
    exact sw.adj_bridge y x (sw.sym _ _ he)

theorem adj_degree (p : Hub X w) : (sw.adj p).card ≤ 3 := by
  rcases p with x | ⟨x, p⟩
  · simp
  refine le_trans ((card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) card_image_le))
    (le_trans ?_ (Tree.degree p))
  refine Nat.add_le_add (Nat.add_le_add card_image_le ?_) (sw.links_card _ _)
  split_ifs <;> simp

end Switch
end OAI.LinearAlgebra.MatrixExponent.Packing.Detour
end

/-!
# Bounded-degree host for tether restoration

Give each parked frozen member a private splitting tree. Its leaves
are outlets. The outlets and the old core use a common contact switch.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Tether
open Finset
open scoped Classical

abbrev End (V : Type) (r s : ℕ) := V ⊕ ((V × Fin r) × Tree.Node s)
abbrev Host (V : Type) (r s w : ℕ) := Detour.Hub (End V r s) w

variable {V : Type} {r s w : ℕ}

def core (v : V) : Host V r s w := .inl (.inl v)
def member (x : V × Fin r) : Host V r s w := .inl (.inr (x, Tree.root s))

def near (N : V → Finset V) (r s : ℕ) : End V r s → Finset (End V r s)
  | .inl v => ((N v ×ˢ univ) ×ˢ univ).image Sum.inr
  | .inr p => (N p.1.1).image Sum.inl

theorem near_symm (N : V → Finset V) (hn : ∀ v u, u ∈ N v → v ∈ N u)
    (v u : End V r s) (h : u ∈ near N r s v) : v ∈ near N r s u := by
  rcases v with v | ⟨⟨v, i⟩, j⟩ <;> rcases u with u | ⟨⟨u, k⟩, l⟩ <;>
    simp [near] at h ⊢ <;> exact hn _ _ h

def width (D r s : ℕ) := D * (r + 1) * 2 ^ (Nat.clog 2 s + 1)

theorem near_card (N : V → Finset V) (D : ℕ) (hd : ∀ v, (N v).card ≤ D) (v : End V r s) :
    (near N r s v).card ≤ width D r s := by
  cases v with
  | inl v =>
    refine card_image_le.trans ?_
    simp only [card_product, card_univ, Fintype.card_fin, width]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (hd v) (Nat.le_succ r))
  | inr v =>
    refine card_image_le.trans ((hd v.1.1).trans ?_)
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))

private def branches (C : V → Finset V) : End V r s → Finset (End V r s)
  | .inl v => (C v).image Sum.inl
  | .inr (x, p) => (Tree.adj p).image fun q => .inr (x, q)

private theorem branches_symm (C : V → Finset V) (hs : ∀ v u, u ∈ C v → v ∈ C u)
    (v u : End V r s) (he : u ∈ branches C v) : v ∈ branches C u := by
  rcases v with v | ⟨x, p⟩
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp he
    exact mem_image_of_mem _ (hs _ _ hu)
  · obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    exact mem_image_of_mem _ (Tree.adj_symm hq)

variable [Fintype V] (sw : Detour.Switch (End V r s) w) (C : V → Finset V)

def adj (z : Host V r s w) : Finset (Host V r s w) :=
  sw.adj z ∪ match z with
    | .inl x => (branches C x).image Sum.inl
    | .inr _ => ∅

theorem adj_symm (hs : ∀ v u, u ∈ C v → v ∈ C u) (z z' : Host V r s w)
    (h : z' ∈ adj sw C z) : z ∈ adj sw C z' := by
  rcases mem_union.mp h with h | h
  · exact mem_union_left _ (sw.adj_symm _ _ h)
  cases z with
  | inr _ => simp at h
  | inl x =>
    obtain ⟨y, hy, rfl⟩ := mem_image.mp h
    exact mem_union_right _ (mem_image_of_mem _ (branches_symm C hs _ _ hy))

theorem adj_degree (hC : ∀ v, (C v).card ≤ 3) (z : Host V r s w) :
    (adj sw C z).card ≤ 4 := by
  cases z with
  | inr v =>
    simpa only [adj, union_empty] using (sw.adj_degree (.inr v)).trans (by decide : 3 ≤ 4)
  | inl x =>
    have h : (branches C x).card ≤ 3 := by
      rcases x with v | ⟨u, p⟩
      · exact card_image_le.trans (hC v)
      · have := Tree.degree p
        exact card_image_le.trans (by omega)
    exact (card_union_le _ _).trans (Nat.add_le_add (by simp) (card_image_le.trans h))

theorem core_adj {v u : V} (hu : u ∈ C v) : core u ∈ adj sw C (core v) :=
  mem_union_right _ (mem_image_of_mem _ (mem_image_of_mem _ hu))

theorem branch_adj (x : V × Fin r) {p q : Tree.Node s} (hq : q ∈ Tree.adj p) :
    Sum.inl (.inr (x, q)) ∈ adj sw C (.inl (.inr (x, p))) :=
  mem_union_right _ (mem_image_of_mem _ (mem_image_of_mem _ hq))

theorem size : Fintype.card (Host V r s w) =
    Fintype.card V * (1 + r * 2 ^ (Nat.clog 2 s + 1)) * (1 + 2 ^ (Nat.clog 2 w + 1)) := by
  simp only [Host, Detour.Hub, End, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

end OAI.LinearAlgebra.MatrixExponent.Packing.Tether
end

/-! # One programmable trivalent permutation network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

/-- Exterior positions and the two ends of every internal edge. -/
abbrev RotorEnd (Y w : ℕ) (E : Type) := (Bool × Fin Y × Fin w) ⊕ E ⊕ E

/-- The graph and port locations are independent of the permutation. -/
structure Rotor (F : Type) [Field F] (Y w : ℕ) where
  V : Type
  E : Type
  [fv : Fintype V]
  [fe : Fintype E]
  pos : RotorEnd Y w E → V
  degree : ∀ v, Fintype.card {q // pos q = v} ≤ 3
  packet : ∀ σ : Equiv.Perm (Fin Y), Spectral.Packet F
    (fun p : Fin Y × Fin w => (pos (.inl (false, p)), pos (.inl (true, σ p.1, p.2))))
    (fun _ : Unit => fun e : E => (pos (.inr (.inl e)), pos (.inr (.inr e))))

attribute [instance] Rotor.fv Rotor.fe

namespace Rotor
variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w)

def port (side : Bool) (i : Fin Y) (j : Fin w) : R.V := R.pos (.inl (side, i, j))

def edge (e : R.E) : R.V × R.V := (R.pos (.inr (.inl e)), R.pos (.inr (.inr e)))

/-- Fix the tags of a single permutation verifier, without adding vertices. -/
theorem of_tag {k m : ℕ}
    (h : Net F (Tagged.inputs k (word w)) .unit (Tagged.tag F k (word w)) m) :
    ∃ R : Rotor F (2 ^ k) w, Fintype.card R.V = m ∧ 2 * Fintype.card R.E ≤ 3 * m := by
  obtain ⟨G, eval, tri, size⟩ := h.diagram
  obtain ⟨p, prog⟩ := tag_program F k w
  let embed : RotorEnd (2 ^ k) w G.E → G.End
    | .inl q => .inl (.inl (p q))
    | .inr (.inl e) => .inl (.inr e)
    | .inr (.inr e) => .inr (.inr e)
  have inj : Function.Injective embed := by
    rintro (q | e | e) (z | f | f) he <;> simp [embed] at he ⊢ <;> exact he
  let pos := G.station ∘ embed
  have degree (v : G.V) : Fintype.card {q // pos q = v} ≤ 3 := by
    let f : {q // pos q = v} → {e // G.station e = v} := fun q => ⟨embed q.val, q.property⟩
    have hi : Function.Injective f := fun _ _ he => Subtype.ext (inj (congrArg Subtype.val he))
    exact (Fintype.card_le_of_injective f hi).trans ((G.degree v).le.trans (tri v))
  have packet (σ : Equiv.Perm (Fin (2 ^ k))) : Spectral.Packet F
      (fun t : Fin (2 ^ k) × Fin w => (pos (.inl (false, t)), pos (.inl (true, σ t.1, t.2))))
      (fun _ : Unit => fun e : G.E => (pos (.inr (.inl e)), pos (.inr (.inr e)))) := by
    obtain ⟨cfg, local_cfg, exact_cfg⟩ := prog σ
    refine ⟨fun _ v x y z => G.vertex (cfg x y) () z v, ?_, ?_⟩
    · intro _ v x y z x' y' z' hx hy hz
      apply G.local_weight
      · rintro (i | e) hi
        · exact local_cfg x y x' y' i (fun t ht => hx t (by simpa [pos, embed, ht, Diagram.station] using hi))
            (fun t ht => hy t (by simpa [pos, embed, ht, Diagram.station] using hi))
        · exact hz e (.inl hi)
      · rintro (i | e) hi
        · exact i.elim
        · exact hz e (.inr hi)
    · intro x y
      rw [Fintype.sum_unique]
      change _ = G.eval (cfg x y) ()
      rw [eval, exact_cfg]
  refine ⟨⟨G.V, G.E, pos, degree, packet⟩, size, ?_⟩
  have := G.cost_trivalent tri
  rw [G.cost_eq, size] at this
  change 2 * Fintype.card G.E ≤ 3 * m
  omega

end Rotor
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Deploying simultaneous permutation layers

All copies use the same hardware. Each active port has
its own wire along the paths joining the terminals to the programmed
network. Both ends of unused port are pinned.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
open Spectral
open scoped Classical

variable {F : Type} [Field F] {Y w n : ℕ} (R : Rotor F Y w)

abbrev Hardware := R.V ⊕ (Bool × Fin Y × Tree.Node w)

def root (t : Bool) (i : Fin Y) : R.Hardware := .inr (t, i, Tree.root w)

/-- Walk from a network port to its gathering-tree root. -/
def walk (t : Bool) (i : Fin Y) (j : Fin w) : ℕ → R.Hardware
  | 0 => .inl (R.port t i j)
  | k + 1 => .inr (t, i, Tree.climb j k)

@[simp] theorem walk_top (t : Bool) (i : Fin Y) (j : Fin w) :
    R.walk t i j (Nat.clog 2 w + 1) = R.root t i := by simp [walk, root]

variable {A : Type} [Fintype A]

abbrev PathEdge (w : ℕ) (A : Type) := Fin (Nat.clog 2 w + 1) × A
abbrev LayerEdge (n : ℕ) := Σ _ : Fin n, R.E
abbrev Supply (A : Type) (n : ℕ) := PathEdge w A ⊕ R.LayerEdge n ⊕ PathEdge w A

def pathEdge (t : Bool) (p : A → Fin Y) (lane : A → Fin n × Fin w)
    (e : PathEdge w A) : R.Hardware × R.Hardware :=
  let f := R.walk t (p e.2) (lane e.2).2
  (f e.1.val, f (e.1.val + 1))

def layerEdge (e : R.LayerEdge n) : R.Hardware × R.Hardware :=
  (.inl (R.edge e.2).1, .inl (R.edge e.2).2)

def supply (p q : A → Fin Y) (lane : A → Fin n × Fin w) :
    R.Supply A n → R.Hardware × R.Hardware :=
  Sum.elim (R.pathEdge false p lane) (Sum.elim R.layerEdge (R.pathEdge true q lane))

def layerRule (p q : A → Fin Y) (σ : Fin n → Equiv.Perm (Fin Y))
    (lane : A → Fin n × Fin w)
    (inj : Function.Injective (fun a => (p a, lane a)))
    (route : ∀ a, σ (lane a).1 (p a) = q a) :
    Packet.Rule F (fun a : A =>
      (R.walk false (p a) (lane a).2 0, R.walk true (q a) (lane a).2 0))
      (fun _ : Unit => R.layerEdge (n := n)) := by
  let embed (a : A) : Σ _ : Fin n, Fin Y × Fin w :=
    ⟨(lane a).1, p a, (lane a).2⟩
  have he : Function.Injective embed := by
    intro a b hab
    simp only [embed, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at hab
    exact inj (Prod.ext hab.2.1 (Prod.ext hab.1 hab.2.2))
  let h := Packet.Rule.parallel_one (fun t : Fin n => (R.packet (σ t)).rule)
  have h' := (h.select ⟨embed, he⟩).place (fun t => (Sum.inl t.2 : R.Hardware))
  refine h'.congr ?_ rfl
  funext i
  simp only [Packet.parallelDemand, Function.Embedding.coeFn_mk, embed, route, walk, port]

def treeRule (p : A → Fin Y) (lane : A → Fin n × Fin w) (t : Bool) :
    Packet.Rule F (fun a : A => (R.walk t (p a) (lane a).2 0, R.root t (p a)))
      (fun _ : Unit => R.pathEdge t p lane) := by
  let hp := Packet.Rule.path F (fun k (a : A) => R.walk t (p a) (lane a).2 k)
    (Nat.clog 2 w + 1)
  exact hp.congr (by simp only [walk_top]) rfl

/-- Each named unit is carried from its input terminal to its assigned
output terminal by an exact one-term packet. -/
def deployRule (p q : A → Fin Y) (σ : Fin n → Equiv.Perm (Fin Y))
    (lane : A → Fin n × Fin w)
    (inj : Function.Injective (fun a => (p a, lane a)))
    (route : ∀ a, σ (lane a).1 (p a) = q a) :
    Packet.Rule F (fun a : A => (R.root false (p a), R.root true (q a)))
      (fun _ : Unit => R.supply p q lane) :=
  (R.treeRule p lane false).reverse.series
    ((R.layerRule p q σ lane inj route).series (R.treeRule q lane true))

end OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
end

/-!
# Common support of a rotor and its gathering trees

The support leaves one free connection at every root. It does not
depend on the demand, layer count, port assignment or permutation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
open Finset
open scoped Classical

variable {F : Type} [Field F] {Y w n : ℕ} (R : Rotor F Y w)

private def opposite : RotorEnd Y w R.E → R.Hardware
  | .inl (t, i, j) => .inr (t, i, Tree.tip j)
  | .inr (.inl e) => .inl (R.edge e).2
  | .inr (.inr e) => .inl (R.edge e).1

def support : R.Hardware → Finset R.Hardware
  | .inl v => (univ.filter fun e => R.pos e = v).image R.opposite
  | .inr (t, i, p) =>
    ((Tree.adj p).image fun q => Sum.inr (t, i, q)) ∪
    ((univ.filter fun j => Tree.tip j = p).image fun j => Sum.inl (R.port t i j))

private theorem neighbor (e : RotorEnd Y w R.E) : R.opposite e ∈ R.support (.inl (R.pos e)) :=
  mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩

theorem support_symm {v u : R.Hardware} (hu : u ∈ R.support v) : v ∈ R.support u := by
  rcases v with v | ⟨t, i, p⟩
  · obtain ⟨e, he, rfl⟩ := mem_image.mp hu
    have h := (mem_filter.mp he).2
    subst v
    rcases e with ⟨t, i, j⟩ | e | e
    · exact mem_union_right _ (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩)
    · exact R.neighbor (.inr (.inr e))
    · exact R.neighbor (.inr (.inl e))
  · rcases mem_union.mp hu with h | h
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp h
      exact mem_union_left _ (mem_image.mpr ⟨p, Tree.adj_symm hq, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
      rw [← (mem_filter.mp hj).2]
      exact R.neighbor (.inl (t, i, j))

theorem support_degree (v : R.Hardware) :
    (R.support v).card + (if ∃ t i, v = R.root t i then 1 else 0) ≤ 3 := by
  rcases v with v | ⟨t, i, p⟩
  · have hn : ¬∃ t i, Sum.inl v = R.root t i := by simp [root]
    rw [ite_eq_right hn, add_zero]
    exact card_image_le.trans ((Fintype.card_subtype _).ge.trans (R.degree v))
  · have ht : (univ.filter fun j => Tree.tip j = p).card ≤
        if 2 ^ Nat.clog 2 w ≤ p.val then 1 else 0 := by
      split_ifs with h
      · exact card_le_one.mpr fun a ha b hb =>
          Tree.tip_injective ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
      · have h' (j : Fin w) : Tree.tip j ≠ p := by
          intro e
          rw [← e] at h
          exact h (Nat.le_add_right _ _)
        simp [h']
    have hr : (∃ b j, Sum.inr (t, i, p) = R.root b j) ↔ p = Tree.root w := by simp [root]
    have hc : (R.support (.inr (t, i, p))).card ≤
        (Tree.adj p).card + (univ.filter fun j => Tree.tip j = p).card :=
      (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
    simp only [hr]
    have := Tree.degree p
    omega

theorem size (hw : 0 < w) : Fintype.card R.Hardware ≤ Fintype.card R.V + 8 * Y * w := by
  simp only [Hardware, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  have h := Tree.size hw
  rw [Fintype.card_fin] at h
  have := Nat.mul_le_mul_left (2 * Y) h
  nlinarith

variable {A : Type} (p q : A → Fin Y) (lane : A → Fin n × Fin w)

private theorem path_mem (t : Bool) (e : PathEdge w A) :
    (R.pathEdge t p lane e).2 ∈ R.support (R.pathEdge t p lane e).1 := by
  obtain ⟨⟨k, hk⟩, a⟩ := e
  cases k with
  | zero =>
    simpa [pathEdge, walk, port, opposite] using R.neighbor (.inl (t, p a, (lane a).2))
  | succ k =>
    exact mem_union_left _ (mem_image.mpr ⟨_, Tree.climb_adj (lane a).2 (by omega), rfl⟩)

theorem supply_mem (e : R.Supply A n) :
    (R.supply p q lane e).2 ∈ R.support (R.supply p q lane e).1 := by
  rcases e with e | e | e
  · exact R.path_mem p lane false e
  · exact R.neighbor (.inr (.inl e.2))
  · exact R.path_mem q lane true e

theorem supply_card [Fintype A] :
    Fintype.card (R.Supply A n) =
      n * Fintype.card R.E + 2 * (Nat.clog 2 w + 1) * Fintype.card A := by
  simp [Supply, LayerEdge, PathEdge, Fintype.card_sigma]
  ring

end OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
end

/-! # Realizing the good contacts by permutation networks and direct links -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
open Spectral
open scoped Classical

variable {P U X W F : Type} [Fintype P] [Field F]
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ} {Y w : ℕ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u) (R : Rotor F Y w)

def source (q : {i // good i}) (t : Bool) : X × R.Hardware :=
  (leaf (point q.val t), R.root false (d.terminal (point q.val t)))

def target (q : {i // good i}) (t : Bool) : X × R.Hardware :=
  ((d.plug q t).1, R.root true (d.plug q t).2)

def inputAt (x : X) (e : GoodEnd leaf point good x) := d.terminal (point e.val.1.val e.val.2)

def outputAt (x : X) (e : GoodEnd leaf point good x) :=
  out x (portOf leaf point good edge outLeaf cap Y d.agree d.slot e)

abbrev LocalWires (x : X) := R.Supply (GoodEnd leaf point good x) (d.layers x)
abbrev Wires := (Σ x, d.LocalWires R x) ⊕ {q // good q}

def inside (e : Σ x, d.LocalWires R x) : (X × R.Hardware) × (X × R.Hardware) :=
  let z := R.supply (d.inputAt e.1) (d.outputAt e.1) (d.lane e.1) e.2
  ((e.1, z.1), (e.1, z.2))

def supply : d.Wires R → (X × R.Hardware) × (X × R.Hardware) :=
  Sum.elim (d.inside R) (fun q => (d.target R q false, d.target R q true))

/-- All hardware and direct links for a group stay in that group. -/
theorem same_group {I : Type} (g : X → I)
    (h : ∀ q, good q → g (leaf (point q false)) = g (leaf (point q true)))
    (e : d.Wires R) : g (d.supply R e).1.1 = g (d.supply R e).2.1 := by
  cases e with
  | inl _ => rfl
  | inr q => exact h q.val q.property

variable [Fintype X] [Fintype U]

/-- The direct wire joins matching reserved outputs. Its internal bit
is summed exactly once, leaving equality on the two input terminals. -/
def deployRule :
    Packet.Rule F (fun q => (d.source R q false, d.source R q true))
      (fun _ : Unit => d.supply R) := by
  have each (x : X) :=
    R.deployRule (d.inputAt x) (d.outputAt x) (d.config x) (d.lane x) (d.input x) (d.routes x)
  let e : {q // good q} × Bool ≃ Σ x, GoodEnd leaf point good x :=
    (Equiv.sigmaFiberEquiv (fun q : {i // good i} × Bool => leaf (point q.1.val q.2))).symm
  have hp := ((Packet.Rule.parallel_one each).place (fun q => (q.1, q.2))).select e.toEmbedding
  have hq : Packet.Rule F (fun q : {i // good i} × Bool => (d.source R q.1 q.2, d.target R q.1 q.2))
      (fun _ : Unit => d.inside R) := hp
  exact hq.join_outputs

end OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
end

/-! # Degree-three support shared by all good contacts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {Z F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w)

namespace Rotor

/-- Attach the predetermined cross-base links at output terminals. -/
def net (p : Z × Fin Y → Z × Fin Y) (v : Z × R.Hardware) : Finset (Z × R.Hardware) :=
  ((R.support v.2).image (Prod.mk v.1)) ∪
    ((univ.filter (fun i => v.2 = R.root true i)).image (fun i =>
      ((p (v.1, i)).1, R.root true (p (v.1, i)).2)))

theorem mem_net (p : Z × Fin Y → Z × Fin Y) (v u : Z × R.Hardware) :
    u ∈ R.net p v ↔ (u.1 = v.1 ∧ u.2 ∈ R.support v.2) ∨
      ∃ i, v.2 = R.root true i ∧ u = ((p (v.1, i)).1, R.root true (p (v.1, i)).2) := by
  obtain ⟨z, a⟩ := u
  simp only [net, mem_union, mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  aesop

theorem net_symm (p : Z × Fin Y → Z × Fin Y) (hp : Function.Involutive p)
    {v u : Z × R.Hardware} (he : u ∈ R.net p v) : v ∈ R.net p u := by
  rw [mem_net] at he ⊢
  rcases he with ⟨hs, he⟩ | ⟨i, hi, rfl⟩
  · exact .inl ⟨hs.symm, R.support_symm he⟩
  · refine .inr ⟨(p (v.1, i)).2, rfl, ?_⟩
    simp only [Prod.mk.eta, hp (v.1, i)]
    exact Prod.ext rfl hi

/-- One connection at every input remains available for the exceptional
contacts, even if some outputs have no active good links. -/
theorem net_degree (p : Z × Fin Y → Z × Fin Y) (v : Z × R.Hardware) :
    (R.net p v).card + (if ∃ i, v.2 = R.root false i then 1 else 0) ≤ 3 := by
  have hd := R.support_degree v.2
  have he : (R.net p v).card ≤ (R.support v.2).card +
      (univ.filter fun i => v.2 = R.root true i).card :=
    (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
  by_cases h : ∃ t i, v.2 = R.root t i
  · rw [ite_eq_left h] at hd
    obtain ⟨t, i, hi⟩ := h
    cases t <;> simp [hi, root, filter_eq] at he hd ⊢ <;> omega
  · have hn t i : v.2 ≠ R.root t i := fun h' => h ⟨t, i, h'⟩
    simp [hn] at he hd ⊢
    exact he.trans hd

end Rotor

variable {P U X W : Type} [Fintype P]
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u)

/-- Project the absolute group coordinates onto common hardware slots. -/
theorem Delivery.supply_mem (g : X → Z) (p : Z × Fin Y → Z × Fin Y)
    (links : ∀ q, p (Prod.map g id (d.plug q false)) = Prod.map g id (d.plug q true))
    (e : d.Wires R) :
    Prod.map g id (d.supply R e).2 ∈ R.net p (Prod.map g id (d.supply R e).1) := by
  rw [R.mem_net]
  rcases e with ⟨x, e⟩ | q
  · exact .inl ⟨rfl, R.supply_mem (d.inputAt x) (d.outputAt x) (d.lane x) e⟩
  · refine .inr ⟨(d.plug q false).2, rfl, ?_⟩
    exact congrArg (fun a : Z × Fin Y => (a.1, R.root true a.2)) (links q).symm

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Attaching the contact trees to the rotor

Common core support consists of three parts. Each site has one rotor
and its gathering trees. Each output terminal has at most one direct
link, and each input terminal has one contact tree for exceptional traffic.
The full support adds tether connections at the input terminals.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
open Finset
open scoped Classical

variable {F X : Type} [Field F] {Y w L : ℕ} (R : Rotor F Y w)

abbrev Host (X : Type) (L : ℕ) := (X × R.Hardware) ⊕ ((X × Fin Y) × Tree.Node L)

def input (p : X × Fin Y) : R.Host X L := .inl (p.1, R.root false p.2)

theorem input_injective : Function.Injective (R.input (X := X) (L := L)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ he
  simpa [input, root] using he

def hub : Detour.Hub (X × Fin Y) L → R.Host X L := Sum.elim R.input Sum.inr

theorem hub_injective : Function.Injective (R.hub (X := X) (L := L)) := by
  rintro (p|p) (q|q) he
  · exact congrArg Sum.inl (R.input_injective he)
  · cases he
  · cases he
  · exact congrArg Sum.inr (Sum.inr.inj he)

variable [Fintype X] (sw : Detour.Switch (X × Fin Y) L) (mate : X × Fin Y → X × Fin Y)

def links : R.Host X L → Finset (R.Host X L)
  | .inl v => (R.net mate v).image Sum.inl ∪
      ((univ.filter fun i => v.2 = R.root false i).image
        fun i => Sum.inr ((v.1, i), Tree.root L))
  | .inr v => (sw.adj (.inr v)).image R.hub

theorem links_net {v z : X × R.Hardware} (hz : z ∈ R.net mate v) :
    .inl z ∈ R.links sw mate (.inl v) := mem_union_left _ (mem_image_of_mem _ hz)

theorem links_detour {v z : Detour.Hub (X × Fin Y) L} (hz : z ∈ sw.adj v) :
    R.hub z ∈ R.links sw mate (R.hub v) := by
  cases v with
  | inl v =>
    have he := mem_singleton.mp hz
    subst z
    exact mem_union_right _ (mem_image.mpr ⟨v.2, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩)
  | inr v => exact mem_image_of_mem _ hz

theorem links_symm (hm : Function.Involutive mate) (v z : R.Host X L)
    (hz : z ∈ R.links sw mate v) : v ∈ R.links sw mate z := by
  cases v with
  | inl v =>
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
      exact R.links_net sw mate (R.net_symm mate hm hq)
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      have he : v = (v.1, R.root false i) := Prod.ext rfl (mem_filter.mp hi).2
      rw [he]
      exact R.links_detour sw mate (sw.adj_symm (.inl (v.1, i)) (.inr ((v.1, i), Tree.root L))
        (mem_singleton_self _))
  | inr v =>
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    exact R.links_detour sw mate (sw.adj_symm _ _ hq)

theorem links_degree (v : R.Host X L) : (R.links sw mate v).card ≤ 3 := by
  cases v with
  | inl v =>
    have ha : (R.links sw mate (.inl v)).card ≤ (R.net mate v).card +
        (univ.filter fun i => v.2 = R.root false i).card :=
      (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
    have hb := R.net_degree mate v
    by_cases hi : ∃ i, v.2 = R.root false i
    · rw [ite_eq_left hi] at hb
      obtain ⟨i, hi⟩ := hi
      simp [hi, root, filter_eq] at ha
      exact ha.trans hb
    · have hn i : v.2 ≠ R.root false i := fun he => hi ⟨i, he⟩
      simp [hn] at ha hb
      exact ha.trans hb
  | inr v => exact card_image_le.trans (sw.adj_degree _)

variable (N : X × Fin Y → Finset (X × Fin Y))

def full (v : R.Host X L) : Finset (R.Host X L) :=
  R.links sw mate v ∪ if hv : ∃ x, R.input x = v then (N hv.choose).image R.input else ∅

theorem links_sub (v : R.Host X L) : R.links sw mate v ⊆ R.full sw mate N v := subset_union_left

theorem input_full {x y} (hy : y ∈ N x) : R.input y ∈ R.full sw mate N (R.input x) := by
  have hv : ∃ z, R.input (L := L) z = R.input x := ⟨x, rfl⟩
  rw [full, dite_eq_left hv, R.input_injective hv.choose_spec]
  exact mem_union_right _ (mem_image_of_mem _ hy)

theorem full_symm (hm : Function.Involutive mate) (sym : ∀ x y, y ∈ N x → x ∈ N y)
    (v z : R.Host X L) (hz : z ∈ R.full sw mate N v) : v ∈ R.full sw mate N z := by
  rcases mem_union.mp hz with hh | hh
  · exact R.links_sub sw mate N z (R.links_symm sw mate hm _ _ hh)
  · split_ifs at hh with hv
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hh
      exact hv.choose_spec ▸ R.input_full sw mate N (sym _ _ hq)
    · simp at hh

theorem full_degree {D : ℕ} (bound : ∀ x, (N x).card ≤ D) (v : R.Host X L) :
    (R.full sw mate N v).card ≤ 3 + D := by
  apply (card_union_le _ _).trans (Nat.add_le_add (R.links_degree sw mate v) ?_)
  split_ifs
  · exact card_image_le.trans (bound _)
  · simp

end OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
end

/-! # Wire cost of all permutation layers and their direct links -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
open Finset
open scoped Classical

variable {P U X W F : Type} [Fintype P] [Fintype U] [Field F]
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ} {Y w : ℕ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u) (R : Rotor F Y w)

theorem card_ends (x : X) : Fintype.card (GoodEnd leaf point good x) ≤ d.layers x * Y * w := by
  simpa [mul_assoc, mul_left_comm] using Fintype.card_le_of_injective _ (d.input x)

variable [Fintype X]

/-- Charge a direct link to its first endpoint. Unused sites incur no
cost. All units are measured relative to the base budget. -/
theorem width_le (c : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hR : (Fintype.card R.E : ℝ) ≤ c * Y * w)
    (s : Finset X) (hs : ∀ q, good q → ∀ t, leaf (point q t) ∈ s) :
    (Fintype.card (d.Wires R) : ℝ) * u ≤
      10 * (c + 2 * (Nat.clog 2 w + 1) + 1) * s.card := by
  let A := GoodEnd leaf point good
  let cost (x : X) := Fintype.card (d.LocalWires R x) + Fintype.card (A x)
  have links : Fintype.card {q // good q} ≤ ∑ x, Fintype.card (A x) := by
    let e := Equiv.sigmaFiberEquiv (fun q : {i // good i} × Bool => leaf (point q.1.val q.2))
    rw [← Fintype.card_sigma, Fintype.card_congr e, Fintype.card_prod, Fintype.card_bool]
    omega
  have total : Fintype.card (d.Wires R) ≤ ∑ x ∈ s, cost x := by
    rw [sum_subset (subset_univ s)]
    · simp only [Wires, Fintype.card_sum, Fintype.card_sigma, cost, sum_add_distrib]
      exact Nat.add_le_add_left links _
    · intro x _ hx
      have hempty : IsEmpty (A x) := ⟨fun q => hx (q.property ▸ hs q.val.1.val q.val.1.property q.val.2)⟩
      have h0 : Fintype.card (A x) = 0 := Fintype.card_eq_zero
      simp [cost, LocalWires, R.supply_card, d.empty x hempty, A] at h0 ⊢
  have localCost (x : X) : (cost x : ℝ) * u ≤ 10 * (c + 2 * (Nat.clog 2 w + 1) + 1) := by
    have hA : (Fintype.card (A x) : ℝ) * u ≤ 10 := calc
      _ ≤ (d.layers x : ℝ) * Y * w * u := mul_le_mul_of_nonneg_right (by exact_mod_cast d.card_ends x) hu
      _ ≤ _ := d.cost x
    have hE : (d.layers x : ℝ) * Fintype.card R.E * u ≤ c * 10 := calc
      _ ≤ (d.layers x : ℝ) * (c * Y * w) * u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)) hu
      _ = c * ((d.layers x : ℝ) * Y * w * u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (d.cost x) hc
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * (Nat.clog 2 w + 1))
    simp only [cost, LocalWires, R.supply_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linarith
  calc
    _ ≤ (∑ x ∈ s, (cost x : ℝ)) * u := mul_le_mul_of_nonneg_right (by exact_mod_cast total) hu
    _ ≤ _ := by
      rw [sum_mul]
      simpa only [sum_const, nsmul_eq_mul, mul_comm] using sum_le_sum (fun x (_ : x ∈ s) => localCost x)

end OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
end
