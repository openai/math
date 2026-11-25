import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule
import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation
import OAI.LinearAlgebra.MatrixExponent.Packing.TetherHost
import OAI.LinearAlgebra.MatrixExponent.Packing.RestoreCost
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection

section
/-!
# The result of resetting a host

Group-prefixed endpoints keep distinct blocks independent. The common
host contains both core links and possible tethers. Width is measured
in the same unit before and after the reset.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

variable {V U : Type} [Fintype V] [Fintype U] {h : ℕ}

structure ResetResult (F : Type) [Field F] (a : ℕ) (N : V → Finset V)
    (src dst : U → V) (ix : U → Cell h) (l : V → Cell h → ℝ)
    (u B W : ℝ) (H D : ℕ) where
  vertex : Type
  wire : Type
  [fv : Fintype vertex]
  [fw : Fintype wire]
  core : vertex → Finset vertex
  full : vertex → Finset vertex
  core_symm : ∀ v w, w ∈ core v → v ∈ core w
  full_symm : ∀ v w, w ∈ full v → v ∈ full w
  sub : ∀ v, core v ⊆ full v
  core_degree : ∀ v, (core v).card ≤ 3
  full_degree : ∀ v, (full v).card ≤ D
  positions : Fintype.card vertex ≤ H * 2 ^ (h - a) * Fintype.card V
  le : a ≤ h
  mix : Cell h ≃ₗ[ZMod 2] Cell h
  owner : V × Cell h → Cell a × vertex
  origin : vertex → V
  uniform : ∃ (Y : Type) (_ : Fintype Y) (e : vertex ≃ V × Y), ∀ t, (e t).1 = origin t
  group : ∀ p, (owner p).1 = ancestor le (mix p.2)
  origin_owner : ∀ p, origin (owner p).2 = p.1
  tether : ∀ v z, z ∈ N v → ∀ x, (owner (z, x)).2 ∈ full (owner (v, x)).2
  supply : wire → (Cell a × vertex) × (Cell a × vertex)
  support : ∀ e, (supply e).1.1 = (supply e).2.1 ∧ (supply e).2.2 ∈ core (supply e).1.2
  active : ∀ e t, ∃ q, src q = origin (cond t (supply e).2 (supply e).1).2 ∨
    dst q = origin (cond t (supply e).2 (supply e).1).2
  rule : Spectral.Packet.Rule F (fun i => (owner (src i, ix i), owner (dst i, ix i)))
    (fun _ : Unit => supply)
  cost : Fintype.card wire * u ≤ W * (Fintype.card V * (2 : ℝ) ^ a * B + ∑ v, ∑ x, l v x)
  load : ∀ p, push owner (Function.uncurry l) p + degree supply p * u ≤ 89 * B

attribute [instance] ResetResult.fv ResetResult.fw

/-- Undo the normalization by a single base's capacity. -/
noncomputable def ResetResult.unscale {F : Type} [Field F] {a H D : ℕ} {N : V → Finset V}
    {src dst : U → V} {ix : U → Cell h} {l : V → Cell h → ℝ} {u B W : ℝ} (hb : 0 < B)
    (G : ResetResult F a N src dst ix (fun v x => l v x / B) (u / B) 1 W H D) :
    ResetResult F a N src dst ix l u B W H D := by
  refine { G with cost := ?_, load := ?_ }
  · have hc := G.cost
    simp only [mul_one, ← Finset.sum_div] at hc
    calc
      _ = (Fintype.card G.wire : ℝ) * (u / B) * B := by field_simp
      _ ≤ _ := (mul_le_mul_of_nonneg_right hc hb.le).trans_eq (by field_simp)
  · intro p
    have hc := G.load p
    rw [show Function.uncurry (fun v x => l v x / B) = fun p => Function.uncurry l p / B from rfl,
      push_div, ← mul_div_assoc, ← add_div, mul_one, div_le_iff₀ hb] at hc
    exact hc

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# The reset as an exact wire packet

Good contacts use the fixed reserved links. Exceptional ones have their
own paths in the contact trees. All sites project to a group and a slot
in the common trivalent host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Schedule

open Finset
open scoped Classical

variable {V A U F : Type} [Fintype V] [Fintype U] [Field F] {h a k Y w L : ℕ}
variable {T : Demands V A U h} {N : V → Finset V} {d : V → V → ℕ}
variable {l : V → Cell h → ℝ} {u g ε : ℝ}
variable (Z : Schedule T N d a k l u g ε) {o : Z.Plugs Y}
variable (D : Z.Dispatch o w) (R : Rotor F Y w)

-- Freeze the same finite enumeration as the delivery packet.
instance {P U' X W : Type} [Fintype P] [Fintype X] [Fintype U']
    {leaf : P → X} {point : U' → Bool → P} {good : U' → Prop}
    {edge : U' → W} {outLeaf : W → Bool → X} {cap : W → ℝ}
    {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l' : P → ℝ}
    (p : Delivery leaf point good edge outLeaf cap Y w out l' u) :
    Fintype (p.Wires R) := inferInstance

abbrev Space (V : Type) (h a L : ℕ) := R.Host (Site V (h - a)) L

def terminal (p : V × Cell h) := ((Z.leaf p).drop a, D.terminal p)

def owner (p : V × Cell h) : Cell a × Space R V h a L :=
  (Z.group p.2, R.input (Z.terminal D p))

def mainPlace (x : Site V h × R.Hardware) : Cell a × Space R V h a L :=
  (x.1.group a, Sum.inl (x.1.drop a, x.2))

def treePlace (x : Cell a × Detour.Hub (Site V (h - a) × Fin Y) L) : Cell a × Space R V h a L :=
  (x.1, R.hub x.2)

theorem place_source (q : {i // Z.good i}) (t : Bool) :
    mainPlace R (D.source R q t) = Z.owner (L := L) D R (T.point q.val t) := by
  exact Prod.ext (Z.group_end _ t) rfl

variable (sw : Detour.Switch (Site V (h - a) × Fin Y) L)
variable (ok : ∀ i : U, Z.terminal D (T.point i true) ∈ sw.near (Z.terminal D (T.point i false)))

abbrev Exceptional := {i : U // ¬Z.good i}
abbrev Wires := D.Wires R ⊕ (Fin (Detour.steps L) × Z.Exceptional)

def treeRoute := sw.route (fun i : Z.Exceptional => Z.group (T.ix i.val))
  (fun i t => Z.terminal D (T.point i.val t)) (fun i => ok i.val)

def supply : Z.Wires (L := L) D R → (Cell a × Space R V h a L) × (Cell a × Space R V h a L) :=
  Sum.elim (fun e => Prod.map (mainPlace R) (mainPlace R) (D.supply R e))
    (fun e => Prod.map (treePlace R) (treePlace R) (Z.treeRoute D sw ok e))

def rule :
    Spectral.Packet.Rule F (fun i => (Z.owner D R (T.point i false), Z.owner D R (T.point i true)))
      (fun _ : Unit => Z.supply D R sw ok) := by
  have hf := D.deployRule R
  have hp := hf.place (mainPlace (V := V) (h := h) (a := a) (L := L) R)
  apply Spectral.Packet.Rule.partition Z.good
  · exact hp.congr (by simp only [Z.place_source]) rfl
  · exact (sw.rule (fun i : Z.Exceptional => Z.group (T.ix i.val))
      (fun i t => Z.terminal D (T.point i.val t)) (fun i => ok i.val) F).place (treePlace R)

theorem supported (e : Z.Wires (L := L) D R) :
    let z := Z.supply D R sw ok e
    z.1.1 = z.2.1 ∧ z.2.2 ∈ R.links sw (peer o) z.1.2 := by
  cases e with
  | inl e =>
    refine ⟨D.same_group R (Site.group a) (fun i _ => ?_) e, R.links_net sw _ ?_⟩
    · rw [Z.group_end, Z.group_end]
    · exact D.supply_mem R (Site.drop a) (peer o) (fun q => D.peer_relative q false) e
  | inr e =>
    have ha := sw.route_adj (fun i : Z.Exceptional => Z.group (T.ix i.val))
      (fun i t => Z.terminal D (T.point i.val t)) (fun i => ok i.val) e
    exact ⟨ha.1, R.links_detour sw _ ha.2⟩

end OAI.LinearAlgebra.MatrixExponent.Packing.Schedule
end

/-! # Incidence budget on the permutation hardware -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

private theorem add_degree {S A B : Type} [Fintype A] [Fintype B]
    (f : A → S × S) (g : B → S × S) (v : S) :
    degree (Sum.elim f g) v = degree f v + degree g v := by
  rw [degree_sum, degree_sum, degree_sum, Fintype.sum_sum_type]
  rfl

variable {F : Type} [Field F] {Y w n : ℕ} (R : Rotor F Y w)

namespace Rotor

private theorem walk_inj (t : Bool) (i : Fin Y) (j : Fin w) {k l : ℕ}
    (hk : k ≤ Nat.clog 2 w + 1) (hl : l ≤ Nat.clog 2 w + 1)
    (he : R.walk t i j k = R.walk t i j l) : k = l := by
  cases k <;> cases l
  · rfl
  · cases he
  · cases he
  · rename_i k l
    have eq : Tree.climb j k = Tree.climb j l := by simpa [walk] using he
    exact congrArg (fun a => a.val + 1)
      (Tree.climb_injective j (a₁ := ⟨k, by omega⟩) (a₂ := ⟨l, by omega⟩) eq)

private theorem layer_degree (v : R.Hardware) :
    Packing.degree (R.layerEdge (n := n)) v ≤ 3 * n := by
  rw [degree_sum, Fintype.sum_sigma]
  calc
    _ ≤ ∑ _i : Fin n, 3 := by
      apply sum_le_sum
      intro i _
      rcases v with v | v
      · have ht : (∑ e, if R.pos e = v then 1 else 0) ≤ 3 := by
          simpa only [sum_boole, Nat.cast_id, Fintype.card_subtype] using R.degree v
        simp only [Fintype.sum_sum_type] at ht
        simp only [arityCost, layerEdge, edge, Sum.inl.injEq, sum_add_distrib]
        omega
      · simp [arityCost, layerEdge]
    _ = _ := by simp [mul_comm]

variable {A : Type} [Fintype A] (p q : A → Fin Y) (lane : A → Fin n × Fin w)

/-- A path visits each vertex at most once, hence contributes at most
two incidences there. -/
private theorem path_degree (t : Bool) (v : R.Hardware) :
    Packing.degree (R.pathEdge t p lane) v ≤ 2 * Fintype.card A := by
  let : DecidableEq R.Hardware := Classical.typeDecidableEq _
  have once (a : A) (k : ℕ) (hk : k ≤ 1) :
      (∑ j : Fin (Nat.clog 2 w + 1), if R.walk t (p a) (lane a).2 (j.val + k) = v then 1 else 0) ≤ 1 := by
    rw [sum_boole, Nat.cast_id]
    apply card_le_one.mpr
    intro i hi j hj
    have he := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
    exact Fin.ext (Nat.add_right_cancel (R.walk_inj _ _ _ (by omega) (by omega) he))
  rw [degree_sum, Fintype.sum_prod_type, sum_comm]
  calc
    _ ≤ ∑ _a : A, 2 := by
      refine sum_le_sum fun a _ => ?_
      simp only [arityCost, pathEdge, sum_add_distrib]
      exact Nat.add_le_add (once a 0 (by decide)) (once a 1 le_rfl)
    _ = _ := by simp [mul_comm]

theorem supply_degree (v : R.Hardware) :
    Packing.degree (R.supply p q lane) v ≤ 3 * n + 4 * Fintype.card A := by
  rw [supply, add_degree, add_degree]
  have := R.layer_degree (n := n) v
  have := R.path_degree p lane false v
  have := R.path_degree q lane true v
  omega

end Rotor

namespace Delivery

variable {P U X W : Type} [Fintype P] [Fintype U] [Fintype X]
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u)

private theorem degree_inside (x : X) (v : R.Hardware) :
    degree (d.inside R) (x, v) = degree (R.supply (d.inputAt x) (d.outputAt x) (d.lane x)) v := by
  let : DecidableEq R.Hardware := Classical.typeDecidableEq _
  rw [degree_sum, degree_sum, Fintype.sum_sigma, sum_eq_single x]
  · simp only [inside, arityCost, Prod.mk.injEq, true_and]
    exact sum_congr rfl (fun _ _ => by congr 1)
  · intro y _ hy
    simp [inside, arityCost, hy]
  · simp

omit [Fintype X] in
private theorem degree_links (x : X) (v : R.Hardware) :
    degree (fun q => (d.target R q false, d.target R q true)) (x, v) ≤
      Fintype.card (GoodEnd leaf point good x) := by
  let : DecidableEq (X × R.Hardware) := Classical.typeDecidableEq _
  have hb : (∑ q : {i // good i}, ∑ t : Bool, if leaf (point q.val t) = x then 1 else 0) =
      Fintype.card (GoodEnd leaf point good x) := by
    rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  have h (q : {i // good i}) (t : Bool) :
      (if d.target R q t = (x, v) then 1 else 0) ≤ if leaf (point q.val t) = x then 1 else 0 := by
    by_cases ht : d.target R q t = (x, v)
    · have he : leaf (point q.val t) = x := congrArg Prod.fst ht
      simp [he, ht]
    · simp [ht]
  rw [degree_sum, ← hb]
  apply sum_le_sum
  intro q _
  rw [Fintype.sum_bool, add_comm]
  unfold arityCost
  exact Nat.add_le_add (h q false) (h q true)

/-- Bound both endpoints of all supply wires on each absolute host site.
This includes repeated incidences and both ends of a loop. -/
theorem incidence (hY : 0 < Y) (hw : 0 < w) (x : X × R.Hardware) :
    degree (d.supply R) x ≤ 8 * (d.layers x.1 * Y * w) := by
  obtain ⟨x, v⟩ := x
  rw [supply, add_degree, degree_inside]
  have hi := R.supply_degree (d.inputAt x) (d.outputAt x) (d.lane x) v
  have hd := degree_links R d x v
  have he := d.card_ends x
  have hl : d.layers x ≤ d.layers x * Y * w :=
    (Nat.le_mul_of_pos_right _ hY).trans (Nat.le_mul_of_pos_right _ hw)
  change _ ≤ 8 * (d.layers x * Y * w)
  omega

end Delivery
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Per-site bounds on loads and wires in the reset packet -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Schedule

open Finset
open scoped Classical

variable {V A U F : Type} [Fintype V] [Fintype U] [Field F] {h a k Y w L : ℕ}
variable {T : Demands V A U h} {N : V → Finset V} {d : V → V → ℕ}
variable {l : V → Cell h → ℝ} {u g ε : ℝ}
variable (Z : Schedule T N d a k l u g ε) {o : Z.Plugs Y}
variable (D : Z.Dispatch o w) (R : Rotor F Y w)

private def dest (p : V × Cell h) := (Z.group p.2, Z.terminal D p)

private theorem leaf_of_dest {p q : V × Cell h} (e : Z.dest D p = Z.dest D q) :
    Z.leaf p = Z.leaf q := by
  apply Site.group_drop (Z.leaf_depth p) (Z.leaf_depth q)
  · rw [Z.leaf_group, Z.leaf_group]
    exact congrArg Prod.fst e
  · exact congrArg (fun z => z.2.1) e

private theorem leaf_bound {X : Type} (f : V × Cell h → X)
    (he : ∀ p q, f p = f q → Z.leaf p = Z.leaf q) (x : X) :
    push f (Function.uncurry l) x ≤ 3 := by
  by_cases h : ∃ p, f p = x
  · obtain ⟨p, rfl⟩ := h
    refine le_trans ?_ ((Z.at_leaf (Z.leaf p)).trans (by norm_num))
    unfold push
    apply sum_le_sum
    intro q _
    by_cases hc : f q = f p
    · rw [ite_eq_left hc, ite_eq_left (he _ _ hc)]
    · rw [ite_eq_right hc]
      split_ifs <;> first | exact (Z.sizes _ _).1 | exact le_rfl
  · push Not at h
    simp [push, h]

theorem owner_load (p : Cell a × Space R V h a L) :
    push (Z.owner D R) (Function.uncurry l) p ≤ 3 := by
  apply Z.leaf_bound
  intro q r he
  apply Z.leaf_of_dest D
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
  exact Prod.ext h₁ (R.input_injective h₂)

private theorem core_load (z : Cell a × (Site V (h - a) × Fin Y)) :
    degree (fun i => (Z.dest D (T.point i false), Z.dest D (T.point i true))) z * u ≤ 3 := by
  rw [degree_push (fun i t => Z.dest D (T.point i t))]
  change push (Z.dest D ∘ Function.uncurry T.point) _ _ ≤ _
  rw [← push_comp]
  exact (push_le_push (Z.dest D) (fun p => Z.mass p.1 p.2) z).trans
    (Z.leaf_bound _ (fun _ _ => Z.leaf_of_dest D) z)

private theorem main_degree (hY : 0 < Y) (hw : 0 < w) (z : Cell a × Space R V h a L) :
    degree (fun e => Prod.map (mainPlace R) (mainPlace R) (D.supply R e)) z * u ≤ 80 := by
  apply degree_le_map (D.supply R) (mainPlace R) (fun x => a ≤ x.1.depth) u 80 (by norm_num)
  · intro x
    have cost {i n : ℕ} (hi : i ≤ 8 * (n * Y * w)) (hn : (n : ℝ) * Y * w * u ≤ 10) :
        (i : ℝ) * u ≤ 80 := by
      have hc : (i : ℝ) ≤ 8 * ((n : ℝ) * Y * w) := by exact_mod_cast hi
      linarith only [mul_le_mul_of_nonneg_right hc Z.width.le, hn]
    exact cost (D.incidence R hY hw x) (D.cost x.1)
  · intro x hx
    have hempty : IsEmpty (GoodEnd Z.leaf T.point Z.good x.1) :=
      ⟨fun p => hx (p.property ▸ Z.leaf_depth _)⟩
    simpa only [D.empty x.1 hempty, zero_mul, mul_zero, Nat.le_zero] using D.incidence R hY hw x
  · intro x hx y hy he
    obtain ⟨hg, he'⟩ := Prod.mk.inj he
    obtain ⟨hd, hr⟩ := Prod.mk.inj (Sum.inl.inj he')
    exact Prod.ext (Site.group_drop hx hy hg hd) hr

variable (sw : Detour.Switch (Site V (h - a) × Fin Y) L)
variable (ok : ∀ i : U, Z.terminal D (T.point i true) ∈ sw.near (Z.terminal D (T.point i false)))

private theorem tree_degree (z : Cell a × Space R V h a L) :
    degree (fun e => Prod.map (treePlace R) (treePlace R) (Z.treeRoute D sw ok e)) z * u ≤ 6 := by
  apply degree_le_map _ _ (fun _ => True) _ _ (by norm_num)
  · intro p
    let v := (p.1, Detour.owner p.2)
    let f i := (Z.dest D (T.point i false), Z.dest D (T.point i true))
    let e : Z.Exceptional ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
    have ht : degree (Z.treeRoute D sw ok) p ≤ 2 * degree (f ∘ e) v :=
      sw.route_degree (fun i : Z.Exceptional => Z.group (T.ix i.val))
        (fun i t => Z.terminal D (T.point i.val t)) (fun i => ok i.val) p
    have hi : (degree (Z.treeRoute D sw ok) p : ℝ) ≤ 2 * degree f v := by
      exact_mod_cast ht.trans (Nat.mul_le_mul_left 2 (degree_select f e v))
    have hc : degree f v * u ≤ 3 := Z.core_load D v
    linarith only [mul_le_mul_of_nonneg_right hi Z.width.le, hc]
  · simp
  · intro x _ y _ he
    obtain ⟨hg, hx⟩ := Prod.mk.inj he
    exact Prod.ext hg (R.hub_injective hx)

theorem incidence (hY : 0 < Y) (hw : 0 < w) (p : Cell a × Space R V h a L) :
    degree (Z.supply D R sw ok) p * u ≤ 86 := by
  rw [supply, degree_partition, Nat.cast_add, add_mul]
  linarith only [Z.main_degree D R hY hw p, Z.tree_degree D R sw ok p]

def origin : Space R V h a L → V :=
  Sum.elim (fun z => z.1.1) (fun z => z.1.1.1)

/-- No core wiring is introduced at a frozen host position. -/
theorem active (e : Z.Wires (L := L) D R) (t : Bool) :
    ∃ q b, (T.point q b).1 =
      origin R (cond t (Z.supply D R sw ok e).2 (Z.supply D R sw ok e).1).2 := by
  rcases e with (⟨x, e⟩ | q) | ⟨i, q⟩
  · have hn : Nonempty (GoodEnd Z.leaf T.point Z.good x) := by
      rcases e with e | e | e
      · exact ⟨e.2⟩
      · by_contra h
        have he := D.empty x (not_nonempty_iff.mp h)
        have := e.1.isLt
        omega
      · exact ⟨e.2⟩
    obtain ⟨p⟩ := hn
    have hp := congrArg Prod.fst p.property
    refine ⟨p.val.1.val, p.val.2, ?_⟩
    cases t <;> exact hp
  · exact ⟨q.val, t, by cases t <;> rfl⟩
  · have hub (s : Detour.Hub (Site V (h - a) × Fin Y) L) :
        origin R (R.hub s) = (Detour.owner s).1.1 := by cases s <;> rfl
    have path (n : ℕ) :
        ∃ b, (T.point q.val b).1 = origin R (R.hub (sw.path (ok q.val) n)) := by
      rw [hub, sw.path_owner]
      split_ifs
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    refine ⟨q.val, ?_⟩
    cases t
    · exact path i.val
    · exact path (i.val + 1)

end OAI.LinearAlgebra.MatrixExponent.Packing.Schedule
end

/-! # Total core width after the degree reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Schedule

open Finset
open scoped Classical

variable {V A U F : Type} [Fintype V] [Fintype U] [Field F] {h a k Y w L : ℕ}
variable {T : Demands V A U h} {N : V → Finset V} {d : V → V → ℕ}
variable {l : V → Cell h → ℝ} {u g ε : ℝ}
variable (Z : Schedule T N d a k l u g ε) {o : Z.Plugs Y}
variable (D : Z.Dispatch o w) (R : Rotor F Y w)

/-- Width is measured relative to the capacity of one base. -/
theorem total_cost (c : ℝ) (hc : 0 ≤ c) (hR : (Fintype.card R.E : ℝ) ≤ c * Y * w)
    (he : Detour.steps L * ε ≤ 1) :
    (Fintype.card (Z.Wires (L := L) D R) : ℝ) * u ≤
      (40 * (c + 2 * (Nat.clog 2 w + 1) + 1) + 1) *
        (Fintype.card V * (2 : ℝ) ^ a + ∑ v, ∑ x, l v x) := by
  let A := (univ : Finset (Σ v, Cell (Z.base v))).image (baseSite Z.base Z.depth)
  have act i (hi : Z.good i) t : Z.leaf (T.point i t) ∈ A := by
    rw [Z.routes i hi t]
    exact mem_image_of_mem _ (mem_univ _)
  let M := ∑ v, ∑ x, l v x
  have hM : 0 ≤ M := sum_nonneg fun v _ => sum_nonneg fun x _ => (Z.sizes v x).1
  let X := Fintype.card V * (2 : ℝ) ^ a
  have hX : 0 ≤ X := by unfold X; positivity
  have count : (A.card : ℝ) ≤ 4 * (X + M) := calc
    _ ≤ (Fintype.card (Σ v, Cell (Z.base v)) : ℝ) := Nat.cast_le.mpr card_image_le
    _ ≤ 2 * X + 4 * M := by
      simp only [Fintype.card_sigma, card_cell, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
      simpa only [X, M, mul_assoc] using Z.count
    _ ≤ _ := by linarith
  let C : ℝ := c + 2 * (Nat.clog 2 w + 1) + 1
  have hC : 0 ≤ C := by unfold C; positivity
  have hr : (Fintype.card (D.Wires R) : ℝ) * u ≤ 40 * C * (X + M) := calc
    _ ≤ 10 * C * A.card := D.width_le R c hc Z.width.le hR A act
    _ ≤ 10 * C * (4 * (X + M)) := mul_le_mul_of_nonneg_left count (by positivity)
    _ = _ := by ring
  have ex : (Fintype.card Z.Exceptional : ℝ) * u ≤ ε * M := by
    have hy := Z.exceptional
    unfold Exceptional
    rw [Fintype.card_subtype, ← nsmul_eq_mul, ← sum_const, sum_filter]
    simpa only [ite_not] using hy
  have hd : (Detour.steps L : ℝ) * (Fintype.card Z.Exceptional : ℝ) * u ≤ X + M := calc
    _ ≤ (Detour.steps L : ℝ) * (ε * M) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ex (by positivity)
    _ ≤ M := by rw [← mul_assoc]; exact mul_le_of_le_one_left hM he
    _ ≤ X + M := le_add_of_nonneg_left hX
  change _ ≤ (40 * C + 1) * (X + M)
  unfold Wires
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, add_mul]
  linarith

end OAI.LinearAlgebra.MatrixExponent.Packing.Schedule
end

/-!
# Resetting the core degree

The rotor and the core degree determine the depth, load and position
overheads. The full degree, which counts tethers, enters only the bound
on the new full degree. Every core demand is transmitted exactly.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {F V U : Type} [Field F] [Fintype V] [Fintype U] {Y w Δ D h a k : ℕ}

def resetWidth (c : ℝ) (w : ℕ) := 40 * (c + 2 * (Nat.clog 2 w + 1) + 1) + 1

def resetPositions (R : Rotor F Y w) (Δ : ℕ) :=
  2 * (Fintype.card R.Hardware + Y * Fintype.card (Tree.Node (terminalWidth Δ Y)))

abbrev Schedule.Address (h : ℕ) := Σ i : Fin (h + 1), Cell i.val

def Schedule.splitHost (R : Rotor F Y w) (a h L : ℕ) :
    Schedule.Space R V h a L ≃ V × R.Host (Schedule.Address (h - a)) L where
  toFun
    | .inl ((v, j), z) => (v, .inl (j, z))
    | .inr (((v, j), t), r) => (v, .inr ((j, t), r))
  invFun
    | (v, .inl (j, z)) => .inl ((v, j), z)
    | (v, .inr ((j, t), r)) => .inr (((v, j), t), r)
  left_inv := by rintro (x|y) <;> rfl
  right_inv := by rintro ⟨v, x|y⟩ <;> rfl

private theorem size_limit (R : Rotor F Y w) :
    Fintype.card (Schedule.Space R V h a (terminalWidth Δ Y)) ≤
      resetPositions R Δ * 2 ^ (h - a) * Fintype.card V := by
  unfold Schedule.Space Rotor.Host
  unfold resetPositions
  calc
    _ = Fintype.card (Site V (h - a)) *
        (Fintype.card R.Hardware + Y * Fintype.card (Tree.Node (terminalWidth Δ Y))) := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      ring
    _ ≤ (2 * 2 ^ (h - a) * Fintype.card V) *
        (Fintype.card R.Hardware + Y * Fintype.card (Tree.Node (terminalWidth Δ Y))) :=
      Nat.mul_le_mul_right _ (Site.card _ _)
    _ = _ := by ring

def Schedule.result {N C : V → Finset V} {src dst : U → V} {ix : U → Cell h}
    {edge : ∀ i, dst i ∈ C (src i)} {l : V → Cell h → ℝ} {u g ε : ℝ}
    (Z : Schedule (coreDemands ix edge) N (resetDelay C Δ D) a k l u g ε)
    {o : Z.Plugs Y} (q : Z.Dispatch o w) (R : Rotor F Y w) (hY : 0 < Y) (hw : 0 < w)
    (hΔ : 0 < Δ) (hD : Δ ≤ D)
    (ns : ∀ v z, z ∈ N v → v ∈ N z) (cs : ∀ v z, z ∈ C v → v ∈ C z)
    (sub : ∀ v, C v ⊆ N v) (ndeg : ∀ v, (N v).card ≤ D)
    (pin : ∀ x : Site V (h - a) × Fin Y, ↥(terminalNear C Δ Y x) ↪ Fin (terminalWidth Δ Y))
    (c : ℝ) (hc : 0 ≤ c) (hR : (Fintype.card R.E : ℝ) ≤ c * Y * w)
    (he : Detour.steps (terminalWidth Δ Y) * ε ≤ 1) :
    ResetResult F a N src dst ix l u 1 (resetWidth c w)
      (resetPositions R Δ) (3 + terminalWidth D Y) := by
  let L := terminalWidth Δ Y
  let sw : Detour.Switch (Site V (h - a) × Fin Y) L :=
    ⟨terminalNear C Δ Y, terminal_symm cs _ _, pin⟩
  have ok (i : U) : Z.terminal q (dst i, ix i) ∈ sw.near (Z.terminal q (src i, ix i)) :=
    mem_product.mpr ⟨Z.leaf_near cs sub (fun _ _ he => by simp [he]) (edge i) (ix i), mem_univ _⟩
  let A := terminalNear (h := h - a) N D Y
  refine {
    vertex := Schedule.Space R V h a L
    wire := Z.Wires (L := L) q R
    core := R.links sw (peer o)
    full := R.full sw (peer o) A
    core_symm := R.links_symm sw _ (peer_involutive o)
    full_symm := R.full_symm sw _ _ (peer_involutive o) (terminal_symm ns _ _)
    sub := R.links_sub sw _ _
    core_degree := R.links_degree sw _
    full_degree := R.full_degree sw _ _ (terminal_card _ _ _ (hΔ.trans_le hD) ndeg)
    positions := size_limit R
    le := (Nat.le_add_right _ _).trans Z.block
    mix := Z.π
    owner := Z.owner q R
    origin := Schedule.origin R
    uniform := ⟨_, inferInstance, Schedule.splitHost R a h L, by rintro (x|y) <;> rfl⟩
    group := fun _ => rfl
    origin_owner := fun _ => rfl
    tether := ?_
    supply := Z.supply q R sw ok
    support := Z.supported q R sw ok
    active := ?_
    rule := Z.rule q R sw ok
    cost := ?_
    load := ?_ }
  · intro v z hz x
    apply R.input_full
    exact mem_product.mpr ⟨Z.leaf_near ns (fun _ => subset_rfl)
      (fun _ _ _ => by split_ifs <;> omega) hz x, mem_univ _⟩
  · intro e t
    obtain ⟨i, b, hb⟩ := Z.active q R sw ok e t
    cases b
    · exact ⟨i, .inl hb⟩
    · exact ⟨i, .inr hb⟩
  · rw [mul_one]
    exact Z.total_cost q R c hc hR he
  · intro p
    have lo := Z.owner_load q R p
    have hi := Z.incidence q R sw ok hY hw p
    linarith

/-- A trivalent rotor of width `w` resets arbitrarily many independent
graphs on a common host. The cutoff for the group length is independent
of the number of frozen neighbors. -/
theorem reset_exists (hY : 0 < Y) (hw : 0 < w)
    (hΔ : 0 < Δ) (enough : 4 * coreBins Δ ≤ Y)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ k, Y ^ 2 * w ≤ 2 ^ k ∧
    ∀ (F : Type) [Field F] (R : Rotor F Y w), (Fintype.card R.E : ℝ) ≤ c * Y * w →
    ∀ (V U : Type) [Fintype V] [Fintype U] (h a D : ℕ), a + k ≤ h → Δ ≤ D →
    ∀ (N C : V → Finset V) (src dst : U → V) (ix : U → Cell h) (edge : ∀ i, dst i ∈ C (src i)),
    (∀ v z, z ∈ N v → v ∈ N z) → (∀ v z, z ∈ C v → v ∈ C z) →
    (∀ v, C v ⊆ N v) → (∀ v, (N v).card ≤ D) → (∀ v, (C v).card ≤ Δ) →
    ∀ (l : V → Cell h → ℝ) (u B : ℝ), (∀ v x, 0 ≤ l v x ∧ l v x ≤ B) →
    0 < u → u ≤ B → (∀ v x, (coreDemands ix edge).incident u v x ≤ l v x) →
    Nonempty (ResetResult F a N src dst ix l u ((2 : ℝ) ^ k * B) (resetWidth c w)
      (resetPositions R Δ) (3 + terminalWidth D Y)) := by
  let L := Detour.steps (terminalWidth Δ Y)
  have hL : 0 < (L : ℝ) := by unfold L Detour.steps; positivity
  obtain ⟨k, hk, ex⟩ := core_schedule Y w Δ (1 / L) hY hw hΔ (by positivity) enough
  refine ⟨k, hk, ?_⟩
  intro F _ R hR V U _ _ h a D ha hD N C src dst ix edge ns cs sub ndeg cdeg l u B hl hu ub mass
  let S := (2 : ℝ) ^ k * B
  have hB : 0 < B := hu.trans_le ub
  have hS : 0 < S := by unfold S; positivity
  have hs : B / S = 1 / (2 : ℝ) ^ k := by unfold S; field_simp
  have hl' v x : 0 ≤ l v x / S ∧ l v x / S ≤ 1 / (2 : ℝ) ^ k :=
    ⟨div_nonneg (hl v x).1 hS.le, (div_le_div_of_nonneg_right (hl v x).2 hS.le).trans_eq hs⟩
  have hi v x : (coreDemands ix edge).incident (u / S) v x ≤ l v x / S := by
    unfold Demands.incident
    rw [push_div]
    exact div_le_div_of_nonneg_right (mass v x) hS.le
  obtain ⟨Z, o, ⟨q⟩⟩ := ex V U h a D ha hD N C src dst ix edge ns cs sub ndeg cdeg
    _ _ hl' (div_pos hu hS) ((div_le_div_of_nonneg_right ub hS.le).trans_eq hs) hi
  have he : (L : ℝ) * (1 / L) ≤ 1 := by simp [hL.ne']
  let sw := Detour.switch (terminalNear (h := h - a) C Δ Y)
    (terminal_symm cs _ _) (terminal_card _ _ _ hΔ cdeg)
  let Q := Z.result q R hY hw hΔ hD ns cs sub ndeg sw.pin c hc hR he
  exact ⟨Q.unscale hS⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Applying a reset to a core diagram

All exterior ports, including tether ends, remain separately named.
Only crossing supplies survive, still bundled in the original unit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.ResetResult

open Finset Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {x y : Wire} {a h u D H : ℕ}
  {src dst : E → V} {ix : E → Cell h} {N : V → Finset V} {l : V → Cell h → ℝ} {B W : ℝ}
  (q : ResetResult F a N src dst ix l u B W H D)
  {G : Diagram F x y} (s : Bundles G src dst ix u)

def assign (_ : Unit) (v : G.V) := q.owner (s.place v)

private abbrev raw := (q.rule.bundle u).reindex s.bits

private def demand (e : G.E) :=
  (q.owner (src (s.bits e).1, ix (s.bits e).1), q.owner (dst (s.bits e).1, ix (s.bits e).1))

private theorem aligned : G.Aligned (q.assign s) (fun _ => id) (q.demand s) := by
  intro _ e
  exact ⟨congrArg q.owner (s.left e), congrArg q.owner (s.right e)⟩

abbrev contract := G.replaced (q.raw s) (q.assign s) (fun _ => id) ()

theorem eval_contract (p : Val x) (r : Val y) : (q.contract s).eval p r = G.eval p r := by
  simpa only [Fintype.sum_unique] using G.eval_replaced (q.raw s) (q.assign s) (fun _ => id) p r

abbrev Survivors := {e : q.wire // (q.supply e).1 ≠ (q.supply e).2}

private def crossingIndex :
    q.Survivors × Fin u ≃
      Diagram.Cut (W := fun _ : Unit => fun z : q.wire × Fin u => q.supply z.1) (fun _ => id) () where
  toFun e := ⟨(e.1.val, e.2), e.1.property⟩
  invFun e := (⟨e.val.1, e.property⟩, e.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

def remaining : q.Survivors × Fin u ≃ (q.contract s).E :=
  q.crossingIndex.trans (G.cutEdges (q.raw s) (q.assign s) (fun _ => id) (q.aligned s) ())

def bundles : Bundles (q.contract s) (fun e : q.Survivors => (q.supply e.val).1.2)
    (fun e => (q.supply e.val).2.2) (fun e => (q.supply e.val).1.1) u where
  place := Prod.swap
  bits := (q.remaining s).symm
  left e := by
    obtain ⟨p, rfl⟩ := (q.remaining s).surjective e
    rw [Equiv.symm_apply_apply]
    rfl
  right e := by
    obtain ⟨p, rfl⟩ := (q.remaining s).surjective e
    rw [Equiv.symm_apply_apply, (q.support _).1]
    rfl

theorem cost_contract :
    (Fintype.card (q.contract s).E : ℝ) ≤ W * (Fintype.card V * (2 : ℝ) ^ a * B + ∑ v, ∑ x, l v x) := by
  rw [← Fintype.card_congr (q.remaining s), Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _))
    (Nat.cast_nonneg _)).trans q.cost

theorem arity_contract (he : ∀ p, (exterior G s.place p : ℝ) ≤ l p.1 p.2)
    (p : Cell a × q.vertex) : ((q.contract s).arity p : ℝ) ≤ 89 * B := by
  have hb := G.arity_replaced (q.raw s) (q.assign s) (fun _ => id) (q.aligned s) () p
  change (q.contract s).arity p ≤ exterior G (q.owner ∘ s.place) p +
    degree (fun i : q.wire × Fin u => q.supply i.1) p at hb
  rw [degree_bundle] at hb
  refine (Nat.cast_le.mpr hb).trans (le_trans ?_ (q.load p))
  rw [Nat.cast_add, Nat.cast_mul, exterior_comp]
  exact add_le_add_left (push_le_push q.owner he p) _

end OAI.LinearAlgebra.MatrixExponent.Packing.ResetResult
end

/-! # Degree reset on a common host with frozen tensors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

open Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {h u a : ℕ}
  {L : Fringe x y T} (G : HostNet F L h u)

section Transform
variable {B W : ℝ} {H D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B W H D)

private theorem moved (p : slots x ⊕ slots y) :
    (q.bundles G.units).place (portEnd (q.contract G.units) p) =
      (q.owner (G.units.place (portEnd G.diagram p))).swap := by
  cases p <;> rfl

def afterReset : HostNet F L a u where
  diagram := q.contract G.units
  V := q.vertex
  E := q.Survivors
  src e := (q.supply e.val).1.2
  dst e := (q.supply e.val).2.2
  ix e := (q.supply e.val).1.1
  units := q.bundles G.units
  past := G.carried (Prod.swap ∘ q.owner)
  park := Prod.swap ∘ q.owner ∘ G.park
  frozen := G.frozen ∘ q.origin
  N := q.full
  C := q.core
  ns := q.full_symm
  cs := q.core_symm
  sub := q.sub
  kept t := by
    dsimp only [Function.comp_apply, Prod.fst_swap]
    rw [q.origin_owner]
    exact G.kept t
  core e := by
    have hs t : ¬ G.frozen (q.origin (cond t (q.supply e.val).2 (q.supply e.val).1).2) := by
      obtain ⟨i, he|he⟩ := q.active e.val t
      · exact he ▸ (G.core i).1
      · exact he ▸ (G.core i).2
    exact ⟨hs false, hs true⟩
  edge e := (q.support e.val).2
  tether t := by
    rw [G.moved q t]
    let p := G.units.place (portEnd G.diagram t)
    let z := G.park (L.tensor t)
    change ¬G.frozen (q.origin (q.owner p).2) ∧ (q.owner p).1 = (q.owner z).1 ∧
      (q.owner z).2 ∈ q.full (q.owner p).2
    obtain ⟨hf, hi, he⟩ := G.tether t
    change p.2 = z.2 at hi
    rw [q.origin_owner, q.group, q.group, hi]
    refine ⟨hf, rfl, ?_⟩
    have ht := q.tether p.1 z.1 he p.2
    rw [show (z.1, p.2) = z by rw [hi]] at ht
    exact ht

theorem reset_load (v : q.vertex) (i : Cell a) :
    (G.afterReset q).load v i ≤ 89 * B := by
  let Q := G.afterReset q
  let f := Prod.swap ∘ q.owner
  have hm := G.reassign Q f rfl (G.moved q) rfl (v, i)
  have hp : push f (Function.uncurry G.load) (v, i) = push q.owner (Function.uncurry G.load) (i, v) := by
    apply sum_congr rfl
    intro j _
    simp [f, Prod.ext_iff, and_comm]
  have hd : degree Q.pair (v, i) ≤ degree q.supply (i, v) := by
    let e : Q.E ↪ q.wire := Function.Embedding.subtype _
    refine le_trans ?_ (degree_select q.supply e (i, v))
    rw [degree_sum, degree_sum]
    apply sum_le_sum
    intro t _
    have he := (q.support (e t)).1
    change arityCost (v, i)
      (((q.supply (e t)).1.2, (q.supply (e t)).1.1),
       ((q.supply (e t)).2.2, (q.supply (e t)).1.1)) ≤ arityCost (i, v) (q.supply (e t))
    simp [arityCost, Prod.ext_iff, and_comm, he]
  exact hm.trans ((add_le_add hp.le (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd)
    (Nat.cast_nonneg _))).trans (q.load (i, v)))

theorem afterReset_spec {σ : ℝ} (width : 0 ≤ W)
    (slack : B * (Fintype.card G.V * 2 ^ a : ℕ) ≤ σ) :
    (G.afterReset q).Bounded 3 D (89 * B) ∧ (G.afterReset q).X ≤ W * (σ + 2 * G.X + 2 * L.Z) ∧
      G.Preserves (G.afterReset q) ∧ (G.afterReset q).mass = G.mass + 2 * G.X ∧
      G.Tracks (G.afterReset q) (H + 1) := by
  obtain ⟨S, _, β, hβ⟩ := q.uniform
  refine ⟨⟨q.core_degree, q.full_degree, G.reset_load q⟩, ?_,
    ⟨Prod.swap ∘ q.owner, rfl, G.moved q, ⟨(prefixMap q.le).comp q.mix.toLinearMap,
      (prefixMap_onto q.le).comp q.mix.surjective, q.group⟩,
      S, inferInstance, β, fun t => (hβ _).trans (q.origin_owner (G.park t))⟩, G.carry_sum (Prod.swap ∘ q.owner), ?_⟩
  · have hs : (Fintype.card G.V : ℝ) * 2 ^ a * B ≤ σ := by
      rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] at slack
    change ((Fintype.card q.Survivors * u : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _))
      (Nat.cast_nonneg _)).trans (q.cost.trans ?_)
    exact mul_le_mul_of_nonneg_left (by linarith only [hs, G.sum_load]) width

  · have hpos : 0 < H + 1 := by omega
    have ht : G.Tracks (G.afterReset q) (1 * (H + 1)) := by
      refine tracks_of_slots β (fun v => {v}) (by simp [eq_comm]) (by simp) hpos
        (q.positions.trans (by gcongr; omega)) ?_
      intro j
      rw [mem_singleton]
      exact (hβ _).trans ((congrArg (fun p => q.origin p.1) (G.moved q j)).trans
        (q.origin_owner _))
    simpa only [one_mul] using ht

end Transform

/-- Reset all groups using one choice of common links and a single rotor. -/
theorem reset {Y w Δ : ℕ} (hY : 0 < Y) (hw : 0 < w)
    (hΔ : 0 < Δ) (enough : 4 * coreBins Δ ≤ Y)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ k, ∀ (F : Type) [Field F] (R : Rotor F Y w), (Fintype.card R.E : ℝ) ≤ c * Y * w →
      ∀ (T : Type) [Fintype T] (x y : Wire) (L : Fringe x y T)
      (h a u D : ℕ) (B σ : ℝ) (G : HostNet F L h u),
      a + k ≤ h → Δ ≤ D → G.Bounded Δ D B → 0 < u → u ≤ B →
      (2 : ℝ) ^ k * B * (Fintype.card G.V * 2 ^ a : ℕ) ≤ σ →
      ∃ Q : HostNet F L a u,
        (∀ x y, Q.diagram.eval x y = G.diagram.eval x y) ∧
        Fintype.card Q.V ≤ resetPositions R Δ * 2 ^ (h - a) * Fintype.card G.V ∧
        Q.Bounded 3 (3 + terminalWidth D Y) (89 * (2 : ℝ) ^ k * B) ∧
        Q.X ≤ resetWidth c w * (σ + 2 * G.X + 2 * L.Z) ∧ G.Preserves Q ∧
        Q.mass = G.mass + 2 * G.X ∧ G.Tracks Q (resetPositions R Δ + 1) := by
  obtain ⟨k, _, ex⟩ := reset_exists hY hw hΔ enough c hc
  refine ⟨k, ?_⟩
  intro F _ R hR T _ x y L h a u D B σ G ha hD bounds hu hb slack
  have load v i : (coreDemands G.ix G.edge).incident u v i ≤ G.load v i := by
    unfold Demands.incident
    rw [← degree_push]
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load v i)
  obtain ⟨q⟩ := ex F R hR G.V G.E h a D ha hD G.N G.C G.src G.dst G.ix G.edge G.ns G.cs G.sub
    bounds.2.1 bounds.1 _ _ _ (fun v i => ⟨G.load_nonneg v i, bounds.2.2 v i⟩)
    (Nat.cast_pos.mpr hu) hb load
  obtain ⟨bound, rest⟩ := G.afterReset_spec q (by unfold resetWidth; positivity) slack
  exact ⟨G.afterReset q, q.eval_contract _, q.positions, by simpa only [mul_assoc] using bound, rest⟩

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end
