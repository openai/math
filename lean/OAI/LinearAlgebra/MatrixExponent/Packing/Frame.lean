import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.CompareExchange

/-! # Double counting the two ends of directed wires -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V I : Type} [Fintype I]

theorem weighted_degree [Fintype V] (e : I → V × V) (f : V → ℕ) :
    ∑ v, degree e v * f v = ∑ i, (f (e i).1 + f (e i).2) := by
  simp_rw [degree_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [arityCost, add_mul, sum_add_distrib, ite_mul]

theorem sum_degree [Fintype V] (e : I → V × V) : ∑ v, degree e v = 2 * Fintype.card I := by
  simpa [mul_comm] using weighted_degree e (fun _ => 1)

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Internal and exterior arity of an aggregate site -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset Classical

variable {F V W E : Type} [Fintype E] {x y : Wire}

theorem degree_bundle (P : E → V × V) (u : ℕ) (z : V) :
    degree (fun q : E × Fin u => P q.1) z = degree P z * u := by
  simp only [degree_sum, Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, mul_comm u, ← sum_mul]

def exterior (G : Diagram F x y) (f : G.V → V) (z : V) : ℕ :=
  Fintype.card {t : slots x // f (G.src.symm (.inl t)).1 = z} +
  Fintype.card {t : slots y // f (G.dst.symm (.inl t)).1 = z}

private theorem card_push (f : E → V) (z : V) :
    (Fintype.card {t // f t = z} : ℝ) = push f (fun _ => 1) z := by
  simp only [push, sum_boole, Fintype.card_subtype]

theorem exterior_comp [Fintype V] (G : Diagram F x y) (f : G.V → V) (g : V → W) (z : W) :
    (exterior G (g ∘ f) z : ℝ) = push g (fun v => (exterior G f v : ℝ)) z := by
  let a := fun t : slots x => f (G.src.symm (.inl t)).1
  let b := fun t : slots y => f (G.dst.symm (.inl t)).1
  simp only [exterior, Nat.cast_add, card_push]
  change push (g ∘ a) _ _ + push (g ∘ b) _ _ = _
  rw [← push_comp, ← push_comp]
  unfold push
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  split_ifs <;> first | rfl | simp

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Blocks on a common host

Retain a separate exterior port of the core for every tether bit.
The frozen tensors and all their other exterior legs need no transformation.
Recording the incidence and charges suffices to reattach them, term by
term, at the end of a sequence of contractions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {F T : Type} {x y : Wire} {h u : ℕ}

structure Fringe (x y : Wire) (T : Type) where
  tensor : slots x ⊕ slots y → T
  charge : T → ℝ
  cover : ∀ t, Fintype.card {q // tensor q = t} ≤ charge t
  scale : ℝ
  pos : 0 < scale
  le : scale ≤ 1
  cap : ℕ := 0
  discount : ℕ := 0

def portEnd (G : Diagram F x y) : slots x ⊕ slots y → G.V :=
  Sum.elim (fun t => (G.src.symm (.inl t)).1) (fun t => (G.dst.symm (.inl t)).1)

/-- All internal edges lie in the core. Frozen tables are indexed by `T`,
independently of the grouping and contraction history. -/
structure HostNet (F : Type) (L : Fringe x y T) (h u : ℕ) where
  diagram : Diagram F x y
  V : Type
  E : Type
  [fv : Fintype V]
  [fe : Fintype E]
  src : E → V
  dst : E → V
  ix : E → Cell h
  units : Bundles diagram src dst ix u
  park : T → V × Cell h
  past : V × Cell h → ℕ := fun _ => 0
  frozen : V → Prop
  N : V → Finset V
  C : V → Finset V
  ns : ∀ v z, z ∈ N v → v ∈ N z
  cs : ∀ v z, z ∈ C v → v ∈ C z
  sub : ∀ v, C v ⊆ N v
  kept : ∀ t, frozen (park t).1
  core : ∀ e, ¬frozen (src e) ∧ ¬frozen (dst e)
  edge : ∀ e, dst e ∈ C (src e)
  tether : ∀ q, let p := units.place (portEnd diagram q)
    let z := park (L.tensor q)
    ¬frozen p.1 ∧ p.2 = z.2 ∧ z.1 ∈ N p.1

attribute [instance] HostNet.fe HostNet.fv

/-- Reserved space for histories of eliminated wires. -/
def Fringe.reserve (L : Fringe x y T) := L.cap / (2 : ℝ) ^ L.discount

def Fringe.Z [Fintype T] (L : Fringe x y T) := (∑ t, L.charge t) + L.reserve

theorem Fringe.reserve_nonneg (L : Fringe x y T) : 0 ≤ L.reserve := by
  unfold reserve; positivity

theorem Fringe.nonneg (L : Fringe x y T) (t : T) : 0 ≤ L.charge t :=
  (Nat.cast_nonneg _).trans (L.cover t)

namespace HostNet

variable {L : Fringe x y T} (G : HostNet F L h u)

def X := Fintype.card G.E * u

def pair (e : G.E) := ((G.src e, G.ix e), (G.dst e, G.ix e))

def tetherLoad (p : G.V × Cell h) := exterior G.diagram G.units.place p

/-- Each eliminated internal port remains part of the local description. -/
def mass := ∑ p, G.past p

def rate := if G.mass ≤ L.cap then 1 / (2 : ℝ) ^ L.discount else 0

theorem rate_nonneg : 0 ≤ G.rate := by unfold rate; positivity

theorem rate_le : G.rate ≤ 1 := by
  unfold rate
  split
  · exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  · norm_num

theorem rate_budget : G.rate * G.mass ≤ L.reserve := by
  unfold rate
  split
  · rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ‹G.mass ≤ L.cap›) (by positivity)
  · rw [zero_mul]; exact L.reserve_nonneg

def carried {W : Type} (f : G.V × Cell h → W) (v : W) :=
  ∑ p, if f p = v then G.past p + degree G.pair p * u else 0

variable [Fintype T]

def load (v : G.V) (i : Cell h) : ℝ :=
  (G.tetherLoad (v, i) : ℝ) + degree G.pair (v, i) * (u : ℝ) +
    L.scale * push G.park L.charge (v, i) + G.rate * G.past (v, i)

def Bounded (Δ D : ℕ) (B : ℝ) : Prop :=
  (∀ v, (G.C v).card ≤ Δ) ∧ (∀ v, (G.N v).card ≤ D) ∧ ∀ v i, G.load v i ≤ B

theorem core_le_load (v : G.V) (i : Cell h) :
    (G.tetherLoad (v, i) : ℝ) + degree G.pair (v, i) * (u : ℝ) ≤ G.load v i :=
  (le_add_of_nonneg_right (mul_nonneg L.pos.le (push_nonneg _ _ L.nonneg _))).trans
    (le_add_of_nonneg_right (mul_nonneg G.rate_nonneg (Nat.cast_nonneg _)))

theorem load_nonneg (v : G.V) (i : Cell h) : 0 ≤ G.load v i :=
  le_trans (by positivity) (G.core_le_load v i)

end HostNet
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Conservation of load in a grouped core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {F T V W : Type} {x y : Wire}

theorem port_load (G : Diagram F x y) (f : G.V → V) (v : V) :
    (exterior G f v : ℝ) = push (f ∘ portEnd G) (fun _ => 1) v := by
  unfold push
  rw [Fintype.sum_sum_type]
  change _ = (∑ t : slots x, if f (G.src.symm (.inl t)).1 = v then (1 : ℝ) else 0) +
    ∑ t : slots y, if f (G.dst.symm (.inl t)).1 = v then (1 : ℝ) else 0
  simp only [exterior, Nat.cast_add, Fintype.card_subtype, sum_boole]

theorem Fringe.tethers [Fintype T] (L : Fringe x y T) : Fintype.card (slots x ⊕ slots y) ≤ L.Z := by
  have hx : (∑ t, push L.tensor (fun _ => 1) t) ≤ L.Z := by
    apply le_trans _ (le_add_of_nonneg_right L.reserve_nonneg)
    apply sum_le_sum
    intro t _
    simpa only [push, sum_boole, Fintype.card_subtype] using L.cover t
  simpa only [sum_push, sum_const, card_univ, nsmul_eq_mul, mul_one] using hx

theorem Fringe.total_nonneg [Fintype T] (L : Fringe x y T) : 0 ≤ L.Z :=
  add_nonneg (sum_nonneg fun t _ => L.nonneg t) L.reserve_nonneg

def prefixMap {a h : ℕ} (ha : a ≤ h) : Cell h →ₗ[ZMod 2] Cell a where
  toFun := ancestor ha
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem prefixMap_onto {a h : ℕ} (ha : a ≤ h) : Function.Surjective (prefixMap ha) := by
  intro c
  have : 0 < Fintype.card {x // ancestor ha x = c} := by rw [card_prefix]; positivity
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp this
  exact ⟨x.val, x.property⟩

namespace HostNet

variable {h u : ℕ} {L : Fringe x y T} (G : HostNet F L h u) [Fintype T]

theorem sum_load : (∑ v, ∑ i, G.load v i) ≤ 2 * (G.X : ℝ) + 2 * L.Z := by
  let endpt (e : G.E) (t : Bool) := if t then (G.dst e, G.ix e) else (G.src e, G.ix e)
  have ed (p : G.V × Cell h) : (degree G.pair p : ℝ) * u =
      push (Function.uncurry endpt) (fun _ => (u : ℝ)) p := degree_push endpt _ p
  have eq : (∑ v, ∑ i, G.load v i) =
      Fintype.card (slots x ⊕ slots y) + 2 * (G.X : ℝ) +
        L.scale * (∑ t, L.charge t) + G.rate * G.mass := by
    rw [← Fintype.sum_prod_type (fun p : G.V × Cell h => G.load p.1 p.2)]
    simp only [load, tetherLoad, port_load, ed, Prod.mk.eta, sum_add_distrib, ← mul_sum, sum_push,
      sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_bool, X, mass, Nat.cast_sum,
      Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [eq]
  have hs : 0 ≤ ∑ t, L.charge t := sum_nonneg fun i _ => L.nonneg i
  have ht := L.tethers
  unfold Fringe.Z at ht ⊢
  linarith only [ht, mul_le_of_le_one_left hs L.le, G.rate_budget]

/-- Exterior and parked charges follow the site assignment. Only the
internal edges need a fresh estimate after contraction. -/
theorem outside_le (o : G.V × Cell h → W) (z : W) :
    (exterior G.diagram (o ∘ G.units.place) z : ℝ) +
        L.scale * push (o ∘ G.park) L.charge z ≤ push o (Function.uncurry G.load) z := by
  rw [exterior_comp, ← push_comp]
  unfold push
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  rintro ⟨v, i⟩ _
  split_ifs
  · exact (add_le_add_left (le_add_of_nonneg_right (by positivity)) _).trans
      (le_add_of_nonneg_right (mul_nonneg G.rate_nonneg (Nat.cast_nonneg _)))
  · simp

omit [Fintype T] in
theorem carry_sum [Fintype W] (o : G.V × Cell h → W) :
    ∑ v, G.carried o v = G.mass + 2 * G.X := by
  unfold carried
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, sum_add_distrib, ← sum_mul]
  unfold X mass
  rw [sum_degree, mul_assoc]

omit [Fintype T] in
theorem rate_anti {a z : ℕ} (Q : HostNet F L a z) (hm : G.mass ≤ Q.mass) :
    Q.rate ≤ G.rate := by
  unfold rate
  split_ifs <;> first | exact le_rfl | omega | positivity

/-- Absorb the discounted history of old incident edges into their
existing port charge. New edges are charged at full width. -/
theorem reassign {a z : ℕ} (Q : HostNet F L a z) (o : G.V × Cell h → Q.V × Cell a)
    (park : Q.park = o ∘ G.park)
    (endpt : ∀ q, Q.units.place (portEnd Q.diagram q) = o (G.units.place (portEnd G.diagram q)))
    (record : Q.past = G.carried o) (p : Q.V × Cell a) :
    Q.load p.1 p.2 ≤ push o (Function.uncurry G.load) p + degree Q.pair p * (z : ℝ) := by
  have hmass : G.mass ≤ Q.mass := by
    change G.mass ≤ ∑ t, Q.past t
    rw [record, carry_sum]; omega
  have hr := G.rate_anti Q hmass
  have he : Q.units.place ∘ portEnd Q.diagram = (o ∘ G.units.place) ∘ portEnd G.diagram :=
    funext endpt
  have outside : (exterior Q.diagram Q.units.place p : ℝ) +
      L.scale * push Q.park L.charge p + Q.rate * Q.past p ≤ push o (Function.uncurry G.load) p := by
    rw [park, port_load, he, ← port_load, exterior_comp, ← push_comp, record]
    unfold carried push
    rw [Nat.cast_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    rintro ⟨v, i⟩ _
    split_ifs with h
    · rw [Nat.cast_add, Nat.cast_mul, mul_add]
      have h₁ := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (α := ℝ) (G.past (v, i)))
      have h₂ := mul_le_mul_of_nonneg_right Q.rate_le
        (show 0 ≤ (degree G.pair (v, i) : ℝ) * u by positivity)
      dsimp only [Function.uncurry_apply_pair, load, tetherLoad, push]
      linarith only [h₁, h₂]
    · simp
  change (exterior Q.diagram Q.units.place p : ℝ) + degree Q.pair p * (z : ℝ) +
    L.scale * push Q.park L.charge p + Q.rate * Q.past p ≤ _
  linarith only [outside]

/-- Every old occurrence has one destination. Frozen labels and tether
ports that coincide at an occurrence stay together. A common surjective
linear map on binary block indices controls all occurrences. Every host
has a uniform number of slots per old position, and parked tensors never
leave the slots allocated to their position. -/
def Preserves {a z : ℕ} (Q : HostNet F L a z) : Prop :=
  ∃ o : G.V × Cell h → Q.V × Cell a, Q.park = o ∘ G.park ∧
    (∀ p, Q.units.place (portEnd Q.diagram p) = o (G.units.place (portEnd G.diagram p))) ∧
      (∃ f : Cell h →ₗ[ZMod 2] Cell a, Function.Surjective f ∧ ∀ p, (o p).2 = f p.2) ∧
      ∃ (B : Type) (_ : Fintype B) (e : Q.V ≃ G.V × B), ∀ t, (e (Q.park t).1).1 = (G.park t).1

omit [Fintype T] in
theorem Preserves.refl : G.Preserves G :=
  ⟨id, rfl, fun _ => rfl, ⟨LinearMap.id, Function.surjective_id, fun _ => rfl⟩,
    Unit, inferInstance, (Equiv.prodUnique G.V Unit).symm, fun _ => rfl⟩

omit [Fintype T] in
theorem Preserves.trans {a z b t : ℕ} {G : HostNet F L h u}
    {Q : HostNet F L a z} {R : HostNet F L b t}
    (h₁ : G.Preserves Q) (h₂ : Q.Preserves R) : G.Preserves R := by
  obtain ⟨o, ho, ht, ⟨f, hf, ef⟩, A, _, j, hj⟩ := h₁
  obtain ⟨p, hp, hu, ⟨g, hg, eg⟩, B, _, k, hk⟩ := h₂
  exact ⟨p ∘ o, by rw [hp, ho]; rfl, fun z => (hu z).trans (congrArg p (ht z)),
    ⟨g.comp f, hg.comp hf, fun z => (eg (o z)).trans (congrArg g (ef z))⟩,
    A × B, inferInstance, k.trans ((j.prodCongr (.refl B)).trans (Equiv.prodAssoc _ _ _)),
    fun t => (congrArg (fun q => (j q).1) (hk t)).trans (hj t)⟩

end HostNet
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Reattaching frozen tables

Each exposed slot on the core becomes a separate wire to its original frozen
table. Only the ports of the frozen tables remain exterior. Contraction is
linear in the core tensor, so exact sums survive reattachment.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

structure Border (F T : Type) (a b x y : Wire) where
  table : T → Table F
  src : (Σ v, slots (table v).1) ≃ slots a ⊕ slots y
  dst : (Σ v, slots (table v).2.1) ≃ slots b ⊕ slots x

namespace Border

variable {F T : Type} {a b x y : Wire} (B : Border F T a b x y)

def tensor : slots x ⊕ slots y → T :=
  Sum.elim (fun i => (B.dst.symm (.inr i)).1) (fun i => (B.src.symm (.inr i)).1)

def merge (A E X Y : Type) : (X ⊕ E) ⊕ (A ⊕ Y) ≃ A ⊕ E ⊕ X ⊕ Y where
  toFun
    | .inl (.inl i) => .inr (.inr (.inl i))
    | .inl (.inr e) => .inr (.inl e)
    | .inr (.inl s) => .inl s
    | .inr (.inr j) => .inr (.inr (.inr j))
  invFun
    | .inl s => .inr (.inl s)
    | .inr (.inl e) => .inl (.inr e)
    | .inr (.inr (.inl i)) => .inl (.inl i)
    | .inr (.inr (.inr j)) => .inr (.inr j)
  left_inv := by rintro ((_|_)|(_|_)) <;> rfl
  right_inv := by rintro (_|_|_|_) <;> rfl

variable [Fintype T] (G : Diagram F x y)

abbrev attach : Diagram F a b where
  V := G.V ⊕ T
  E := G.E ⊕ slots x ⊕ slots y
  table := Sum.elim G.table B.table
  src := (Equiv.sumSigmaDistrib _).trans ((G.src.sumCongr B.src).trans (merge _ _ _ _))
  dst := (Equiv.sumSigmaDistrib _).trans ((G.dst.sumCongr B.dst).trans
    ((merge _ _ _ _).trans ((Equiv.refl _).sumCongr ((Equiv.refl _).sumCongr (Equiv.sumComm _ _)))))

theorem ends_core (e : G.E) :
    ((B.attach G).source (.inl e), (B.attach G).target (.inl e)) =
      (Sum.inl (G.source e), Sum.inl (G.target e)) := rfl

theorem ends_input (i : slots x) :
    ((B.attach G).source (.inr (.inl i)), (B.attach G).target (.inr (.inl i))) =
      (Sum.inl (portEnd G (.inl i)), Sum.inr (B.tensor (.inl i))) := rfl

theorem ends_output (i : slots y) :
    ((B.attach G).source (.inr (.inr i)), (B.attach G).target (.inr (.inr i))) =
      (Sum.inr (B.tensor (.inr i)), Sum.inl (portEnd G (.inr i))) := rfl

variable [Field F]

def weight (s : Val a) (t : Val b) (u : Val x) (v : Val y) : F :=
  ∏ j, (B.table j).2.2
    ((bits (B.table j).1).symm (fun i => Sum.elim (bits a s) (bits y v) (B.src ⟨j, i⟩)))
    ((bits (B.table j).2.1).symm (fun i => Sum.elim (bits b t) (bits x u) (B.dst ⟨j, i⟩)))

theorem eval_attach (s : Val a) (t : Val b) :
    (B.attach G).eval s t = ∑ u : Val x, ∑ v : Val y, G.eval u v * B.weight s t u v := by
  classical
  let _ : DecidableEq (B.attach G).E := fun _ _ => Classical.propDecidable _
  let e : (Val x × Val y) × (G.E → Bool) ≃ ((B.attach G).E → Bool) :=
    (Equiv.prodComm _ _).trans (((Equiv.refl _).prodCongr (bits (.pair x y))).trans
      (Equiv.sumArrowEquivProdArrow _ _ Bool).symm)
  unfold Diagram.eval
  rw [← e.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  change (∏ j : G.V ⊕ T, (B.attach G).vertex s t (e ((u, v), z)) j) = _
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _
    apply congrArg₂ (G.table j).2.2
    · apply congrArg (bits (G.table j).1).symm
      funext i
      change Sum.elim _ _ (merge _ _ _ _ (.inl (G.src ⟨j, i⟩))) = _
      cases G.src ⟨j, i⟩ <;> rfl
    · apply congrArg (bits (G.table j).2.1).symm
      funext i
      change Sum.elim _ _ (Sum.map id (Sum.map id Sum.swap) (merge _ _ _ _ (.inl (G.dst ⟨j, i⟩)))) = _
      cases G.dst ⟨j, i⟩ <;> rfl
  · apply Finset.prod_congr rfl
    intro j _
    apply congrArg₂ (B.table j).2.2
    · apply congrArg (bits (B.table j).1).symm
      funext i
      change Sum.elim _ _ (merge _ _ _ _ (.inr (B.src ⟨j, i⟩))) = _
      cases B.src ⟨j, i⟩ <;> rfl
    · apply congrArg (bits (B.table j).2.1).symm
      funext i
      change Sum.elim _ _ (Sum.map id (Sum.map id Sum.swap) (merge _ _ _ _ (.inr (B.dst ⟨j, i⟩)))) = _
      cases B.dst ⟨j, i⟩ <;> rfl

theorem attach_sum {I : Type} [Fintype I] (Q : I → Diagram F x y)
    (H : ∀ u v, ∑ i, (Q i).eval u v = G.eval u v) (s : Val a) (t : Val b) :
    ∑ i, (B.attach (Q i)).eval s t = (B.attach G).eval s t := by
  simp_rw [eval_attach]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, H]

end Border
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Separating off the frozen vertices

All exterior positions lie on frozen vertices. No internal wire
joins two frozen vertices. Partition the wires into core edges and
the two directions of tethers, giving each tether a separate name.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open scoped Classical

variable {F : Type} {a b : Wire}

structure Freeze (G : Diagram F a b) where
  frozen : G.V → Prop
  exterior : ∀ q, frozen (portEnd G q)
  separate : ∀ e, ¬(frozen (G.source e) ∧ frozen (G.target e))

namespace Freeze
variable {G : Diagram F a b} (Z : Freeze G)

abbrev Core := {v // ¬ Z.frozen v}
abbrev Fixed := {v // Z.frozen v}
abbrev Internal := {e // ¬ Z.frozen (G.source e) ∧ ¬ Z.frozen (G.target e)}
abbrev Input := {e // Z.frozen (G.target e)}
abbrev Output := {e // Z.frozen (G.source e)}

def x := word (Fintype.card Z.Input)
def y := word (Fintype.card Z.Output)

def input : slots Z.x ≃ Z.Input :=
  Fintype.equivOfCardEq ((card_slots Z.x).trans (wd_word _))

def output : slots Z.y ≃ Z.Output :=
  Fintype.equivOfCardEq ((card_slots Z.y).trans (wd_word _))

def edges : Z.Internal ⊕ slots Z.x ⊕ slots Z.y ≃ G.E where
  toFun := Sum.elim Subtype.val (Sum.elim (Subtype.val ∘ Z.input) (Subtype.val ∘ Z.output))
  invFun e := if hi : Z.frozen (G.target e) then .inr (.inl (Z.input.symm ⟨e, hi⟩))
    else if ho : Z.frozen (G.source e) then .inr (.inr (Z.output.symm ⟨e, ho⟩))
    else .inl ⟨e, ho, hi⟩
  left_inv := by
    rintro (e | i | j)
    · simp [e.property.1, e.property.2]
    · simp [(Z.input i).property]
    · have hn : ¬Z.frozen (G.target (Z.output j)) :=
        fun h => Z.separate _ ⟨(Z.output j).property, h⟩
      simp [hn, (Z.output j).property]
  right_inv e := by dsimp; split_ifs <;> simp

private def forget {V : Type} {I : V → Type} {p : V → Prop}
    (z : Σ v : Subtype p, I v.val) : Σ v, I v := ⟨z.1.val, z.2⟩

private theorem forget_inj {V : Type} {I : V → Type} {p : V → Prop} :
    Function.Injective (forget (I := I) (p := p)) := by
  rintro ⟨⟨v, hv⟩, i⟩ ⟨⟨w, hw⟩, j⟩ h
  cases h; rfl

private def restrict {V A B : Type} {I : V → Type} (e : A ⊕ B ≃ Σ v, I v) (p : V → Prop)
    (ha : ∀ x, p (e (.inl x)).1) (hb : ∀ x, ¬p (e (.inr x)).1) :
    (Σ v : Subtype p, I v.val) ≃ A :=
  (Equiv.ofBijective (fun x => ⟨⟨(e (.inl x)).1, ha x⟩, (e (.inl x)).2⟩) (by
    constructor
    · intro i j he
      exact Sum.inl.inj (e.injective (congrArg forget he))
    · intro z
      obtain ⟨x|x, hx⟩ := e.surjective (forget z)
      · exact ⟨x, forget_inj hx⟩
      · exact (hb x (hx.symm ▸ z.1.property)).elim)).symm

private def srcOrder := ((Border.merge (slots a) Z.Internal (slots Z.x) (slots Z.y)).trans
    ((Equiv.refl _).sumCongr Z.edges)).trans G.src.symm

private def dstOrder := (((Border.merge (slots b) Z.Internal (slots Z.y) (slots Z.x)).trans
    ((Equiv.refl _).sumCongr ((Equiv.refl _).sumCongr (Equiv.sumComm _ _)))).trans
      ((Equiv.refl _).sumCongr Z.edges)).trans G.dst.symm

private theorem src_core (p : slots Z.x ⊕ Z.Internal) : ¬Z.frozen (Z.srcOrder (.inl p)).1 := by
  cases p with
  | inl i => exact fun h => Z.separate _ ⟨h, (Z.input i).property⟩
  | inr e => exact e.property.1

private theorem src_fixed (p : slots a ⊕ slots Z.y) : Z.frozen (Z.srcOrder (.inr p)).1 := by
  cases p with
  | inl i => exact Z.exterior (.inl i)
  | inr i => exact (Z.output i).property

private theorem dst_core (p : slots Z.y ⊕ Z.Internal) : ¬Z.frozen (Z.dstOrder (.inl p)).1 := by
  cases p with
  | inl i => exact fun h => Z.separate _ ⟨(Z.output i).property, h⟩
  | inr e => exact e.property.2

private theorem dst_fixed (p : slots b ⊕ slots Z.x) : Z.frozen (Z.dstOrder (.inr p)).1 := by
  cases p with
  | inl i => exact Z.exterior (.inr i)
  | inr i => exact (Z.input i).property

abbrev core : Diagram F Z.x Z.y where
  V := Z.Core
  E := Z.Internal
  table v := G.table v.val
  src := restrict Z.srcOrder _ Z.src_core (fun i => not_not.mpr (Z.src_fixed i))
  dst := restrict Z.dstOrder _ Z.dst_core (fun i => not_not.mpr (Z.dst_fixed i))

def border : Border F Z.Fixed a b Z.x Z.y where
  table v := G.table v.val
  src := restrict ((Equiv.sumComm _ _).trans Z.srcOrder) Z.frozen Z.src_fixed Z.src_core
  dst := restrict ((Equiv.sumComm _ _).trans Z.dstOrder) Z.frozen Z.dst_fixed Z.dst_core

theorem source (e : Z.Internal) : (Z.core.source e).val = G.source e.val := rfl
theorem target (e : Z.Internal) : (Z.core.target e).val = G.target e.val := rfl

def tether : slots Z.x ⊕ slots Z.y → G.E := fun i => Z.edges (.inr i)

theorem ports (q : slots Z.x ⊕ slots Z.y) :
    let c := (portEnd Z.core q).val
    let t := (Z.border.tensor q).val
    (G.source (Z.tether q), G.target (Z.tether q)) =
      if q.isLeft then (c, t) else (t, c) := by cases q <;> rfl

private abbrev joined := Z.border.attach Z.core

private def vertices : Z.Core ⊕ Z.Fixed ≃ G.V :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl Z.frozen)

private theorem restrict_apply {V A B : Type} {I : V → Type} (e : A ⊕ B ≃ Σ v, I v)
    (p : V → Prop) (ha : ∀ x, p (e (.inl x)).1) (hb : ∀ x, ¬p (e (.inr x)).1)
    (z : Σ v : Subtype p, I v.val) : e (.inl (restrict e p ha hb z)) = forget z :=
  congrArg forget ((restrict e p ha hb).symm_apply_apply z)

private theorem read {A E E' : Type} (s : A → Bool) (z : E → Bool)
    (e : E' ≃ E) (q : A ⊕ E') (r : A ⊕ E) (h : ((Equiv.refl _).sumCongr e) q = r) :
    Sum.elim s (z ∘ e) q = Sum.elim s z r := by
  subst r
  cases q <;> rfl

private theorem vertex_join (s : Val a) (t : Val b) (z : G.E → Bool) (v : Z.Core ⊕ Z.Fixed) :
    Z.joined.vertex s t (z ∘ Z.edges) v = G.vertex s t z (Z.vertices v) := by
  cases v with
  | inl v =>
    apply congrArg₂ (G.table v.val).2.2
    · apply congrArg (bits (G.table v.val).1).symm
      funext i
      apply read
      apply G.src.symm_apply_eq.mp
      exact restrict_apply Z.srcOrder _ Z.src_core (fun i => not_not.mpr (Z.src_fixed i)) ⟨v, i⟩
    · apply congrArg (bits (G.table v.val).2.1).symm
      funext i
      apply read
      apply G.dst.symm_apply_eq.mp
      exact restrict_apply Z.dstOrder _ Z.dst_core (fun i => not_not.mpr (Z.dst_fixed i)) ⟨v, i⟩
  | inr v =>
    apply congrArg₂ (G.table v.val).2.2
    · apply congrArg (bits (G.table v.val).1).symm
      funext i
      apply read
      apply G.src.symm_apply_eq.mp
      exact restrict_apply ((Equiv.sumComm _ _).trans Z.srcOrder) _ Z.src_fixed Z.src_core ⟨v, i⟩
    · apply congrArg (bits (G.table v.val).2.1).symm
      funext i
      apply read
      apply G.dst.symm_apply_eq.mp
      exact restrict_apply ((Equiv.sumComm _ _).trans Z.dstOrder) _ Z.dst_fixed Z.dst_core ⟨v, i⟩

theorem reconstruct [Field F] (s : Val a) (t : Val b) :
    (Z.border.attach Z.core).eval s t = G.eval s t := by
  let _ : DecidableEq Z.joined.E := fun _ _ => Classical.propDecidable _
  let e := Z.edges.symm.arrowCongr (Equiv.refl Bool)
  unfold Diagram.eval
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  exact Fintype.prod_equiv Z.vertices _ _ (fun v => Z.vertex_join s t z v)

end Freeze
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Partitioning parallel core wires into equal bundles -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open scoped Classical

variable {F : Type} {a b : Wire}

/-- Uniform packets of bits, each with one ordered pair of endpoints. -/
structure Packets (G : Diagram F a b) (u : ℕ) where
  E : Type
  [fe : Fintype E]
  src : E → G.V
  dst : E → G.V
  bits : G.E ≃ E × Fin u
  left : ∀ e, src (bits e).1 = G.source e
  right : ∀ e, dst (bits e).1 = G.target e

attribute [instance] Packets.fe

private theorem bundle_fibers {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] (p : E → V) (u : ℕ)
    (h : ∀ v, u ∣ Fintype.card {e // p e = v}) :
    ∃ (A : Type) (_ : Fintype A) (f : A → V) (bits : E ≃ A × Fin u),
      ∀ e, f (bits e).1 = p e := by
  choose n hn using h
  let index (v : V) : {e // p e = v} ≃ Fin (n v) × Fin u :=
    Fintype.equivOfCardEq (by simp [hn v, mul_comm])
  let A := Σ v, Fin (n v)
  let flatten : (Σ v, Fin (n v) × Fin u) ≃ A × Fin u :=
    { toFun := fun p => (⟨p.1, p.2.1⟩, p.2.2)
      invFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      left_inv _ := rfl, right_inv _ := rfl }
  exact ⟨A, inferInstance, Sigma.fst,
    (Equiv.sigmaFiberEquiv p).symm.trans ((Equiv.sigmaCongrRight index).trans flatten),
    fun _ => rfl⟩

theorem packets_exist (G : Diagram F a b) (u : ℕ)
    (hw : ∀ v w, u ∣ Fintype.card {e // G.source e = v ∧ G.target e = w}) :
    Nonempty (Packets G u) := by
  let p (e : G.E) := (G.source e, G.target e)
  have div (q : G.V × G.V) : u ∣ Fintype.card {e // p e = q} := by
    obtain ⟨v, w⟩ := q
    simpa [p, Fintype.card_subtype] using hw v w
  obtain ⟨E, _, f, bits, hf⟩ := bundle_fibers p u div
  exact ⟨⟨E, fun e => (f e).1, fun e => (f e).2, bits,
    fun e => congrArg Prod.fst (hf e), fun e => congrArg Prod.snd (hf e)⟩⟩

namespace Freeze

variable {G : Diagram F a b} (Z : Freeze G)

def Divisible (u : ℕ) : Prop :=
  ∀ v w, ¬Z.frozen v → ¬Z.frozen w → u ∣ Fintype.card {e // G.source e = v ∧ G.target e = w}

theorem bundles {u : ℕ} (h : Z.Divisible u) : Nonempty (Packets Z.core u) := by
  let p (e : Z.Internal) := (Z.core.source e, Z.core.target e)
  have div (q : Z.Core × Z.Core) : u ∣ Fintype.card {e // p e = q} := by
    let eq : {e // p e = q} ≃ {e // G.source e = q.1.val ∧ G.target e = q.2.val} :=
      { toFun := fun e => ⟨e.val.val, congrArg (fun q => q.1.val) e.property,
          congrArg (fun q => q.2.val) e.property⟩
        invFun := fun e => ⟨⟨e.val, e.property.1.symm ▸ q.1.property,
          e.property.2.symm ▸ q.2.property⟩, Prod.ext (Subtype.ext e.property.1)
            (Subtype.ext e.property.2)⟩
        left_inv _ := rfl, right_inv _ := rfl }
    rw [Fintype.card_congr eq]
    exact h _ _ q.1.property q.2.property
  obtain ⟨E, _, f, bits, hf⟩ := bundle_fibers p u div
  exact ⟨⟨E, fun e => (f e).1, fun e => (f e).2, bits,
    fun e => congrArg Prod.fst (hf e), fun e => congrArg Prod.snd (hf e)⟩⟩

end Freeze
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Recovering loads from station arities -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {F V T : Type} {a b : Wire} {h u : ℕ}

theorem site_arity (G : Diagram F a b) (p : G.V → V) (v : V) :
    push p (fun i => (G.arity i : ℝ)) v = (exterior G p v : ℝ) +
      degree (fun e => (p (G.source e), p (G.target e))) v := by
  have arity (i : G.V) : (G.arity i : ℝ) = push G.station (fun _ => 1) i := by
    rw [← G.degree]
    simp only [push, sum_boole, Fintype.card_subtype]
  rw [show (fun i => (G.arity i : ℝ)) = push G.station (fun _ => 1) from funext arity, push_comp]
  rw [port_load, degree_sum, Nat.cast_sum]
  simp only [arityCost, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_add_distrib]
  unfold push
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  exact add_add_add_comm _ _ _ _

theorem HostNet.load_eq [Fintype T] {L : Fringe a b T} (H : HostNet F L h u) (v : H.V × Cell h) :
    H.load v.1 v.2 = push H.units.place (fun i => (H.diagram.arity i : ℝ)) v +
      L.scale * push H.park L.charge v + H.rate * H.past v := by
  let p (e : H.diagram.E) := (H.units.place (H.diagram.source e), H.units.place (H.diagram.target e))
  have deg : degree p v = degree H.pair v * u := by
    rw [← degree_bundle H.pair u v, degree_sum, degree_sum]
    exact Fintype.sum_equiv H.units.bits _ _ (fun e =>
      congrArg (arityCost v) (Prod.ext (H.units.left e) (H.units.right e)))
  unfold HostNet.load HostNet.tetherLoad
  rw [site_arity]
  change _ = (exterior H.diagram H.units.place v : ℝ) + degree p v + _ + _
  rw [deg, Nat.cast_mul]

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Each tether uses a distinct port of its frozen table -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Freeze

open scoped Classical

variable {F : Type} {a b : Wire} {G : Diagram F a b} (Z : Freeze G)

theorem cover (t : Z.Fixed) :
    Fintype.card {q // Z.border.tensor q = t} ≤ G.arity t.val := by
  let endpt : slots Z.x ⊕ slots Z.y → G.End
    | .inl i => .inr (.inr (Z.input i).val)
    | .inr i => .inl (.inr (Z.output i).val)
  have loc q : G.station (endpt q) = (Z.border.tensor q).val := by cases q <;> rfl
  have hi : Function.Injective endpt := by
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl (Z.input.injective (Subtype.ext (Sum.inr.inj (Sum.inr.inj h))))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Z.output.injective (Subtype.ext (Sum.inr.inj (Sum.inl.inj h))))
  let f (q : {q // Z.border.tensor q = t}) : {e // G.station e = t.val} :=
    ⟨endpt q.val, (loc _).trans (congrArg Subtype.val q.property)⟩
  rw [← G.degree]
  exact Fintype.card_le_of_injective f fun _ _ h => Subtype.ext (hi (congrArg Subtype.val h))

def fringe (charge : Z.Fixed → ℝ) (hc : ∀ t, (G.arity t.val : ℝ) ≤ charge t)
    (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) : Fringe Z.x Z.y Z.Fixed where
  tensor := Z.border.tensor
  charge := charge
  cover t := by convert! (Nat.cast_le.mpr (Z.cover t)).trans (hc t) using 3
  scale := s
  pos := hs
  le := hs'

end OAI.LinearAlgebra.MatrixExponent.Packing.Freeze
end

/-!
# Placing the split diagram on its block host

Uniform internal multiplicities suffice to construct the core bundles.
The two exterior legs of the core consist precisely of its tethers.
Every other leg stays attached to the original frozen table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Freeze
open scoped Classical

variable {F : Type} {a b : Wire} {G : Diagram F a b} (Z : Freeze G)

structure Frame (V : Type) (h : ℕ) where
  place : G.V → V × Cell h
  frozen : V → Prop
  keep : ∀ v, frozen (place v).1 ↔ Z.frozen v
  N : V → Finset V
  C : V → Finset V
  ns : ∀ v z, z ∈ N v → v ∈ N z
  cs : ∀ v z, z ∈ C v → v ∈ C z
  sub : ∀ v, C v ⊆ N v
  group : ∀ e, (place (G.source e)).2 = (place (G.target e)).2
  edge : ∀ e : Z.Internal, (place (G.target e.val)).1 ∈ C (place (G.source e.val)).1
  full : ∀ e, (place (G.target e)).1 ∈ N (place (G.source e)).1

namespace Frame

variable {V : Type} {h u : ℕ} {Z} (H : Z.Frame V h) (hu : 0 < u) (hd : Z.Divisible u)
  (L : Fringe Z.x Z.y Z.Fixed) (hL : L.tensor = Z.border.tensor)

private theorem tether (q : slots Z.x ⊕ slots Z.y) :
    let p := H.place (portEnd Z.core q).val
    let z := H.place (Z.border.tensor q).val
    ¬H.frozen p.1 ∧ p.2 = z.2 ∧ z.1 ∈ H.N p.1 := by
  refine ⟨mt (H.keep _).mp (portEnd Z.core q).property, ?_⟩
  cases q with
  | inl i => exact ⟨H.group (Z.input i).val, H.full (Z.input i).val⟩
  | inr i => exact ⟨(H.group (Z.output i).val).symm, H.ns _ _ (H.full (Z.output i).val)⟩

variable [Fintype V]

/-- The caller may specify the ordering within each packet. -/
def hostOf (r : Packets Z.core u) : HostNet F L h u := by
  let p (v : Z.Core) := H.place v.val
  have hh (e : r.E) : (p (r.src e)).2 = (p (r.dst e)).2 ∧
      (p (r.dst e)).1 ∈ H.C (p (r.src e)).1 := by
    obtain ⟨j, hj⟩ := r.bits.surjective (e, ⟨0, hu⟩)
    have hs := r.left j
    have ht := r.right j
    rw [hj] at hs ht
    rw [hs, ht]
    exact ⟨H.group j.val, H.edge j⟩
  exact {
    diagram := Z.core
    V := V
    E := r.E
    src e := (p (r.src e)).1
    dst e := (p (r.dst e)).1
    ix e := (p (r.src e)).2
    units := {
      place := p
      bits := r.bits
      left e := by rw [r.left]
      right e := by rw [(hh _).1, r.right] }
    park t := H.place t.val
    frozen := H.frozen
    N := H.N, C := H.C, ns := H.ns, cs := H.cs, sub := H.sub
    kept t := (H.keep _).mpr t.property
    core e := ⟨mt (H.keep _).mp (r.src e).property, mt (H.keep _).mp (r.dst e).property⟩
    edge e := (hh e).2
    tether q := by rw [hL]; exact H.tether q }

def host : HostNet F L h u :=
  H.hostOf hu L hL (Classical.choice (Z.bundles hd))

theorem host_load (p : V × Cell h) :
    (H.host hu hd L hL).load p.1 p.2 =
      push (fun v : Z.Core => H.place v.val) (fun v => (G.arity v.val : ℝ)) p +
        L.scale * push (fun t : Z.Fixed => H.place t.val) L.charge p :=
  by
    have ht := HostNet.load_eq (H.host hu hd L hL) p
    rw [show (H.host hu hd L hL).past p = 0 from rfl, Nat.cast_zero, mul_zero, add_zero] at ht
    exact ht

end Frame
end OAI.LinearAlgebra.MatrixExponent.Packing.Freeze
end
