import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Host
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality

/-! # Width and incident bundle counts for ordinary keys -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Finset
open scoped Classical

variable {K : Type} [Fintype K]

private theorem by_key {A : Type} [Fintype A] (p : K → A → Prop) [∀ k, DecidablePred (p k)]
    (keys : A → Finset K) (he : ∀ k i, p k i ↔ k ∈ keys i) (f : K → ℕ) (g : A → ℕ) :
    (∑ k, ∑ i : {a // p k a}, g i.val * f k) = ∑ i, g i * (∑ k ∈ keys i, f k) := by
  have row k : (∑ i : {a // p k a}, g i.val * f k) =
      ∑ i, if k ∈ keys i then g i * f k else 0 := by
    rw [← sum_subtype (univ.filter (p k)) (fun _ => mem_filter_univ _) (fun i => g i * f k),
      sum_filter]
    simp only [he]
  simp_rw [row]
  rw [sum_comm]
  simp [mul_sum]

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y)

private def traffic (f : K → ℕ) (v : S.Vertex) :=
  ∑ e : S.Edge, Packing.arityCost v (S.source e, S.target e) * f e.1

omit [Field F] in
private theorem expanded (f : K → ℕ) (v : S.Vertex) :
    S.traffic f v =
      (∑ a, Packing.arityCost v (.inr (.inl a), .inr (.inr a)) * (∑ k ∈ S.seen a, f k)) +
      (∑ e, Packing.arityCost v (.inr (.inl (S.src e)), .inr (.inl (S.dst e))) *
        (∑ k ∈ S.seen (S.src e) ∩ S.seen (S.dst e), f k)) +
      (∑ i : Place C, Packing.arityCost v (.inr (.inl i.1), .inl i) * (∑ k ∈ S.reads i, f k)) := by
  rw [traffic, Fintype.sum_sigma]
  simp only [Fintype.sum_sum_type, source, start, target, sum_add_distrib,
    ← add_assoc]
  refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ ?_) ?_
  · exact by_key (fun k a => k ∈ S.seen a) S.seen (fun _ _ => Iff.rfl) f
      (fun a => Packing.arityCost v (.inr (.inl a), .inr (.inr a)))
  · exact by_key (fun k e => k ∈ S.seen (S.src e) ∧ k ∈ S.seen (S.dst e))
      (fun e => S.seen (S.src e) ∩ S.seen (S.dst e)) (fun _ _ => mem_inter.symm) f
      (fun e => Packing.arityCost v (.inr (.inl (S.src e)), .inr (.inl (S.dst e))))
  · exact by_key (fun k i => k ∈ S.reads i) S.reads (fun _ _ => Iff.rfl) f
      (fun i => Packing.arityCost v (.inr (.inl i.1), .inl i))

omit [Field F] in
private theorem traffic_item (f : K → ℕ) (i : Place C) :
    S.traffic f (.inl i) = ∑ k ∈ S.reads i, f k := by
  rw [expanded]
  simp [Packing.arityCost, ite_mul]

omit [Field F] in
private theorem traffic_storage (f : K → ℕ) (v : V) :
    S.traffic f (.inr (.inr v)) = ∑ k ∈ S.seen v, f k := by
  rw [expanded]
  simp [Packing.arityCost, ite_mul]

omit [Field F] in
private theorem traffic_hub (f : K → ℕ) (v : V) :
    S.traffic f (.inr (.inl v)) ≤
      (1 + Packing.degree (fun e => (S.src e, S.dst e)) v) * (∑ k ∈ S.seen v, f k) +
        ∑ i : Place C, if i.1 = v then ∑ k ∈ S.reads i, f k else 0 := by
  rw [expanded, Packing.degree_sum, add_mul, one_mul, sum_mul]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · simp [Packing.arityCost, ite_mul]
  · apply sum_le_sum
    intro e _
    simp only [Packing.arityCost, Sum.inr.injEq, Sum.inl.injEq]
    by_cases hi : S.src e = v
    · rw [hi]; exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset inter_subset_left)
    by_cases hj : S.dst e = v
    · rw [hj]; exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset inter_subset_right)
    simp [hi, hj]
  · simp [Packing.arityCost, ite_mul]

private theorem arity_eq (v : S.Vertex) :
    S.backdrop.base.arity v =
      Fintype.card {i // Sum.inl (S.left i) = v} + Fintype.card {i // Sum.inl (S.right i) = v} +
        S.traffic Y.width v := by
  simp only [Bundled.arity, traffic, Packing.arityCost, add_mul, sum_add_distrib, ite_mul,
    one_mul, zero_mul, add_assoc]
  congr! 4

private theorem degree_eq (v : S.Vertex) :
    S.backdrop.base.degree v = S.traffic (fun _ => 1) v := by
  simp only [Bundled.degree, traffic, Packing.arityCost, mul_one, sum_add_distrib]

theorem arity_item (i : Place C) :
    S.backdrop.base.arity (.inl i) = Fintype.card {j // S.left j = i} +
      Fintype.card {j // S.right j = i} + ∑ k ∈ S.reads i, Y.width k := by
  rw [arity_eq, traffic_item]
  simp [Fintype.card_subtype]

theorem arity_storage (v : V) : S.backdrop.base.arity (.inr (.inr v)) = ∑ k ∈ S.seen v, Y.width k := by
  rw [arity_eq, traffic_storage]
  simp

theorem arity_hub (v : V) : S.backdrop.base.arity (.inr (.inl v)) ≤
    (1 + Packing.degree (fun e => (S.src e, S.dst e)) v) * (∑ k ∈ S.seen v, Y.width k) +
      ∑ i : Place C, if i.1 = v then ∑ k ∈ S.reads i, Y.width k else 0 := by
  rw [arity_eq]
  simpa [Fintype.card_subtype] using S.traffic_hub Y.width v

theorem degree_item (i : Place C) : S.backdrop.base.degree (.inl i) = (S.reads i).card := by
  rw [degree_eq, traffic_item]
  simp

theorem degree_storage (v : V) : S.backdrop.base.degree (.inr (.inr v)) = (S.seen v).card := by
  rw [degree_eq, traffic_storage]
  simp

theorem degree_hub (v : V) : S.backdrop.base.degree (.inr (.inl v)) ≤
    (1 + Packing.degree (fun e => (S.src e, S.dst e)) v) * (S.seen v).card +
      ∑ i : Place C, if i.1 = v then (S.reads i).card else 0 := by
  rw [degree_eq]
  simpa using S.traffic_hub (fun _ => 1) v

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! Raw numerical inputs to the layout estimates. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y) {h D T R g k : ℕ} {W : ℝ} {P : Input F a b h D T R g W}

def seamDegree (v : V) := Packing.degree (fun e => (S.src e, S.dst e)) v

def ordinaryLoad (v : V) :=
  (1 + S.seamDegree v) * (∑ k ∈ S.seen v, Y.width k) +
    ∑ i : Place C, if i.1 = v then ∑ k ∈ S.reads i, Y.width k else 0

def exteriorLoad (i : Place C) := Fintype.card {j // S.left j = i} + Fintype.card {j // S.right j = i}

def stationLoad (i : Place C) := S.exteriorLoad i + legWidth C i

variable {S} (G : S.Geo P k)

structure Geo.Budgets (d ℓ : ℕ) (e : E → ℕ) : Prop where
  occupied : (Fintype.card V : ℝ) * T ≤ W
  keys : ∀ v, (S.seen v).card ≤ D ^ k
  seams : ∀ v, S.seamDegree v ≤ D ^ k
  ordinary : ∀ v, (S.ordinaryLoad v : ℝ) ≤ T / (D : ℝ) ^ (ℓ + 3)
  collectors : (Fintype.card {i // G.frozen i} : ℝ) * D * T ≤ k * W
  max : ∀ i, G.frozen i → S.stationLoad i ≤ k * (D : ℝ) * T
  square : (∑ i : {i // G.frozen i}, (S.stationLoad i.val) ^ 2) ≤ k * W * T
  residue : ∀ i, ¬ G.frozen i → legWidth C i ≤ T / (D : ℝ) ^ (ℓ + 3)
  chambers : ∀ v, S.backdrop.chamberLoad e v ≤ (T / (D : ℝ) ^ (ℓ + 2)) * Real.sqrt M
  total : (∑ i, legWidth C i) + (∑ j, seamWidth C e j) ≤ k * W * (1 + (d : ℝ))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! # Contact counts in a profile -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K} {e : E → ℕ}

omit [Field F] [Fintype E] in
theorem sum_place {R : Type*} [AddCommMonoid R] (f : Place C → R) (v : V) :
    (∑ i, if i.1 = v then f i else 0) = ∑ j, f ⟨v, j⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_single v (fun x hx => by simp [hx])]
  simp

namespace Backdrop
variable (B : Backdrop C a b) (p : Profile C e) (L : ℕ)

theorem base_degree (v : B.base.V) :
    (B.emitted p L).degree (.inl v) =
      B.base.degree v + ∑ i, if B.owner i = v then 2 * M else 0 := by
  simp only [Bundled.degree, emitted, Attach.net, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    Sum.inl.injEq, reduceCtorEq, ite_false, sum_const_zero, add_zero, zero_add,
    arm, Grid.point]
  rw [← sum_add_distrib]
  simp [-sum_boole, two_mul, add_assoc]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases h : B.owner i = v <;> simp [h]

theorem degree_a (v : V) (j : Fin M) :
    (B.emitted p L).degree (.inr (.inl (v, j))) =
      Packing.degree (fun e => (B.src e, B.dst e)) v + (C v).stations.length := by
  rw [degree_sum]
  simp [-sum_boole, Bundled.degree, emitted, Attach.net, chambers, seamEnd, socket, Grid.map,
    Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and, arityCost, sum_add_distrib,
    sum_place, add_assoc]

theorem degree_b (v : V) (j : Fin M) :
    (B.emitted p L).degree (.inr (.inr (v, j))) = (C v).stations.length := by
  simp [-sum_boole, Bundled.degree, emitted, Attach.net, chambers, seamEnd, socket, Grid.map,
    Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and, sum_place]

end Backdrop
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-! Numerical data of one terminal configuration, before chunk encoding. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Rounds
open SphereScale (q size budget probes)

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k : ℕ} {W : ℝ} {P : Input F a b h D T R g W}

def allocation (g ℓ : ℕ) := 64 * (budget g + 1) ^ 2 + 8 * (ℓ + 32) + 10

def energyAt (C : V → Surface.Cell F (M * r) (M * t) U E X) (L : ℕ) (i : Place C) :=
  L * (item C i).a + (item C i).b

/-- Here `L` is the Frobenius power, `B` the block size and `m`
the number of private species. -/
structure Geo.Raw (G : S.Geo P k) (ℓ L B m : ℕ) (e : E → ℕ)
    (thin : Place C → Prop) (selector : K → Prop) : Prop where
  occupied : (Fintype.card V : ℝ) * D * T ≤ W
  seams : ∀ v, S.seamDegree v ≤ budget g
  seamEnergy : ∀ i, e i ≤ budget g * D ^ 2 * SphereScale.energy ℓ D (m * B)
  energy : ∀ i, energyAt C L i ≤ budget g * D ^ 2 * L * SphereScale.energy ℓ D (m * B)
  collected : (∑ i : {i // G.frozen i}, (energyAt C L i.val : ℝ)) ≤
    budget g * (L : ℝ) * size ℓ D * W
  collectors : (Fintype.card {i // G.frozen i} : ℝ) * D * T ≤ budget g * W
  exterior : ∀ i, G.frozen i → S.exteriorLoad i ≤ budget g * D * T
  square : (∑ i : {i // G.frozen i}, (S.exteriorLoad i.val : ℝ) ^ 2) ≤ budget g * W * T
  light : ∀ v, Fintype.card {i : Fin (C v).stations.length // thin ⟨v, i⟩} ≤ probes ℓ D
  heavy : ∀ v, Fintype.card {i : Fin (C v).stations.length // ¬thin ⟨v, i⟩} ≤ D ^ 5
  auxiliary : ∀ i, thin i → (item C i).a ≤ m * B ∧ (item C i).b ≤ m * (Routing.Private.energyConstant * B ^ 2)
  residue : ∀ i, ¬thin i → ¬G.frozen i → (item C i).a = 0
  keys : ∀ v, (S.seen v).card ≤ D ^ 14
  keyWidth : ∀ j, (Y.width j : ℝ) ≤ T / (q ℓ D : ℝ)
  selectorWidth : ∀ j, selector j → (Y.width j : ℝ) ≤ m * B / (q ℓ D : ℝ)
  reads : ∀ i, thin i → ∀ j ∈ S.reads i, selector j

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! # Converting the two sphere energies to bit widths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale.Scales
open Real Sphere.Layout

variable {g ℓ D T L B m M r t : ℕ} (s : Scales g ℓ D T L B m)
include s

private theorem root_bound {x : ℕ} (h : x ≤ budget g * D ^ 2 * (m * B * size ℓ D) ^ 2) :
    sqrt (x : ℝ) ≤ budget g * (D : ℝ) * T := by
  refine sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hx : x ≤ (budget g * D * T) ^ 2 := calc
    _ ≤ budget g * D ^ 2 * (m * B * size ℓ D) ^ 2 := h
    _ ≤ (budget g) ^ 2 * D ^ 2 * T ^ 2 := by gcongr; exact Nat.le_self_pow (by decide) _; exact s.lower
    _ = _ := by ring
  exact_mod_cast hx

theorem public_root (a : ℕ) (h : a ≤ budget g * D ^ 2 * energy ℓ D (m * B)) :
    sqrt ((m : ℝ) * B * a) ≤ budget g * (D : ℝ) * T := by
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  apply s.root_bound
  exact (Nat.mul_le_mul_left (m * B) h).trans_eq (by unfold energy; ring)

theorem private_root (a : ℕ) (h : a ≤ budget g * D ^ 2 * L * energy ℓ D (m * B)) :
    sqrt ((m : ℝ) * a) * (q ℓ D : ℝ) ^ 2 ≤ budget g * (D : ℝ) * T := by
  have hh : (m * a) * (q ℓ D) ^ 4 ≤ budget g * D ^ 2 * (m * B * size ℓ D) ^ 2 := calc
    _ ≤ m * (budget g * D ^ 2 * L * energy ℓ D (m * B)) * (q ℓ D) ^ 4 := by gcongr
    _ = _ := by unfold energy; rw [s.block]; ring
  have hk := s.root_bound hh
  push_cast at hk
  rw [show (q ℓ D : ℝ) ^ 4 = ((q ℓ D : ℝ) ^ 2) ^ 2 by ring,
    sqrt_mul (by positivity), sqrt_sq (by positivity)] at hk
  exact hk

omit s in
theorem auxiliary_root (a : ℕ) (h : a ≤ m * (Routing.Private.energyConstant * B ^ 2)) :
    sqrt ((m : ℝ) * a) ≤ budget g * ((m : ℝ) * B) := by
  have hg : Routing.Private.energyConstant ≤ (budget g) ^ 2 :=
    (show Routing.Private.energyConstant ≤ budget g by have := overhead (g := g); omega).trans
      (Nat.le_self_pow (by decide) _)
  have hh : m * a ≤ (budget g * (m * B)) ^ 2 := calc
    _ ≤ m * (m * (Routing.Private.energyConstant * B ^ 2)) := Nat.mul_le_mul_left _ h
    _ ≤ m * (m * ((budget g) ^ 2 * B ^ 2)) := by gcongr
    _ = _ := by ring
  exact sqrt_le_iff.mpr ⟨by positivity, by exact_mod_cast hh⟩

theorem small_species : (m : ℝ) * B ≤ T / (q ℓ D : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast s.qpos)]
  exact_mod_cast (Nat.mul_le_mul_left (m * B) (Nat.le_self_pow (by decide : 8 ≠ 0) _)).trans s.lower

theorem small_chunks : (chunks ℓ D : ℝ) ≤ T / (q ℓ D : ℝ) :=
  (show (chunks ℓ D : ℝ) ≤ m * B by exact_mod_cast s.smallM).trans s.small_species

/-- A record of the private state left by a crossing is a thin wire. -/
theorem hidden_width (j : ℕ) (hj : j ≤ budget g * D ^ 2 * L * energy ℓ D (m * B)) :
    (Sphere.Chunk.width m j : ℝ) ≤ T / (q ℓ D : ℝ) := by
  have hq : (0 : ℝ) < q ℓ D := by exact_mod_cast s.qpos
  have he : 8 * (budget g : ℝ) * D ≤ q ℓ D := by
    have hz : 8 * budget g * D ≤ q ℓ D := calc
      _ ≤ D * D * D := by gcongr <;> have := s.bound <;> have := s.large <;> omega
      _ = D ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_right s.Dpos (by omega)
    exact_mod_cast hz
  have hT : 2 * (q ℓ D : ℝ) ≤ T := by
    have hz : 2 * q ℓ D ≤ T := calc
      _ ≤ q ℓ D * q ℓ D := Nat.mul_le_mul_right _ (by have := s.bound; have := s.Dle; omega)
      _ = chunks ℓ D := (pow_two _).symm
      _ ≤ T := s.smallM.trans ((Nat.le_mul_of_pos_right _ s.apos).trans s.lower)
    exact_mod_cast hz
  have hs : 8 * sqrt ((m : ℝ) * j) * q ℓ D ≤ T := by
    apply (mul_le_mul_iff_left₀ hq).mp
    linarith only [s.private_root j hj, mul_le_mul_of_nonneg_right he (Nat.cast_nonneg T)]
  refine (Sphere.Chunk.width_le m j).trans ((le_div_iff₀ hq).mpr ?_)
  linarith only [hs, hT]

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale.Scales
end

/-! # Polynomial bounds on the physical vertex and bundle counts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k d ℓ : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} (hb : G.Budgets d ℓ e) (p : Profile C e) (L : ℕ)

include hb

private theorem hub_degree (v : V) (hD : 4 ≤ D) :
    S.backdrop.base.degree (.inr (.inl v)) ≤ 3 * (D ^ k) ^ 2 := by
  have hr (i : Place C) := (card_le_card (S.within i)).trans (hb.keys i.1)
  have h := S.degree_hub v
  rw [sum_place] at h
  have hsum : (∑ j, (S.reads ⟨v, j⟩).card) ≤ D ^ k * D ^ k := calc
    _ ≤ (C v).stations.length * D ^ k := by
      simpa using sum_le_card_nsmul univ (fun j => (S.reads ⟨v, j⟩).card) (D ^ k) (fun i _ => hr _)
    _ ≤ _ := Nat.mul_le_mul_right _ (G.count v)
  calc
    _ ≤ (1 + D ^ k) * D ^ k + D ^ k * D ^ k := h.trans
      (Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_left (hb.seams v) 1) (hb.keys v)) hsum)
    _ ≤ _ := by
      have hp : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
      nlinarith

theorem contacts_bound (hD : 4 ≤ D) (v : S.Position) :
    (S.backdrop.emitted p L).degree v ≤ 8 * (D ^ k) ^ 2 := by
  have h : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  rcases v with v | ⟨v, j⟩ | ⟨v, j⟩
  · rw [Backdrop.base_degree]
    rcases v with i | v | v
    · rw [degree_item]
      simp
      have hr := (card_le_card (S.within i)).trans (hb.keys i.1)
      nlinarith only [hr, h, G.chunks]
    · simp
      exact (hub_degree hb v hD).trans (Nat.mul_le_mul_right _ (by decide : 3 ≤ 8))
    · rw [degree_storage]
      simp
      nlinarith only [hb.keys v, h]
  · rw [Backdrop.degree_a]
    change S.seamDegree v + (C v).stations.length ≤ _
    nlinarith only [hb.seams v, G.count v, h]
  · rw [Backdrop.degree_b]
    nlinarith only [G.count v, h]

theorem size_bound (hD : 4 ≤ D) :
    ((Fintype.card (S.backdrop.emitted p L).V : ℝ) + Fintype.card (S.backdrop.emitted p L).E) * T ≤
      (D : ℝ) ^ radius k * W := by
  let Z := S.backdrop.emitted p L
  have hp : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have hc : Fintype.card (Place C) ≤ Fintype.card V * D ^ k := by
    rw [Fintype.card_sigma]
    simpa using sum_le_card_nsmul univ (fun v => (C v).stations.length) (D ^ k)
      (fun v _ => G.count v)
  have hv : Fintype.card Z.V ≤ Fintype.card V * (5 * D ^ k) := by
    change Fintype.card S.Position ≤ _
    simp only [Position, Vertex, Grid, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    nlinarith only [hc, Nat.mul_le_mul_left (Fintype.card V) hp, Nat.mul_le_mul_left (Fintype.card V) G.chunks]
  have he : Fintype.card Z.E ≤ Fintype.card Z.V * (8 * (D ^ k) ^ 2) := by
    have hsum := sum_le_card_nsmul univ Z.degree (8 * (D ^ k) ^ 2) (fun v _ => contacts_bound hb p L hD v)
    rw [Bundled.degree_total, card_univ, smul_eq_mul] at hsum
    omega
  have h : Fintype.card Z.V + Fintype.card Z.E ≤ Fintype.card V * D ^ radius k := calc
    _ ≤ Fintype.card Z.V * (1 + 8 * (D ^ k) ^ 2) := by rw [mul_add, mul_one]; omega
    _ ≤ Fintype.card V * (5 * D ^ k) * (1 + 8 * (D ^ k) ^ 2) := Nat.mul_le_mul_right _ hv
    _ ≤ Fintype.card V * (64 * (D ^ k) ^ 3) := by
      rw [mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith [Nat.le_self_pow (by decide : 3 ≠ 0) (D ^ k)]
    _ ≤ _ := Nat.mul_le_mul_left _ (polynomial hD k)
  calc
    _ ≤ ((Fintype.card V : ℝ) * (D : ℝ) ^ radius k) * T := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast h
    _ = (D : ℝ) ^ radius k * (Fintype.card V * T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb.occupied (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
end

/-! # The ordinary selector and residue wires fit the small budget -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Rounds
open SphereScale (Scales q size budget probes)

private theorem part_bound {I : Type} [Fintype I] (p : I → Prop) (a b : ℝ) (f : I → ℝ)
    (ha : ∀ i, p i → f i ≤ a) (hb : ∀ i, ¬ p i → f i ≤ b) :
    ∑ i, f i ≤ Fintype.card {i // p i} * a + Fintype.card {i // ¬p i} * b := by
  calc
    _ ≤ ∑ i, if p i then a else b := sum_le_sum (fun i _ => by
      split_ifs with h
      · exact ha i h
      · exact hb i h)
    _ = _ := by simp [sum_ite, Fintype.card_subtype]

variable {F U X E V K : Type} [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k ℓ L B m : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop}

namespace Geo.Raw

variable (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)

include hr in
theorem station_sum (v : V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (f : Place C → ℝ)
    (hf : ∀ i, thin i → f i ≤ a) (hg : ∀ i, ¬ thin i → f i ≤ b) :
    ∑ j, f ⟨v, j⟩ ≤ (probes ℓ D : ℝ) * a + (D : ℝ) ^ 5 * b := by
  refine (part_bound (fun j => thin ⟨v, j⟩) a b (fun j => f ⟨v, j⟩)
    (fun j => hf ⟨v, j⟩) (fun j => hg ⟨v, j⟩)).trans ?_
  gcongr
  · exact_mod_cast hr.light v
  · exact_mod_cast hr.heavy v

theorem room (hD : 1 ≤ D) {z : ℕ} (hz : z ≤ 29) :
    (D : ℝ) ^ z * (T / (q ℓ D : ℝ)) ≤ T / (D : ℝ) ^ (ℓ + 3) := by
  have h : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  unfold q
  rw [Nat.cast_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity),
    mul_comm ((D : ℝ) ^ z), mul_assoc, ← pow_add]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h (by omega)) (by positivity)

include hr s in
theorem ordinary_small (v : V) : (S.ordinaryLoad v : ℝ) ≤ T / (D : ℝ) ^ (ℓ + 3) := by
  have hD : 1600 ≤ (D : ℝ) := by exact_mod_cast (show 1600 ≤ D by have := s.bound; omega)
  have hD' : 1 ≤ (D : ℝ) := by linarith
  let x := T / (q ℓ D : ℝ)
  let y := (m : ℝ) * B / (q ℓ D : ℝ)
  have hx : 0 ≤ x := by unfold x; positivity
  have hy : 0 ≤ y := by unfold y; positivity
  have hxy : size ℓ D * y ≤ x := by
    unfold x y
    rw [← mul_div_assoc, mul_comm (size ℓ D : ℝ)]
    gcongr
    exact_mod_cast s.lower
  have per (u : V) (l : Finset K) (hl : l ⊆ S.seen u) (z : ℝ) (hz : 0 ≤ z)
      (hw : ∀ i ∈ l, (Y.width i : ℝ) ≤ z) : ∑ i ∈ l, (Y.width i : ℝ) ≤ (D : ℝ) ^ 14 * z := by
    calc
      _ ≤ l.card * z := by simpa using sum_le_card_nsmul l _ z hw
      _ ≤ _ := by gcongr; exact_mod_cast (card_le_card hl).trans (hr.keys u)
  have hv := per v (S.seen v) Subset.rfl x hx (fun k _ => hr.keyWidth k)
  let f (i : Place C) := ∑ j ∈ S.reads i, (Y.width j : ℝ)
  have hh := hr.station_sum v ((D : ℝ) ^ 14 * y) ((D : ℝ) ^ 14 * x) (by positivity) (by positivity) f
    (fun i hi => per i.1 _ (S.within i) y hy (fun j hj => hr.selectorWidth j (hr.reads i hi j hj)))
    (fun i _ => per i.1 _ (S.within i) x hx (fun j _ => hr.keyWidth j))
  have hd : (1 : ℝ) + S.seamDegree v ≤ (D : ℝ) ^ 2 := by
    have : (S.seamDegree v : ℝ) ≤ D := by exact_mod_cast (hr.seams v).trans (by have := s.large; omega)
    nlinarith
  have hl : (probes ℓ D : ℝ) * ((D : ℝ) ^ 14 * y) ≤ (D : ℝ) ^ 16 * x := by
    calc
      _ = 1600 * (D : ℝ) ^ 15 * (size ℓ D * y) := by unfold probes; push_cast; ring
      _ ≤ D * (D : ℝ) ^ 15 * x := by gcongr
      _ = _ := by ring
  have hsum : (S.ordinaryLoad v : ℝ) ≤ 2 * (D : ℝ) ^ 16 * x + (D : ℝ) ^ 19 * x := by
    unfold ordinaryLoad
    rw [sum_place]
    push_cast
    have := mul_le_mul hd hv (by positivity) (by positivity)
    unfold f at hh
    linarith only [this, hh, hl]
  refine hsum.trans (le_trans ?_ (room s.Dpos (show 20 ≤ 29 by decide)))
  change _ ≤ (D : ℝ) ^ 20 * x
  have h₁ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD' (by decide : 16 ≤ 19)) hx
  have h₂ := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ D by linarith) (show 0 ≤ (D : ℝ) ^ 19 * x by positivity)
  linarith only [h₁, h₂]

end Geo.Raw
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-!
# Three kinds of legs

A public seam and a collector can use the full local energy budget.
A private residue gains the square root of the species ratio. An
untouched auxiliary has the smaller, per-block energy bounds.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
open Classical Finset Rounds Real
open SphereScale (Scales q size budget chunks)

variable {F U X E V K : Type} [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k ℓ L B m : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop}
  (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)
  (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks ℓ D)

include hr s

private theorem first_bound (i : Place C) :
    (item C i).a ≤ budget g * D ^ 2 * SphereScale.energy ℓ D (m * B) := by
  apply Nat.le_of_mul_le_mul_left _ s.pos
  calc
    _ ≤ energyAt C L i := Nat.le_add_right _ _
    _ ≤ _ := (hr.energy i).trans_eq (by ring)

omit s in
private theorem second_bound (i : Place C) :
    (item C i).b ≤ budget g * D ^ 2 * L * SphereScale.energy ℓ D (m * B) :=
  (Nat.le_add_left _ _).trans (hr.energy i)

omit hr in
private theorem rounds_le : (SphereScale.chunks ℓ D : ℝ) ≤ budget g * (D : ℝ) * T := by
  have hk : 1 ≤ budget g * D := Nat.mul_pos (by have := SphereScale.budget_large g; omega) s.Dpos
  have h := (s.smallM.trans ((Nat.le_mul_of_pos_right _ s.apos).trans s.lower)).trans
    (Nat.le_mul_of_pos_left T hk)
  exact_mod_cast h

include ha hM in
theorem seam_le (i : E) : seamWidth C e i ≤ 5 * (budget g : ℝ) * D * T := by
  unfold seamWidth proxy
  have he : (M : ℝ) * r = m * B := by exact_mod_cast ha
  rw [he, hM]
  linarith only [s.public_root _ (hr.seamEnergy i), rounds_le s]

include ha hb hM

omit hr s hM [Fintype E] [Fintype V] in
theorem leg_eq (i : Place C) :
    legWidth C i = 4 * sqrt ((m : ℝ) * B * (item C i).a) +
      4 * sqrt ((m : ℝ) * (item C i).b) + 2 * M := by
  have he : (M : ℝ) * r = m * B := by exact_mod_cast ha
  have hf : (M : ℝ) * t = m := by exact_mod_cast hb
  unfold legWidth proxy
  rw [he, hf]
  ring

theorem leg_le (i : Place C) : legWidth C i ≤ 10 * (budget g : ℝ) * D * T := by
  have h₁ := s.public_root _ (first_bound hr s i)
  have h₂ := s.private_root _ (second_bound hr i)
  have hq : 1 ≤ (q ℓ D : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast s.qpos)
  have hh := (le_mul_of_one_le_right (sqrt_nonneg _) hq).trans h₂
  rw [leg_eq ha hb, show (M : ℝ) = SphereScale.chunks ℓ D by rw [hM]]
  linarith only [h₁, hh, rounds_le s]

theorem thin_le (i : Place C) (hi : thin i) : legWidth C i ≤ 10 * (budget g : ℝ) * ((m : ℝ) * B) := by
  obtain ⟨h₁, h₂⟩ := hr.auxiliary i hi
  have hm : (M : ℝ) ≤ m * B := by rw [hM]; exact_mod_cast s.smallM
  have h₃ : sqrt ((m : ℝ) * B * (item C i).a) ≤ m * B := by
    refine sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [pow_two]
    gcongr
    exact_mod_cast h₁
  have h₄ : (m : ℝ) * B ≤ budget g * ((m : ℝ) * B) :=
    le_mul_of_one_le_left (by positivity) (by exact_mod_cast (show 1 ≤ budget g by
      have := SphereScale.budget_large g; omega))
  rw [leg_eq ha hb]
  linarith only [h₃, h₄, hm, SphereScale.Scales.auxiliary_root (g := g) _ h₂]

theorem residue_le (i : Place C) (hi : ¬G.frozen i) :
    legWidth C i ≤ (D : ℝ) ^ 3 * (T / (q ℓ D : ℝ)) := by
  have hD : 16 ≤ (D : ℝ) := by exact_mod_cast (show 16 ≤ D by have := s.bound; omega)
  have hg : (budget g : ℝ) ≤ D := by exact_mod_cast (show budget g ≤ D by have := s.large; omega)
  have hq : 1 ≤ (q ℓ D : ℝ) := by exact_mod_cast s.qpos
  have hv : 10 * (budget g : ℝ) ≤ (D : ℝ) ^ 3 := by nlinarith [sq_nonneg ((D : ℝ) - 4)]
  by_cases hthin : thin i
  · exact (hr.thin_le s ha hb hM i hthin).trans (mul_le_mul hv s.small_species (by positivity) (by positivity))
  · have hk := s.private_root _ (second_bound hr i)
    have hh : sqrt ((m : ℝ) * (item C i).b) * (q ℓ D : ℝ) ≤ (budget g : ℝ) * D * T :=
      (mul_le_mul_of_nonneg_left (by nlinarith : (q ℓ D : ℝ) ≤ (q ℓ D : ℝ) ^ 2) (sqrt_nonneg _)).trans hk
    have hm : (M : ℝ) * (q ℓ D : ℝ) ≤ T := (le_div_iff₀ (by positivity)).mp (hM ▸ s.small_chunks)
    have hd : 4 * (budget g : ℝ) * D + 2 ≤ (D : ℝ) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg D),
        mul_le_mul_of_nonneg_right hD (sq_nonneg (D : ℝ))]
    rw [leg_eq ha hb, hr.residue i hthin hi, Nat.cast_zero, mul_zero, sqrt_zero, mul_zero,
      zero_add, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    linarith only [hh, hm, mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg T)]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
end

/-! # The frozen square budget after chunk encoding -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
open Classical Finset Rounds Real
open SphereScale (Scales size budget)

variable {F U X E V K : Type} [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k ℓ L B m : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop}
  (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)
  (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks ℓ D)

private theorem three_sq (x y z : ℝ) :
    (4 * x + 4 * y + 2 * z) ^ 2 ≤ 48 * (x ^ 2 + y ^ 2) + 12 * z ^ 2 := by
  nlinarith only [sq_nonneg (2 * x - 2 * y), sq_nonneg (2 * x - z), sq_nonneg (2 * y - z)]

include s ha hb
omit [Fintype E] [Fintype V] in
private theorem leg_square (i : Place C) :
    legWidth C i ^ 2 ≤ 48 * ((m : ℝ) * B / L) * energyAt C L i + 12 * (M : ℝ) ^ 2 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast s.pos
  have hB : (L : ℝ) ≤ B := by
    exact_mod_cast (s.block ▸ Nat.le_mul_of_pos_right L (pow_pos s.qpos 4))
  have h : (m : ℝ) * B * (item C i).a + m * (item C i).b ≤ (m : ℝ) * B / L * energyAt C L i := by
    unfold energyAt
    push_cast
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    linarith only [mul_le_mul_of_nonneg_left hB (show 0 ≤ (m : ℝ) * (item C i).b by positivity)]
  rw [leg_eq ha hb]
  refine (three_sq _ _ _).trans ?_
  rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]
  linarith only [h]

include hr hM

theorem frozen_square :
    (∑ i : {i // G.frozen i}, (S.stationLoad i.val) ^ 2) ≤ 122 * (budget g : ℝ) * W * T := by
  have hW : 0 ≤ W := le_trans (by positivity) hr.occupied
  have hL : (0 : ℝ) < L := by exact_mod_cast s.pos
  have hm : M ≤ T := hM ▸ s.smallM.trans ((Nat.le_mul_of_pos_right _ s.apos).trans s.lower)
  let N := Fintype.card {i // G.frozen i}
  have hm' : (N : ℝ) * M ^ 2 ≤ (budget g : ℝ) * W * T := calc
    _ ≤ (N : ℝ) * T ^ 2 := by gcongr
    _ ≤ N * (D : ℝ) * T * T := by
      rw [pow_two, ← mul_assoc]
      gcongr
      exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast s.Dpos)
    _ ≤ _ := mul_le_mul_of_nonneg_right hr.collectors (by positivity)
  let c := (m : ℝ) * B / L
  have hc : c * (∑ i : {i // G.frozen i}, (energyAt C L i.val : ℝ)) ≤
      (budget g : ℝ) * W * T := calc
    _ ≤ c * ((budget g : ℝ) * L * size ℓ D * W) :=
      mul_le_mul_of_nonneg_left hr.collected (by unfold c; positivity)
    _ = (budget g : ℝ) * W * ((m : ℝ) * B * size ℓ D) := by unfold c; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast s.lower) (by positivity)
  have hp (i : {i // G.frozen i}) : S.stationLoad i.val ^ 2 ≤
      2 * (S.exteriorLoad i.val : ℝ) ^ 2 + 96 * c * energyAt C L i.val + 24 * (M : ℝ) ^ 2 := by
    unfold stationLoad c
    nlinarith only [leg_square s ha hb i.val, sq_nonneg ((S.exteriorLoad i.val : ℝ) - legWidth C i.val)]
  have := sum_le_sum (fun i (_ : i ∈ univ) => hp i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at this
  unfold N at hm'
  linarith only [this, hc, hm', hr.square]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
end

/-! # Charges of insertion tables, hubs, and storage positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y) {e : E → ℕ} (p : Profile C e) (L : ℕ)

omit [Field F] [Fintype K] in
theorem seen_load (v : V) : ∑ i ∈ S.seen v, Y.width i ≤ S.ordinaryLoad v := by
  unfold ordinaryLoad
  exact (Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_add_right _ _)

theorem item_load (i : Place C) :
    ((S.backdrop.emitted p L).arity (.inl (.inl i)) : ℝ) ≤ S.stationLoad i + S.ordinaryLoad i.1 := by
  have hs := S.backdrop.station_le p L (.inl i)
  have hu := (sum_le_sum_of_subset (f := Y.width) (S.within i)).trans (S.seen_load i.1)
  have hp : push S.backdrop.owner (legWidth C) (.inl i) = legWidth C i := by
    simp [push]
  rw [hp, arity_item] at hs
  unfold stationLoad exteriorLoad
  have hv : ((∑ k ∈ S.reads i, Y.width k : ℕ) : ℝ) ≤ S.ordinaryLoad i.1 := Nat.cast_le.mpr hu
  push_cast at hs hv ⊢
  linarith only [hs, hv]

theorem hubs_load (v : V ⊕ V) :
    ((S.backdrop.emitted p L).arity (.inl (.inr v)) : ℝ) ≤ S.ordinaryLoad (Sum.elim id id v) := by
  have hs := S.backdrop.station_le p L (.inr v)
  have hp : push S.backdrop.owner (legWidth C) (.inr v) = 0 := by simp [push]
  rw [hp, add_zero] at hs
  refine hs.trans (Nat.cast_le.mpr ?_)
  cases v with
  | inl v => exact S.arity_hub v
  | inr v => rw [arity_storage]; exact S.seen_load v

theorem total_base : ∑ i, S.backdrop.base.width i ≤ ∑ v, S.ordinaryLoad v := by
  have h := S.backdrop.base.width_le_source (fun v : V => .inr (.inl v))
    (fun e => ⟨(S.start e.2).val, rfl⟩)
  exact h.trans (sum_le_sum (fun v _ => S.arity_hub v))

theorem ties_zero (i j : Place C) :
    (S.backdrop.emitted p L).ties (.inl (.inl i)) (.inl (.inl j)) = 0 := by
  have he (e : (S.backdrop.emitted p L).E) :
      (∀ w, (S.backdrop.emitted p L).src e ≠ .inl (.inl w)) ∨
        (∀ w, (S.backdrop.emitted p L).dst e ≠ .inl (.inl w)) := by
    rcases e with e | e | e
    · left; intro w h; cases h
    · left; intro w h; cases h
    · right; intro w h; cases h
  unfold Bundled.ties
  rw [← sum_add_distrib]
  apply sum_eq_zero
  intro e _
  rcases he e with hs | ht
  · rw [ite_eq_right (fun h => hs i h.1), ite_eq_right (fun h => hs j h.2), zero_add]
  · rw [ite_eq_right (fun h => ht j h.2), ite_eq_right (fun h => ht i h.1), zero_add]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! # Concentration estimates for an emitted profile -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k d ℓ : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  (G : S.Geo P k) (hD : D = 2 ^ d) (hd : 4 ≤ D)
  {e : E → ℕ} (hb : G.Budgets d ℓ e) (p : Profile C e) (L : ℕ)

include hd hb

private theorem ordinary_le (v : V) : (S.ordinaryLoad v : ℝ) ≤ T :=
  (hb.ordinary v).trans (div_le_self (by positivity)
    (one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))))

private theorem sum_width : (∑ i, ((S.backdrop.emitted p L).width i : ℝ)) ≤
    (k + 1) * W * (1 + (d : ℝ)) := by
  have hp : (∑ i, (S.backdrop.base.width i : ℝ)) ≤ W := calc
    _ ≤ ∑ v, (S.ordinaryLoad v : ℝ) := by exact_mod_cast S.total_base
    _ ≤ (Fintype.card V : ℝ) * T := by
      simpa using sum_le_card_nsmul univ _ _ (fun v _ => G.ordinary_le hd hb v)
    _ ≤ _ := hb.occupied
  have hw : 0 ≤ W := (by positivity : 0 ≤ (Fintype.card V : ℝ) * T) |>.trans hb.occupied
  linarith only [S.backdrop.emitted_width p L, hp, hb.total, mul_nonneg hw (Nat.cast_nonneg d)]

private theorem max_core (v : (G.layout hD hd p L).Mobile) :
    ((S.backdrop.emitted p L).arity v.val : ℝ) ≤ T / (D : ℝ) ^ (ℓ + 2) := by
  let B := (T : ℝ) / (D : ℝ) ^ (ℓ + 3)
  have h₀ : 0 ≤ B := by unfold B; positivity
  have hcap : 2 * B ≤ T / (D : ℝ) ^ (ℓ + 2) := by
    unfold B
    rw [show ℓ + 3 = (ℓ + 2) + 1 by omega, pow_succ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have h : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
    linarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (T : ℝ) * (D : ℝ) ^ (ℓ + 2) by positivity)]
  obtain ⟨(i | v) | s, hv⟩ := v
  · have hi : ¬ G.frozen i := fun h => hv ((G.fixed_item hD hd p L _).mpr h)
    have hl (j) : S.left j ≠ i := fun h => hi (h ▸ G.left j)
    have hr (j) : S.right j ≠ i := fun h => hi (h ▸ G.right j)
    have hload := S.item_load p L i
    simp [stationLoad, exteriorLoad, hl, hr] at hload
    have hi' := (add_le_add (hb.residue i hi) (hb.ordinary i.1))
    exact (hload.trans hi').trans (by rw [← two_mul]; exact hcap)
  · exact ((S.hubs_load p L v).trans (hb.ordinary _)).trans ((le_mul_of_one_le_left h₀ (by norm_num)).trans hcap)
  · have hm : 0 < M := by
      rcases s with ⟨_, j⟩ | ⟨_, j⟩ <;> exact Nat.zero_lt_of_lt j.isLt
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < Real.sqrt M)).mp
      ((S.backdrop.chamber_le p L s).trans (hb.chambers _))

private theorem square_frozen :
    (∑ v : (G.layout hD hd p L).Frozen, ((S.backdrop.emitted p L).arity v.val : ℝ) ^ 2) ≤
      radius k * W * T := by
  have hW : 0 ≤ W := le_trans (by positivity) hb.occupied
  have hcount : (Fintype.card {i // G.frozen i} : ℝ) * T ≤ k * W := calc
    _ ≤ Fintype.card {i // G.frozen i} * (D : ℝ) * T := by
      gcongr
      exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast (show 1 ≤ D by omega))
    _ ≤ _ := hb.collectors
  rw [← (G.frozenEquiv hD hd p L).sum_comp]
  calc
    _ ≤ ∑ i : {i // G.frozen i}, (2 * (S.stationLoad i.val) ^ 2 + 2 * (T : ℝ) ^ 2) := by
      apply sum_le_sum
      intro i _
      have ht := (S.item_load p L i.val).trans (add_le_add_right (G.ordinary_le hd hb i.val.1) _)
      have h₁ := pow_le_pow_left₀ (by positivity) ht 2
      change ((S.backdrop.emitted p L).arity (.inl (.inl i.val)) : ℝ) ^ 2 ≤ _
      nlinarith only [h₁, sq_nonneg (S.stationLoad i.val - T)]
    _ = 2 * (∑ i : {i // G.frozen i}, (S.stationLoad i.val) ^ 2) +
        2 * (Fintype.card {i // G.frozen i} * T) * T := by
      rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
      ring
    _ ≤ 4 * (k : ℝ) * W * T := by
      linarith only [hb.square, mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg T)]
    _ ≤ _ := by gcongr; exact_mod_cast (show 4 * k ≤ radius k by unfold radius; omega)

theorem caps : (G.layout hD hd p L).Caps P ℓ := by
  have hW : 0 ≤ W := le_trans (by positivity) hb.occupied
  have hrad : 2 * (k + 1) ≤ radius k := by unfold radius; omega
  refine ⟨G.host_count hd, size_bound hb p L hd, ?_, ?_, ?_, G.square_frozen hD hd hb p L,
    G.max_core hD hd hb p L, ?_, ?_, ?_⟩
  · intro v
    refine ((contacts_bound hb p L hd v).trans ?_).trans (polynomial hd k)
    exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by positivity) (by decide))
  · rw [← Fintype.card_congr (G.frozenEquiv hD hd p L)]
    exact hb.collectors.trans (by gcongr; omega)
  · intro v
    obtain ⟨i, rfl⟩ := (G.frozenEquiv hD hd p L).surjective v
    calc
      _ ≤ S.stationLoad i.val + S.ordinaryLoad i.val.1 := S.item_load p L i.val
      _ ≤ (k : ℝ) * D * T + T := add_le_add (hb.max _ i.property) (G.ordinary_le hd hb _)
      _ ≤ ((k : ℝ) + 1) * D * T := by
        have hh : 1 ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
        linarith only [le_mul_of_one_le_left (Nat.cast_nonneg T) hh]
      _ ≤ _ := by gcongr; exact_mod_cast (show k + 1 ≤ radius k by omega)
  · intro v w
    obtain ⟨i, rfl⟩ := (G.frozenEquiv hD hd p L).surjective v
    obtain ⟨j, rfl⟩ := (G.frozenEquiv hD hd p L).surjective w
    change ((S.backdrop.emitted p L).ties (.inl (.inl i.val)) (.inl (.inl j.val)) : ℝ) ≤ _
    rw [ties_zero, Nat.cast_zero]
    positivity
  · have hx := G.external hD hd p L
    have hh := (S.backdrop.emitted p L).sum_mobile (fun v => ¬ (G.layout hD hd p L).fixed v)
      (fun i he => he (hx.1 i)) (fun i he => he (hx.2 i))
    calc
      _ ≤ 2 * (∑ i, ((S.backdrop.emitted p L).width i : ℝ)) := by exact_mod_cast hh
      _ ≤ 2 * ((k + 1) * W * (1 + (d : ℝ))) := mul_le_mul_of_nonneg_left (G.sum_width hd hb p L) (by positivity)
      _ = (2 * ((k : ℝ) + 1)) * W * (1 + d) := by ring
      _ ≤ _ := by gcongr; exact_mod_cast hrad
  · exact (G.sum_width hd hb p L).trans (by gcongr; exact_mod_cast (show k + 1 ≤ radius k by omega))

variable {u : ℕ} (hu : 0 < u)

abbrev output := (G.layout hD hd p L).finish (G.external hD hd p L) hu

omit hb in
theorem sum_output (x : Val a) (y : Val b) :
    ∑ p : Profile C e, p.sign * (G.output hD hd p L hu).diagram.eval x y =
      ∑ s, Surface.eval L C e (S.param x y s) := by
  rw [← S.eval x y (Surface.eval L C e)]
  have ht := S.backdrop.expansion (d := e) L Profile.widths x y
  refine Eq.trans ?_ (ht.trans ?_)
  · apply sum_congr rfl
    intro p _
    rw [output, Fanout.eval_finish, Bundled.eval_diagram]
  · congr!

theorem concentrated {N : ℕ} (hN : Fanout.exponent (radius k) ℓ ≤ N) (hs : u * D ^ N ≤ T) :
    Concentrated P (G.output hD hd p L hu) N d ℓ :=
  (G.layout hD hd p L).concentrated P hD hd (by unfold radius; omega) hN hu hs _
    (G.caps hD hd hb p L)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
end
