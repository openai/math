import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Debit.Legs
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Initial

/-! # Counting linked spans and exterior pins at one station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj}
    {x y : Wire} {G : Diagram F x y} (p : S.Presentation r G)

/-- Count exposed ends in two ways, first in diagram order and then
by the local pin numbering. -/
private theorem exterior_sum (v : G.V) :
    Packing.exterior G id v = ∑ s : B S.e,
      if S.peer r (p.vertex v, s) = none then S.width r (p.vertex v, s) else 0 := by
  let f (e : G.End) := if G.station e = v ∧ S.peer r (p.toSeating.ends e).1 = none then 1 else 0
  have hin (e : G.E) : S.peer r (p.toSeating.ends (.inl (.inr e))).1 ≠ none := by
    rw [(p.internal e).1]; simp
  have hout (e : G.E) : S.peer r (p.toSeating.ends (.inr (.inr e))).1 ≠ none := by
    rw [(p.proper _ _ (p.internal e).1).1]; simp
  have h : ∑ e, f e = Packing.exterior G id v := by
    simp only [Diagram.End, Fintype.sum_sum_type, f, p.input, p.output, hin, hout, and_true,
      and_false, ↓reduceIte, sum_const_zero, add_zero]
    simp only [Diagram.station, Packing.exterior, Fintype.card_subtype, card_filter, id_eq]
    rfl
  rw [← h, ← G.portEquiv.sum_comp, Fintype.sum_sigma, Fintype.sum_eq_single v]
  · let c (t : S.LocalPin r (p.vertex v)) := if S.peer r (p.vertex v, t.1) = none then 1 else 0
    have hc (t : G.Port v) : f (G.portEquiv ⟨v, t⟩) = c (p.pin v t) := by
      simp only [f, G.station_port, true_and, p.toSeating.ends_at]
      rfl
    simp only [hc]
    rw [(p.pin v).sum_comp c, Fintype.sum_sigma]
    refine sum_congr rfl fun s _ => ?_
    by_cases h : S.peer r (p.vertex v, s) = none <;> simp [c, h]
  · intro u hu
    exact sum_eq_zero fun t _ => by simp [f, G.station_port, hu]

/-- Each linked span contributes its full width, independently of
direction. This counts both ends of a loop at the same station. -/
theorem arity_links (u : ℕ) (v : G.V)
    (uniform : ∀ i : S.Span, (S.peer r i).isSome → S.width r i = u) :
    (univ.filter fun s : B S.e => (S.peer r (p.vertex v, s)).isSome).card * u +
      Packing.exterior G id v = G.arity v := by
  have h : G.arity v = ∑ s : B S.e, S.width r (p.vertex v, s) := by
    simpa only [Diagram.arity, Diagram.Port, Fintype.card_sum, card_slots, Fintype.card_sigma,
      Fintype.card_fin] using Fintype.card_congr (p.pin v)
  rw [h, p.exterior_sum, ← Nat.nsmul_eq_mul, ← sum_const, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  cases he : S.peer r (p.vertex v, s) with
  | none => simp
  | some q => simp [uniform _ (by rw [he]; rfl)]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# The square budget after subtracting exterior wires

Rounding and routing cost at most a multiple of T/D² per
station. Squaring this error leaves an O(D T²) term even when
an occupied cell retains D⁵ frozen stations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
open Finset Rounds
open SphereScale (Scales size chunks)
open scoped Classical

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k σ L B m u n : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} (sc : Scales g σ D T L B m)
  (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks σ D)

private theorem squares (x y z : ℝ) : (4 * x + 4 * y + 4 * z) ^ 2 ≤ 48 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

include sc in
private theorem rate (x y : ℕ) :
    (m : ℝ) * B * x + m * y ≤ T / ((L : ℝ) * size σ D) * (L * x + y) := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr sc.pos
  have hs : (0 : ℝ) < size σ D := Nat.cast_pos.mpr sc.apos
  have hl : (L : ℝ) ≤ B := by exact_mod_cast (sc.block ▸ Nat.le_mul_of_pos_right L (pow_pos sc.qpos 4))
  have ht : (m : ℝ) * B * size σ D ≤ T := by exact_mod_cast sc.lower
  calc
    _ ≤ ((m : ℝ) * B / L) * (L * x + y) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL]
      linarith only [mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ m * y by positivity)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [div_le_div_iff₀ hL (mul_pos hL hs)]
      linarith only [mul_le_mul_of_nonneg_right ht hL.le]

private theorem margin (D c σ u T : ℕ) (hd : 4 ≤ D)
    (hs : u * D ^ (Fanout.exponent c σ) ≤ T) : (u : ℝ) * ((D : ℝ) ^ c + 1) ≤ T / (D : ℝ) ^ 2 := by
  have hh : c + 3 ≤ Fanout.exponent c σ := by
    have h := Nat.le_self_pow (by decide : 2 ≠ 0) (c + σ + 1)
    unfold Fanout.exponent; omega
  have ht : u * D ^ (c + 3) ≤ T := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hh)).trans hs
  have hp : (1 : ℝ) ≤ (D : ℝ) ^ c := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))
  refine (le_div_iff₀ (by positivity)).mpr (le_trans ?_ (show (u : ℝ) * D ^ (c + 3) ≤ T by exact_mod_cast ht))
  have hd' : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
  have he : (D : ℝ) ^ c + 1 ≤ (D : ℝ) ^ c * D := by
    linarith only [hp, mul_le_mul_of_nonneg_left hd' (zero_le_one.trans hp)]
  rw [show c + 3 = (c + 1) + 2 by omega, pow_add, pow_succ (D : ℝ) c, ← mul_assoc]
  gcongr

include sc ha hb hM in
theorem internal_square (hD : D = 2 ^ n) (hd : 4 ≤ D) (hbud : G.Budgets n σ e) (p : Profile C e)
    (hs : u * D ^ (Fanout.exponent (radius k) σ) ≤ T) (i : Place C) {x : ℝ} (hx : 0 ≤ x)
    (he : x + S.exteriorLoad i ≤ (((S.backdrop.emitted p L).pad u).arity (.inl (.inl i)) : ℝ) + u) :
    x ^ 2 ≤ 48 * (T / ((L : ℝ) * size σ D) * (energyAt C L i : ℝ) + ((T : ℝ) / D ^ 2) ^ 2) := by
  let E := S.backdrop.emitted p L
  let j : E.V := .inl (.inl i)
  have hp : (E.pad u).arity j ≤ E.arity j + u * D ^ (radius k) :=
    (E.arity_pad u j).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ((G.caps hD hd hbud p L).degree j)) _)
  have ht : ((E.pad u).arity j : ℝ) + u ≤ E.arity j + T / (D : ℝ) ^ 2 := by
    have he' : ((E.pad u).arity j : ℝ) ≤ E.arity j + u * (D : ℝ) ^ (radius k) := by exact_mod_cast hp
    linarith only [he', margin D _ _ _ _ hd hs]
  have ho : (S.ordinaryLoad i.1 : ℝ) ≤ T / (D : ℝ) ^ 2 := (hbud.ordinary _).trans (by
    gcongr
    · exact_mod_cast (show 1 ≤ D by omega)
    · omega)
  have hc : (M : ℝ) ≤ T / (D : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast (Nat.mul_le_mul_right _ (hM ▸ sc.smallM)).trans sc.smallR
  have hload : (E.arity j : ℝ) ≤ S.exteriorLoad i + legWidth C i + S.ordinaryLoad i.1 := S.item_load p L i
  rw [Raw.leg_eq ha hb] at hload
  let A := Real.sqrt ((m : ℝ) * B * (item C i).a)
  let B' := Real.sqrt ((m : ℝ) * (item C i).b)
  have hi : x ≤ 4 * A + 4 * B' + 4 * (T / (D : ℝ) ^ 2) := by
    change x + S.exteriorLoad i ≤ ((E.pad u).arity j : ℝ) + u at he
    unfold A B'; linarith only [he, ht, hload, hc, ho]
  refine ((pow_le_pow_left₀ hx hi 2).trans (squares ..)).trans ?_
  unfold A B' energyAt
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Nat.cast_add, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add_left (rate sc _ _) _) (by norm_num)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
end

/-! # Restricting the collected energy to one occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Ledger
open Finset Surface
open scoped Classical

variable {V : Type} [Fintype V] {I : V → Type} [∀ v, Fintype (I v)]

theorem fiber {A : Type} [AddCommMonoid A] (frozen : Sigma I → Prop)
    [DecidablePred frozen] (f : {i // frozen i} → A) (v : V) :
    (∑ i, if i.val.1 = v then f i else 0) =
      ∑ j : {j : I v // frozen ⟨v, j⟩}, f ⟨⟨v, j.val⟩, j.property⟩ := by
  let eq : (Σ v, {j : I v // frozen ⟨v, j⟩}) ≃ {i // frozen i} := {
    toFun := fun t => ⟨⟨t.1, t.2.val⟩, t.2.property⟩
    invFun := fun t => ⟨t.val.1, ⟨t.val.2, t.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← eq.sum_comp, Fintype.sum_sigma, sum_eq_single v]
  · exact sum_congr rfl fun _ _ => ite_eq_left rfl
  · intro i _ hi
    exact sum_eq_zero fun _ _ => ite_eq_right hi
  · simp

variable {F Z E X : Type} {r t : ℕ} (s : Stage F r t Z V E X) (j : ℕ)
    (frozen : Layout.Place s.scene.cell → Prop)

omit [Fintype V] in
theorem collected (v : V) (hf : ∀ i, frozen i → (Layout.item s.scene.cell i).label.role = .collector) :
    (∑ i : {i : Fin (s.scene.cell v).stations.length // frozen ⟨v, i⟩},
      energyOf j (Layout.item s.scene.cell ⟨v, i.val⟩)) ≤ s.tally j Role.collected v := by
  let f (a : s.St) := a.label.role.collected (energyOf j a)
  have he : s.tally j Role.collected v = ∑ i, f ((s.scene.cell v).stations.get i) := by
    rw [← List.sum_ofFn]
    change _ = (List.ofFn (f ∘ (s.scene.cell v).stations.get)).sum
    rw [← List.map_ofFn, List.ofFn_get]
    rfl
  rw [he]
  let t := univ.filter (fun i => frozen ⟨v, i⟩)
  refine le_trans ?_ (sum_le_sum_of_subset (subset_univ t))
  rw [sum_subtype t (fun _ => mem_filter_univ _) (fun i => f ((s.scene.cell v).stations.get i))]
  apply sum_le_sum
  intro i _
  change _ ≤ (Layout.item s.scene.cell ⟨v, i.val⟩).label.role.collected _
  rw [hf _ i.property]; rfl

theorem charges {A : Type} [Fintype A] (f E : A → ℝ) (T D L x : ℝ)
    (hT : 0 ≤ T) (hD : 0 < D) (hL : 0 < L) (hx : 0 ≤ x)
    (hc : (Fintype.card A : ℝ) ≤ D ^ 5) (he : ∑ i, E i ≤ x)
    (h : ∀ i, (f i) ^ 2 ≤ 48 * (T / L * E i + (T / D ^ 2) ^ 2)) :
    ∑ i, (f i) ^ 2 ≤ 128 * (T * x / L + D * T ^ 2) := by
  have hh := sum_le_sum (s := univ) (fun i _ => h i)
  simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hh
  calc
    _ ≤ _ := hh
    _ ≤ 48 * (T / L * x + D ^ 5 * (T / D ^ 2) ^ 2) := by gcongr
    _ = 48 * (T * x / L + D * T ^ 2) := by field_simp
    _ ≤ _ := by gcongr; norm_num

end OAI.LinearAlgebra.MatrixExponent.Sphere.Ledger
end

/-! # Aggregating squared collector charges in one cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Ledger
open Finset Rounds Surface
open scoped Classical

variable {F Z V E X : Type} [Fintype V] {r t : ℕ}

theorem sq_cell (s : Stage F r t Z V E X) (j : ℕ) (fixed : Layout.Place s.scene.cell → Prop)
    (f : {i // fixed i} → ℝ) (v : V) {σ D T : ℕ}
    (hcard : Fintype.card {i : Fin (s.scene.cell v).stations.length // fixed ⟨v, i⟩} ≤ D ^ 5)
    (hf : ∀ i, fixed i → (Layout.item s.scene.cell i).label.role = .collector)
    (hD : 0 < D) (hL : 0 < (j : ℝ) * SphereScale.size σ D)
    (hsq : ∀ i, (f i) ^ 2 ≤ 48 * ((T : ℝ) / ((j : ℝ) * SphereScale.size σ D) *
      energyOf j (Layout.item s.scene.cell i.val) + ((T : ℝ) / D ^ 2) ^ 2)) :
    (∑ i, if i.val.1 = v then (f i) ^ 2 else 0) ≤
      128 * ((T : ℝ) * s.tally j Role.collected v / ((j : ℝ) * SphereScale.size σ D) + D * (T : ℝ) ^ 2) := by
  let I := {i : Fin (s.scene.cell v).stations.length // fixed ⟨v, i⟩}
  let x (i : I) : {j // fixed j} := ⟨⟨v, i.val⟩, i.property⟩
  let e (i : I) := energyOf j (Layout.item s.scene.cell (x i).val)
  have he : (∑ i, e i) ≤ s.tally j Role.collected v := collected s j fixed v hf
  refine (fiber fixed (fun i => (f i) ^ 2) v).le.trans ?_
  exact charges (f ∘ x) (fun i => (e i : ℝ)) _ _ _ _ (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr hD) hL (Nat.cast_nonneg _) (by exact_mod_cast hcard)
    (by exact_mod_cast he) (fun i => hsq (x i))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Ledger
end

/-! # Aligning live child slots with the vertices of their parent -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)

omit [Finite K] in
theorem child_frozen (i : V) : Children.frozen U.slot (U.slot (B.child p i)) ↔
    (B.term p).freeze.frozen i := by
  rw [Children.frozen_slot]
  refine (Children.fixed_iff U.dyadic U.large G ((G.layout U.dyadic U.large p j).place i).1).trans ?_
  cases i <;> rfl

/-- A live child at these coordinates arises from exactly one vertex based
at this parent. The equality applies to weights in any additive monoid. -/
theorem sum_child (live : Coloring.B m → Coloring.B h → Coloring.B U.childBits → Bool)
    (hl : ∀ i : U.template.scheme.Vtx, live (U.split i.1).1 i.2.1 (U.split i.1).2 = true ↔
      i ∈ Set.range (B.vertex p))
    (v : P.Occupied) {α : Type*} [AddCommMonoid α] (f : Coloring.B U.childBits → α) :
    (∑ i, if live (a.coord v).1 (a.coord v).2 i then f i else 0) =
      ∑ j : V, if (S).home (root j) = v then f (U.slot (B.child p j)) else 0 := by
  let loc (i : Coloring.B U.childBits) : U.template.scheme.Vtx :=
    (U.split.symm ((a.coord v).1, i), (a.coord v).2, 0)
  have lv (i) : live (a.coord v).1 (a.coord v).2 i = true ↔ loc i ∈ Set.range (B.vertex p) := by
    simpa only [loc, Equiv.apply_symm_apply] using hl (loc i)
  have spot (j : V) (hj : (S).home (root j) = v) : B.vertex p j = loc (U.slot (B.child p j)) := by
    obtain ⟨h₁, h₂⟩ := B.address p j
    rw [hj] at h₁ h₂
    exact Prod.ext (U.split.eq_symm_apply.mpr h₁) (Prod.ext h₂ (Fin.eq_zero _))
  symm
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => U.slot (B.child p j)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lv _).mpr ⟨j, spot j (Finset.mem_filter.mp hj).2⟩⟩
  · intro i hi j hj e
    apply (B.vertex p).injective
    rw [spot i (Finset.mem_filter.mp hi).2, spot j (Finset.mem_filter.mp hj).2, e]
  · intro i hi
    obtain ⟨j, hj⟩ := (lv _).mp (Finset.mem_filter.mp hi).2
    obtain ⟨h₁, h₂⟩ := B.address p j
    rw [hj] at h₁ h₂
    simp only [loc, Equiv.apply_symm_apply, Prod.mk.injEq] at h₁
    have hv := a.coord.injective (Prod.ext h₁.1.symm h₂.symm)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, h₁.2.symm⟩

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Frozen station charges in the ordered diagram -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
open Finset
local notation "Q'" => B.term p

def frozenPlaces : {i // G.frozen i} ≃ (Q').freeze.Fixed :=
  (G.frozenEquiv U.dyadic U.large p j).trans
    (((H).pad u).fixedEquiv (G.external U.dyadic U.large p j))

omit [Finite K] in
theorem home_frozen (i : {i // G.frozen i}) :
    (S).home (root (B.frozenPlaces p i).val) = i.val.1 := rfl

omit [Finite K] in
theorem charge_frozen (i : {i // G.frozen i}) :
    (Q').charge (B.frozenPlaces p i).val = ((((S).backdrop.emitted p j).pad u).arity (.inl (.inl i.val)) : ℝ) + u :=
  ((H).pad u).old_charge (G.external U.dyadic U.large p j) (((S).backdrop.emitted p j).divisible_pad u U.pos) _

omit [Finite K] in
theorem exterior_frozen (i : {i // G.frozen i}) :
    Packing.exterior (Q').diagram id (B.frozenPlaces p i).val = (S).exteriorLoad i.val := by
  let D := ((H).routed (B.rules.script p j) u).drawing
  have eq (q : slots x ⊕ slots y) :
      Packing.portEnd (Q').diagram q = .inl (.inl (.inl (Sum.elim (S).left (S).right q))) := by
    change Packing.portEnd D.diagram q = _
    rw [D.exterior]
    cases q <;> rfl
  have he (q : slots x ⊕ slots y) :
      Packing.portEnd (Q').diagram q = (B.frozenPlaces p i).val ↔ Sum.elim (S).left (S).right q = i.val := by
    rw [eq]
    change Sum.inl (Sum.inl (Sum.inl _)) = Sum.inl (Sum.inl (Sum.inl _)) ↔ _
    simp only [Sum.inl.injEq]
  unfold Packing.exterior Sharing.exteriorLoad
  simp only [Fintype.card_eq_nat_card]
  exact congrArg₂ (· + ·) (Nat.card_congr (Equiv.subtypeEquivRight (fun a => he (.inl a))))
    (Nat.card_congr (Equiv.subtypeEquivRight (fun b => he (.inr b))))

private theorem arity_cover {F : Type} {x y : Wire} (G : Diagram F x y) (v : G.V) :
    (Packing.exterior G id v : ℝ) ≤ G.arity v := by
  have h := Packing.site_arity G id v
  have hh : Packing.push id (fun i => (G.arity i : ℝ)) v = G.arity v := by simp [Packing.push]
  rw [hh] at h
  exact h.symm ▸ le_add_of_nonneg_right (Nat.cast_nonneg _)

def internalCharge (i : (Q').diagram.V) := (Q').charge i - (Packing.exterior (Q').diagram id i : ℝ)

omit [Finite K] in
theorem internal_nonneg (i : (Q').diagram.V) : 0 ≤ B.internalCharge p i :=
  sub_nonneg.mpr ((arity_cover _ i).trans ((Q').cover i))

omit [Finite K] in
theorem square_place {σ b l : ℕ} (hbud : G.Budgets n σ s.scene.level)
    (sc : SphereScale.Scales g σ D T j b l) (ha : M * r = l * b) (hb : M * t = l) (hM : M = SphereScale.chunks σ D)
    (hs : u * D ^ (Layout.Fanout.exponent (Sharing.radius k) σ) ≤ T) (i : {i // G.frozen i}) :
    (B.internalCharge p (B.frozenPlaces p i).val) ^ 2 ≤
      48 * (T / ((j : ℝ) * SphereScale.size σ D) * (energyOf j (Layout.item s.scene.cell i.val) : ℝ) + ((T : ℝ) / D ^ 2) ^ 2) := by
  refine Sharing.Geo.internal_square sc ha hb hM U.dyadic U.large hbud p hs i.val (B.internal_nonneg p _) ?_
  rw [internalCharge, charge_frozen, exterior_frozen, sub_add_cancel]

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Frozen square bound for a single occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
open Finset
local notation "Q'" => B.term p

omit [Finite K] in
theorem cell_square {σ b l : ℕ} {thin : Layout.Place s.scene.cell → Prop} {selector : _ → Prop}
    (hr : G.Raw σ j b l s.scene.level thin selector) (sc : SphereScale.Scales g σ D T j b l)
    (ha : M * r = l * b) (hb : M * t = l) (hM : M = SphereScale.chunks σ D) (hk : Sharing.allocation g σ ≤ k)
    (hu : u * D ^ (Layout.Fanout.exponent (Sharing.radius k) σ) ≤ T)
    (hf : ∀ i, G.frozen i → (Layout.item s.scene.cell i).label.role = .collector ∧ ¬thin i)
    (v : P.Occupied) :
    (∑ i : (Q').freeze.Fixed, if (S).home (root i.val) = v then (B.internalCharge p i.val) ^ 2 else 0) ≤
      128 * ((T : ℝ) * s.tally j Role.collected v / ((j : ℝ) * SphereScale.size σ D) + D * (T : ℝ) ^ 2) := by
  let Z := {i // G.frozen i}
  let I := {i : Fin (s.scene.cell v).stations.length // G.frozen ⟨v, i⟩}
  let f := fun i : Z => B.internalCharge p (B.frozenPlaces p i).val
  have hcard : Fintype.card I ≤ D ^ 5 :=
    (Fintype.card_subtype_mono _ _ fun i hi => (hf ⟨v, i⟩ hi).2).trans (hr.heavy v)
  have hbud := hr.budgets sc ha hb hM hk n
  have hsq (i : Z) := B.square_place p hbud sc ha hb hM hu i
  have hc := Sphere.Ledger.sq_cell s j G.frozen f v hcard (fun i hi => (hf i hi).1) sc.Dpos
    (mul_pos (Nat.cast_pos.mpr sc.pos) (Nat.cast_pos.mpr sc.apos)) hsq
  refine le_trans ?_ hc
  rw [← (B.frozenPlaces p).sum_comp]
  exact sum_le_sum fun i _ => by
    rw [home_frozen]
    split_ifs <;> rfl

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Counting the internal bits displayed by a printed blueprint -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
open Finset
local notation "Q'" => B.term p

variable {l : ℕ} (A : Coloring.B m → Coloring.B h → Geometry.Blueprint U.childBits
    (Children.degree d U.childBits) U.spanBits l)

abbrev view (U : Printer F K N m d h ℓ M r t q D k n u j z)
    (A : Coloring.B m → Coloring.B h → Geometry.Blueprint U.childBits
      (Children.degree d U.childBits) U.spanBits l)
    (i : U.template.scheme.Vtx) := A (U.split i.1).1 i.2.1 (U.split i.1).2

structure Displayed : Prop where
  live : ∀ i, (view U A i).live = true ↔ i ∈ Set.range (B.vertex p)
  peer : ∀ i, (view U A i).peer = (U.template.scheme.pattern (B.record p).1 i).peer 0

namespace Displayed
variable {B p A} (ok : B.Displayed p A)
    (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

local notation "X'" => U.template.scheme
local notation "out" => Prod.fst (B.record p)

include ok in
theorem count_links (i : V) : (view U A (B.vertex p i)).links =
    (univ.filter fun r : Coloring.B (X').e => ((X').peer out (B.vertex p i, r)).isSome).card := by
  have h : (B.vertex p i).2.2 = 0 := Fin.eq_zero _
  unfold Geometry.Outline.links
  rw [ok.peer]
  simp only [Scheme.peer, Option.isSome_map, h]
  rfl

include ok hw in
theorem toll (i : V) :
    ((view U A (B.vertex p i)).toll : ℝ) * u = B.internalCharge p i := by
  have h := (B.frame p hw).presentation.arity_links u i ((B.frame p hw).uniform)
  have hb : (view U A (B.vertex p i)).links * u + Packing.exterior (Q').diagram id i = (Q').diagram.arity i := by
    rw [ok.count_links i]
    exact h
  have e := congrArg (fun j : ℕ => (j : ℝ)) hb
  rw [Nat.cast_add, Nat.cast_mul] at e
  have hl := (ok.live _).mpr ⟨i, rfl⟩
  rw [Geometry.Outline.toll, ite_eq_left hl, internalCharge, B.charge, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  linarith only [e]

theorem view_at (i : V) :
    view U A (B.vertex p i) =
      A (a.coord ((S).home (root i))).1 (a.coord ((S).home (root i))).2 (U.slot (B.child p i)) := by
  have h := B.address p i
  unfold view
  rw [h.1, h.2]

end Displayed
end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Maximum toll of a frozen or mobile child -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
local notation "Q'" => B.term p

variable {l : ℕ} (A : Coloring.B m → Coloring.B h → Geometry.Blueprint U.childBits
    (Children.degree d U.childBits) U.spanBits l)

namespace Displayed
variable {B p A} (ok : B.Displayed p A)
    (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)
include ok hw

/-- An unoccupied slot costs nothing. At a live slot the toll is
at most the full charge of its vertex. -/
private theorem toll_charge (v : P.Occupied) (i : Coloring.B U.childBits) :
    (A (a.coord v).1 (a.coord v).2 i).toll = 0 ∨ ∃ w : V, U.slot (B.child p w) = i ∧
      ((A (a.coord v).1 (a.coord v).2 i).toll : ℝ) * u ≤ (Q').charge w := by
  let y : U.template.scheme.Vtx := (U.split.symm ((a.coord v).1, i), (a.coord v).2, 0)
  have e : view U A y = A (a.coord v).1 (a.coord v).2 i := by
    simp only [view, y, Equiv.apply_symm_apply]
  by_cases h : (view U A y).live
  · obtain ⟨w, ew⟩ := (ok.live _).mp h
    have he := (B.address p w).1
    rw [ew] at he
    simp only [y, Equiv.apply_symm_apply, Prod.mk.injEq] at he
    refine Or.inr ⟨w, he.2.symm, ?_⟩
    rw [← e, ← ew, ok.toll hw]
    exact sub_le_self _ (Nat.cast_nonneg _)
  · left
    rw [← e, Geometry.Outline.toll, ite_eq_right h]

variable {C σ : ℕ} (hc : Concentrated P (B.term p) C n σ)
include hc

theorem large (v : P.Occupied) (i : Coloring.B U.childBits)
    (hi : decide (Children.frozen U.slot i) = true) :
    (A (a.coord v).1 (a.coord v).2 i).toll * u ≤ C * D * T := by
  rcases ok.toll_charge hw v i with h | ⟨w, he, h⟩
  · simp [h]
  have hf : (Q').freeze.frozen w := (B.child_frozen p w).mp (he.symm ▸ of_decide_eq_true hi)
  exact_mod_cast h.trans (hc.frozenMax ⟨w, hf⟩)

theorem small (v : P.Occupied) (i : Coloring.B U.childBits)
    (hi : decide (Children.frozen U.slot i) = false) :
    (A (a.coord v).1 (a.coord v).2 i).toll * u * D ^ σ ≤ T := by
  rcases ok.toll_charge hw v i with h | ⟨w, he, h⟩
  · simp [h]
  have hf : ¬ (Q').freeze.frozen w := by
    rw [← B.child_frozen p w, he]
    exact of_decide_eq_false hi
  have hm := mul_le_mul_of_nonneg_right h (pow_nonneg (Nat.cast_nonneg (α := ℝ) D) σ)
  exact_mod_cast hm.trans (hc.coreMax ⟨w, hf⟩)

end Displayed
end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Translating charges between child labels and physical stations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
open Finset
local notation "Q'" => B.term p

variable {l : ℕ} (A : Coloring.B m → Coloring.B h → Geometry.Blueprint U.childBits
    (Children.degree d U.childBits) U.spanBits l)
namespace Displayed
variable {B p A} (ok : B.Displayed p A)
    (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

local notation "atCell" => (fun v => A (Prod.fst (a.coord v)) (Prod.snd (a.coord v)))
local notation "fixed" => (fun i => decide (Children.frozen U.slot i))
local notation "home" => (Layout.Sharing.home S ∘ Print.root)
local notation "slot" => (fun i => U.slot (B.child p i))

private theorem restrict_sum {I α : Type} [Fintype I] [AddCommMonoid α]
    (A B : I → Prop) [DecidablePred A] [DecidablePred B] (f : I → α) :
    (∑ i, if A i then if B i then f i else 0 else 0) =
      ∑ i : {i // B i}, if A i.val then f i.val else 0 := by
  rw [← sum_subtype (univ.filter B) (fun _ => mem_filter_univ _) (fun i => if A i then f i else 0), sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases h : B i <;> simp [h]

include ok in
private theorem sum_fixed (v : P.Occupied) {α : Type} [AddCommMonoid α] (f : Coloring.B U.childBits → α) :
    (∑ i, if (atCell v i).live = true ∧ fixed i = true then f i else 0) =
      ∑ i : (Q').freeze.Fixed, if home i.val = v then f (slot i.val) else 0 := by
  simp only [ite_and]
  have h := B.sum_child p (fun i j c => (A i j c).live) ok.live v (fun i => if fixed i then f i else 0)
  refine h.trans ?_
  refine Eq.trans ?_ (restrict_sum (fun i => home i = v) (Q').freeze.frozen (fun i => f (slot i)))
  apply sum_congr rfl
  intro i _
  simp only [decide_eq_true_eq, B.child_frozen, Function.comp_apply]

include ok in
theorem count (v : P.Occupied) : (atCell v).count fixed = G.collectorCount v := by
  rw [B.collectorCount_eq p, Geometry.Blueprint.count, Fintype.card_subtype, card_filter, card_filter]
  exact ok.sum_fixed v (fun _ => 1)

include ok hw in
theorem square (v : P.Occupied) :
    ((atCell v).square fixed : ℝ) * (u : ℝ) ^ 2 =
      ∑ i : (Q').freeze.Fixed, if home i.val = v then (B.internalCharge p i.val) ^ 2 else 0 := by
  let f (i : Coloring.B U.childBits) := (((atCell v i).toll : ℝ) * u) ^ 2
  have h := ok.sum_fixed v f
  refine Eq.trans ?_ (h.trans ?_)
  · rw [Geometry.Blueprint.square, Nat.cast_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    by_cases hl : (atCell v i).live = true
    · simp only [hl, true_and, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow, ite_mul, zero_mul, f, mul_pow]
    · simp [hl, Geometry.Outline.toll]
  · apply sum_congr rfl
    intro i _
    split
    · rename_i hi
      have he := ok.toll hw i.val
      rw [view_at] at he
      change (S).home (root i.val) = v at hi
      rw [hi] at he
      exact congrArg (·^2) he
    · rfl

include ok hw in
theorem mobile (v : P.Occupied) :
    ((atCell v).mobile fixed : ℝ) * u ≤ Packing.push home (Q').charge v := by
  let f (i : Coloring.B U.childBits) := ((atCell v i).toll : ℝ) * u
  have h := B.sum_child p (fun i j c => (A i j c).live) ok.live v f
  refine le_trans ?_ (h.le.trans ?_)
  · rw [Geometry.Blueprint.mobile, Nat.cast_sum, sum_mul]
    apply sum_le_sum
    intro i _
    by_cases hl : (atCell v i).live = true
    · simp only [hl, ite_true, f]
      gcongr
      split <;> simp
    · simp [hl, Geometry.Outline.toll]
  · unfold Packing.push
    apply sum_le_sum
    intro i _
    by_cases hi : (S).home (root i) = v
    · simp only [Function.comp_apply, hi, ite_true]
      have he := ok.toll hw i
      rw [view_at, hi] at he
      exact he.le.trans (sub_le_self _ (Nat.cast_nonneg _))
    · simp only [Function.comp_apply, ite_eq_right hi, le_refl]

end Displayed
end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Every genuine blueprint satisfies the finite quota check -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
open Finset
local notation "Q'" => B.term p

variable {l : ℕ} (A : Coloring.B m → Coloring.B h → Geometry.Blueprint U.childBits
    (Children.degree d U.childBits) U.spanBits l)
namespace Displayed
variable {B p A} (ok : B.Displayed p A)
    (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

local notation "atCell" => (fun v => A (Prod.fst (a.coord v)) (Prod.snd (a.coord v)))
local notation "fixed" => (fun i => decide (Children.frozen U.slot i))

include ok hw in
theorem quota {σ b c ν : ℕ} {thin : Layout.Place s.scene.cell → Prop} {selector : Key P.Occupied s.hidden → Prop}
    (hr : G.Raw σ j b c s.scene.level thin selector) (sc : SphereScale.Scales g σ D T j b c)
    (ha : M * r = c * b) (hb : M * t = c) (hM : M = SphereScale.chunks σ D) (hk : k = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T)
    (hf : ∀ i, G.frozen i → (Layout.item s.scene.cell i).label.role = .collector ∧ ¬thin i)
    (v : P.Occupied) (credits : Geometry.Credits g σ D ν)
    (ht : D ^ 5 * G.collectorCount v ≤ credits.time (Fin.last ν))
    (he : Geometry.clip ν (j * SphereScale.energy σ D (c * b)) (s.tally j Role.collected v) ≤
      credits.power (Fin.last ν)) :
    Geometry.Quota (Input.terminalExponent g σ) n (T / u) fixed (atCell v) credits := by
  have hu' : u * D ^ (Layout.Fanout.exponent (Sharing.radius k) σ) ≤ T := by rw [hk]; exact hu
  have hbud := hr.budgets sc ha hb hM hk.ge n
  have hc : Concentrated P (B.term p) (Input.terminalExponent g σ) n σ :=
    B.concentrated p (G.concentrated U.dyadic U.large hbud p j U.pos (by rw [hk]; rfl) hu)
  have hlow : u ≤ T := (Nat.le_mul_of_pos_right u (pow_pos sc.Dpos _)).trans hu
  refine Geometry.Quota.make sc fixed (atCell v) credits U.pos hlow he ?_ ?_ ?_
    (ok.large hw hc v) (ok.small hw hc v)
  · rw [ok.count v]; exact ht
  · exact (ok.square hw v).le.trans (B.cell_square p hr sc ha hb hM hk.ge hu' hf v)
  · rw [ok.count v]
    have h := (ok.mobile hw v).trans (B.cell_charge p hr sc ha hb hM hk hu v)
    exact_mod_cast h

end Displayed
end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end
