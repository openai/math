import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Ledger
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Remnants

/-! # Inserting a finite family of isolated scalar tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Packing
open scoped Classical

private def discard {V I : Type} (X : V ⊕ I → Type) (empty : ∀ i, X (.inr i) → False) :
    (Σ j, X j) ≃ Σ j, X (.inl j) where
  toFun
    | ⟨.inl v, p⟩ => ⟨v, p⟩
    | ⟨.inr i, p⟩ => (empty i p).elim
  invFun t := ⟨.inl t.1, t.2⟩
  left_inv := by
    rintro ⟨v|i, p⟩
    · rfl
    · exact (empty i p).elim
  right_inv _ := rfl

variable {F I : Type} [Fintype I] {x y : Wire} (G : Diagram F x y) (c : I → F)

abbrev scalarTable (v : F) : Table F := ⟨.unit, .unit, fun _ _ => v⟩

abbrev withScalars : Diagram F x y where
  V := G.V ⊕ I
  E := G.E
  table := Sum.elim G.table (scalarTable ∘ c)
  src := (discard (fun j => slots ((Sum.elim G.table (scalarTable ∘ c)) j).1) (fun _ => Empty.elim)).trans G.src
  dst := (discard (fun j => slots ((Sum.elim G.table (scalarTable ∘ c)) j).2.1) (fun _ => Empty.elim)).trans G.dst

theorem scalar_portEnd (i : slots x ⊕ slots y) : portEnd (G.withScalars c) i = .inl (portEnd G i) := by
  cases i <;> rfl

theorem scalar_source (i : G.E) : (G.withScalars c).source i = .inl (G.source i) := rfl
theorem scalar_target (i : G.E) : (G.withScalars c).target i = .inl (G.target i) := rfl

theorem eval_scalars [Field F] (a : Val x) (b : Val y) :
    (G.withScalars c).eval a b = (∏ i, c i) * G.eval a b := by
  unfold eval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  change (∏ i : G.V ⊕ I, (G.withScalars c).vertex a b z i) = _
  rw [Fintype.prod_sum_type, mul_comm]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Counting terminal collectors

Each occupied cell starts with one extra vacuum collector. A new
collector can only be created by using a full movement allowance.
Charge its crossings to incidences at occupied cells.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
open Finset
open scoped Classical
variable {F T V E X : Type} {r t : ℕ} [Fintype V] (s : Stage F r t T V E X)

theorem card_collectors :
    Fintype.card {i : Sphere.Layout.Place s.scene.cell //
      (Sphere.Layout.item s.scene.cell i).label.role = .collector} = s.collectors := by
  have eq (r : Role) : (if r = .collector then 1 else 0) = r.collected 1 := by
    cases r <;> simp [Role.collected]
  rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  unfold collectors
  apply sum_congr rfl
  intro v _
  simp only [Sphere.Layout.item, tally]
  let l := (s.scene.cell v).stations
  let f := fun a : s.St => a.label.role.collected 1
  trans ∑ i : Fin l.length, f (l.get i)
  · exact sum_congr rfl fun i _ => eq _
  change _ = (l.map f).sum
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [←List.map_ofFn, List.ofFn_get]

theorem hits_le_visits [Fintype E] (src : E → V) (incident : ∀ e, e ∈ s.edges (src e)) :
    (∑ e, s.hits e) ≤ ∑ v, s.visits v := by
  rw [← sum_fiberwise univ src]
  apply sum_le_sum
  intro v _
  apply sum_le_sum_of_subset
  intro e he
  rw [← (mem_filter.mp he).2]
  exact incident e

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private SphereScale
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)
  [Field F] [Field K] [Algebra K F] (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)

def collectorCount (c : P.Occupied) : ℕ :=
  1 + ∑ v ∈ P.grid.stations c, if ¬P.mobile v then 1 else 0

theorem plant_collector_cell (t : ℕ) (c : P.Occupied) :
    (P.plant p s).tally t (fun r _ => r.collected 1) c = P.collectorCount c := by
  let wt := fun v => if ¬P.mobile v then 1 else 0
  unfold Stage.tally collectorCount
  change ((Template.cells p P.tag s c).stations.map (fun u => u.label.role.collected 1)).sum =
    1 + ∑ v ∈ P.grid.stations c, wt v
  rw [Template.cells_stations, ←sum_coe_sort, ←(Grid.number P.grid.stationRank (P.grid.stations c)).sum_comp]
  simp only [List.map_cons, List.map_append, List.map_ofFn, List.sum_cons, List.sum_append, List.sum_ofFn]
  change 1 + ((∑ _ : Fin n, 0) + ∑ i, (P.tag (n := n) c (.inl (P.grid.label c i))).role.collected 1)
    = 1 + ∑ i, wt (P.grid.label c i)
  simp only [sum_const_zero, zero_add]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases h : P.mobile (P.grid.label c i) <;> simp [wt, tag, h, Role.collected]

theorem plant_collectors :
    (P.plant p s).collectors = Fintype.card P.Occupied + Fintype.card {v // ¬P.mobile v} := by
  let wt := fun v => if ¬P.mobile v then 1 else 0
  have each c : (P.plant p s).tally 0 (fun r _ => r.collected 1) c =
      1 + ∑ v ∈ P.grid.stations c, wt v := P.plant_collector_cell p s 0 c
  unfold Stage.collectors
  simp only [each, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, mul_one]
  simp only [Grid.stations, sum_filter]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, wt, sum_boole, Nat.cast_id, Fintype.card_subtype]

theorem final_count {ℓ : ℕ} (sc : Scales g ℓ D T m b d)
    {t : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam ((Val x × Val y) × Template.Keys p)}
    (reach : (P.plant p s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) (D ^ 5) t)
    (visits : ∀ v, t.visits v ≤ budget g * D ^ 2) :
    (t.collectors : ℝ) * D * T ≤ budget g * W := by
  have total : D ^ 5 * t.expired ≤ ∑ v, t.visits v := by
    have ht := (reach.budget.limits (fun _ => rfl) (P.plant_zero p s _) rfl).2.2.2.1
    refine ht.trans (t.hits_le_visits (fun e => e.val.1) ?_)
    intro e
    rw [reach.edges_eq, Stage.edges, List.mem_toFinset]
    exact ((P.plant_layout p s sc.Rpos).incident _ e).mpr (Or.inl rfl)
  have hb : budget g * D ^ 2 ≤ D ^ 5 := calc
    _ ≤ D * D ^ 2 := Nat.mul_le_mul_right _ (by have := sc.large; omega)
    _ ≤ _ := by rw [←pow_succ']; exact Nat.pow_le_pow_right sc.Dpos (by decide)
  have exp : t.expired ≤ Fintype.card P.Occupied := by
    apply Nat.le_of_mul_le_mul_left _ (pow_pos sc.Dpos 5)
    apply total.trans
    simpa [mul_comm] using sum_le_sum (fun v (_ : v ∈ univ) => (visits v).trans hb)
  have cnt := reach.collectors
  rw [P.plant_collectors] at cnt
  have bnd : t.collectors ≤ 2 * Fintype.card P.Occupied + Fintype.card {v // ¬P.mobile v} := by omega
  have occ : (Fintype.card P.Occupied : ℝ) * D * T ≤ W := by
    simpa only [Occupied, Fintype.card_coe] using P.occupied
  calc
    _ ≤ (2 * Fintype.card P.Occupied + Fintype.card {v // ¬P.mobile v} : ℝ) * D * T := by
      gcongr
      exact_mod_cast bnd
    _ ≤ 3 * W := by linarith only [occ, P.immobile]
    _ ≤ budget g * W := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show 3 ≤ budget g by have := budget_large g; omega))
      (le_trans (by positivity) occ)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Uniform room for the motion of planted stations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m H U : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)
  [Field F] [Field K] [Algebra K F] (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)

def initialEnergy (D T b d n m H : ℕ) : ℝ :=
  reserve D b d n m H + m * (8 * (200 * (D : ℝ) * T) ^ 2 / (d * b : ℕ))

theorem plant_room (hr : 0 < d * b) (hm : 0 < m) (hh : 0 < H) (M N : ℕ)
    (size : (2 * m * H * (100 * D + n + 1 + 2 * g) : ℕ) + initialEnergy D T b d n m H ≤ (2 * m * H * M : ℕ))
    (en : (1 + 4 * g : ℕ) * initialEnergy D T b d n m H ≤ N)
    {z : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam ((Val x × Val y) × Template.Keys p)}
    (hz : (P.plant p s).Reach m (2 * g) H U z) : z.Room M N := by
  let S := P.plant p s
  let A := S.ledger m H
  let seam c := ∑ e ∈ S.edges c, A.seam e
  let total c := A.mobile c + A.collected c + seam c
  have ht c : (total c : ℝ) ≤ initialEnergy D T b d n m H := P.plant_local_energy p s hr H c
  apply hz.room hm hh (P.plant_layout p s hr).unique M N
  · intro c
    have pos : (S.scene.cell c).positions.length ≤ 100 * D + n + 1 + 2 * g := by
      rw [Cell.positions, List.length_append, List.length_map, List.length_map]
      exact Nat.add_le_add (P.plant_length p s c) ((P.plant_layout p s hr).degree c)
    have hs : (seam c : ℝ) ≤ initialEnergy D T b d n m H :=
      ((Nat.cast_le (α := ℝ)).mpr (Nat.le_add_left _ _)).trans (ht c)
    change (2 * m * H) * (S.scene.cell c).positions.length + seam c ≤ 2 * m * H * M
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_add]
    exact (add_le_add ((Nat.cast_le (α := ℝ)).mpr (Nat.mul_le_mul_left _ pos)) hs).trans size
  · intro c
    change A.cost (2 * g) c + (1 + 2 * (2 * g)) * (seam c) ≤ N
    calc
      _ ≤ (1 + 4 * g) * (total c) := by
        dsimp only [total, Ledger.cost]
        rw [show 2 * (2 * g) = 4 * g by omega, mul_add, mul_add]
        exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _) _
      _ ≤ N := by
        apply (Nat.cast_le (α := ℝ)).mp
        rw [Nat.cast_mul]
        exact (mul_le_mul_of_nonneg_left (ht c) (Nat.cast_nonneg _)).trans en

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# A separate bank of scalar stations

The new bank uses the input host and block indices. All new
stations are mobile, have no edges, and pay the unit floor charge.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Packing Finset
open scoped Classical

variable {F : Type} {x y : Wire} {h D T R g u : ℕ} {W : ℝ}
    (P : Input F x y h D T R g W) (Q : LocalTerm F x y h u) (c : P.Occupied → F)

local notation "G" => Q.diagram.withScalars c

def scalarPlace : Q.diagram.V ⊕ P.Occupied → (Q.V ⊕ P.V) × Cell h
  | .inl v => (.inl (Q.frame.place v).1, (Q.frame.place v).2)
  | .inr i => (.inr i.val.1, i.val.2)

private theorem scalar_one : Function.Injective (P.scalarPlace Q) := by
  rintro (a|a) (b|b) e
  · exact congrArg Sum.inl (Q.one (Prod.ext (Sum.inl.inj (Prod.mk.inj e).1) (Prod.mk.inj e).2))
  · cases (Prod.mk.inj e).1
  · cases (Prod.mk.inj e).1
  · exact congrArg Sum.inr (Subtype.ext (Prod.ext (Sum.inr.inj (Prod.mk.inj e).1) (Prod.mk.inj e).2))

abbrev scalarAdj (N : Q.V → Finset Q.V) : Q.V ⊕ P.V → Finset (Q.V ⊕ P.V) :=
  Sum.elim (fun v => (N v).map Function.Embedding.inl) (fun _ => ∅)

private theorem scalar_sym {N : Q.V → Finset Q.V} (hn : ∀ v w, w ∈ N v → v ∈ N w) :
    ∀ v w, w ∈ P.scalarAdj Q N v → v ∈ P.scalarAdj Q N w := by
  rintro (v|v) w hw
  · obtain ⟨z, hz, rfl⟩ := mem_map.mp hw
    exact mem_map_of_mem _ (hn v z hz)
  · exact (notMem_empty w hw).elim

abbrev scalarFreeze : Freeze (G) where
  frozen := Sum.elim Q.freeze.frozen (fun _ => False)
  exterior i := by rw [Diagram.scalar_portEnd]; exact Q.freeze.exterior i
  separate i := Q.freeze.separate i

abbrev scalarFrame : (P.scalarFreeze Q c).Frame (Q.V ⊕ P.V) h where
  place := P.scalarPlace Q
  frozen := Sum.elim Q.frame.frozen (fun _ => False)
  keep v := by cases v with | inl v => exact Q.frame.keep v | inr _ => rfl
  N := P.scalarAdj Q Q.frame.N
  C := P.scalarAdj Q Q.frame.C
  ns := P.scalar_sym Q Q.frame.ns
  cs := P.scalar_sym Q Q.frame.cs
  sub v := by
    cases v with
    | inl v => exact map_subset_map.mpr (Q.frame.sub v)
    | inr _ => exact Subset.rfl
  group e := Q.frame.group e
  edge e := mem_map_of_mem _ (Q.frame.edge ⟨e.val, e.property⟩)
  full e := mem_map_of_mem _ (Q.frame.full e)

private theorem scalar_width (v w : (G).V) :
    u ∣ Fintype.card {e // (G).source e = v ∧ (G).target e = w} := by
  rcases v with v|v <;> rcases w with w|w <;>
    simp only [Fintype.card_subtype, Diagram.scalar_source, Diagram.scalar_target, Sum.inl.injEq,
      reduceCtorEq, false_and, and_false, filter_false, card_empty, dvd_zero]
  simpa only [Fintype.card_subtype] using Q.width v w

abbrev weighted : LocalTerm F x y h u where
  V := Q.V ⊕ P.V
  diagram := G
  freeze := P.scalarFreeze Q c
  frame := P.scalarFrame Q c
  one := P.scalar_one Q
  width v w := by simpa only [Fintype.card_eq_nat_card] using P.scalar_width Q c v w
  charge := Sum.elim Q.charge (fun _ => (u : ℝ))
  cover v := by
    cases v with
    | inl v => exact Q.cover v
    | inr _ => exact Nat.cast_le.mpr (Nat.zero_le _)
  floor v := by cases v with | inl v => exact Q.floor v | inr _ => rfl

theorem weighted_eval [Field F] (a : Val x) (b : Val y) :
    (P.weighted Q c).diagram.eval a b = (∏ v, c v) * Q.diagram.eval a b :=
  Q.diagram.eval_scalars c a b

theorem weighted_portEnd (i : slots x ⊕ slots y) :
    portEnd (P.weighted Q c).diagram i = .inl (portEnd Q.diagram i) :=
  Q.diagram.scalar_portEnd c i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Concentration after incorporating the scalar weights

Each occupied cell pays the floor charge once. The input bound
on occupied cells covers these charges without a factor growing
with the number of blocks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

variable {F : Type} {x y : Wire} {h D T R g u C d ℓ : ℕ} {W : ℝ}
    (P : Input F x y h D T R g W) (Q : LocalTerm F x y h u) (c : P.Occupied → F)

local notation "A" => P.weighted Q c

namespace Input

def scalarFixed : Q.freeze.Fixed ≃ (A).freeze.Fixed where
  toFun v := ⟨.inl v.val, v.property⟩
  invFun
    | ⟨.inl v, h⟩ => ⟨v, h⟩
    | ⟨.inr _, h⟩ => False.elim h
  left_inv _ := rfl
  right_inv := by rintro ⟨v|i, h⟩; rfl; exact False.elim h

def scalarCore : Q.freeze.Core ⊕ P.Occupied ≃ (A).freeze.Core where
  toFun
    | .inl v => ⟨.inl v.val, v.property⟩
    | .inr i => ⟨.inr i, fun h => h⟩
  invFun
    | ⟨.inl v, h⟩ => .inl ⟨v, h⟩
    | ⟨.inr i, _⟩ => .inr i
  left_inv := by rintro (_|_) <;> rfl
  right_inv := by rintro ⟨_|_, _⟩ <;> rfl

theorem scalar_sum :
    (∑ v : (A).freeze.Core, (A).charge v.val) =
      (∑ v : Q.freeze.Core, Q.charge v.val) + Fintype.card P.Occupied * u := by
  rw [← (P.scalarCore Q c).sum_comp, Fintype.sum_sum_type]
  change (∑ v : Q.freeze.Core, Q.charge v.val) + (∑ _ : P.Occupied, (u : ℝ)) = _
  simp only [sum_const, card_univ, nsmul_eq_mul]

end Input

variable {P Q}

theorem Concentrated.weighted (hc : Concentrated P Q C d ℓ) (c : P.Occupied → F)
    (hD : 2 ≤ D) (hu : u * D ^ ℓ ≤ T) : Concentrated P (P.weighted Q c) (C + 2) d ℓ := by
  have hd : 0 < D := by omega
  have hw : 0 ≤ W := (by positivity : (0 : ℝ) ≤ (univ.image P.place).card * D * T) |>.trans P.occupied
  have he : D ^ C + 1 ≤ D ^ (C + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpow : D ^ C ≤ D ^ (C + 2) := (Nat.le_add_right ..).trans he
  have hC : (C : ℝ) ≤ (C + 2 : ℕ) := Nat.cast_le.mpr (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Fintype.card (Q.V ⊕ P.V) ≤ _
    rw [Fintype.card_sum]
    calc
      _ ≤ D ^ C * Fintype.card P.V + Fintype.card P.V := Nat.add_le_add_right hc.cells _
      _ = (D ^ C + 1) * Fintype.card P.V := by rw [add_mul, one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ he
  · rintro (v|v)
    · exact (card_map _).le.trans ((hc.coreDegree v).trans (by omega))
    · exact Nat.zero_le _
  · rintro (v|v)
    · exact (card_map _).le.trans ((hc.fullDegree v).trans hpow)
    · exact Nat.zero_le _
  · rw [← Fintype.card_congr (P.scalarFixed Q c)]
    exact hc.frozenCount.trans (mul_le_mul_of_nonneg_right hC hw)
  · intro i
    obtain ⟨v, rfl⟩ := (P.scalarFixed Q c).surjective i
    exact (hc.frozenMax v).trans (by gcongr)
  · rw [← (P.scalarFixed Q c).sum_comp]
    exact hc.frozenSquare.trans (by gcongr)
  · rintro ⟨v|j, hv⟩
    · exact hc.coreMax ⟨v, hv⟩
    · change (u : ℝ) * D ^ ℓ ≤ T
      exact_mod_cast hu
  · rw [P.scalar_sum]
    have hu' : u ≤ D * T := ((Nat.le_mul_of_pos_right _ (pow_pos hd _)).trans hu).trans
      (Nat.le_mul_of_pos_left _ hd)
    have cost : (Fintype.card P.Occupied : ℝ) * u ≤ W := calc
      _ ≤ (Fintype.card P.Occupied : ℝ) * (D * T) := mul_le_mul_of_nonneg_left (by exact_mod_cast hu') (by positivity)
      _ ≤ _ := by simpa only [Input.Occupied, Fintype.card_coe, mul_assoc] using P.occupied
    refine (add_le_add hc.coreSum cost).trans ?_
    have hh : (1 : ℝ) ≤ (1 + (d : ℝ)) ^ 2 := one_le_pow₀ (by simp)
    rw [Nat.cast_add, Nat.cast_ofNat]
    linarith only [mul_le_mul_of_nonneg_left hh hw, hw]

end OAI.LinearAlgebra.MatrixExponent.Rounds
end
