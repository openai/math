import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Sphere.Scalar.Term
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares
import OAI.LinearAlgebra.MatrixExponent.Sphere.Footprint.Load
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Ledger
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Host
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Remnants
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting

/-! # Initial energy estimates at the chosen public and private scales -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale.Scales
open Routing.Private

variable {g ℓ D T m b d : ℕ} (s : Scales g ℓ D T m b d)
private theorem constants (c : ℕ) :
    200 + 1600 * (c + 1) ≤ 2000 * (c + 1) ∧ 2000 * (c + 1) + 16 ≤ 10000000 * (c + 1) := by
  constructor <;> omega

include s

private theorem block_le : b ≤ m * size ℓ D := by
  rw [s.block]
  exact Nat.mul_le_mul_left m (Nat.pow_le_pow_right s.qpos (by decide))

theorem reserve_bound :
    Input.reserve D b d (probes ℓ D) m (energy ℓ D (d * b)) ≤
      2000 * (energyConstant + 1) * D * m * energy ℓ D (d * b) := by
  let R := d * b
  let A := size ℓ D
  let H := R * A ^ 2
  have h₁ : m * R ≤ m * R * A := Nat.le_mul_of_pos_right _ s.apos
  have h₂ : d * (energyConstant * b ^ 2) ≤ energyConstant * m * R * A := calc
    _ = (energyConstant * R) * b := by unfold R; ring
    _ ≤ (energyConstant * R) * (m * A) := Nat.mul_le_mul_left _ s.block_le
    _ = _ := by ring
  unfold Input.reserve probes
  change 2 * m * H * (100 * D) + 1600 * D * A * (m * R + d * (energyConstant * b ^ 2)) ≤ _
  calc
    _ ≤ 2 * m * H * (100 * D) + 1600 * D * A * (m * R * A + energyConstant * m * R * A) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add h₁ h₂)) _
    _ = (200 + 1600 * (energyConstant + 1)) * (D * m * H) := by unfold H; ring
    _ ≤ (2000 * (energyConstant + 1)) * (D * m * H) := Nat.mul_le_mul_right (D * m * H)
      (constants energyConstant).1
    _ = _ := by change _ = 2000 * (energyConstant + 1) * D * m * H; ring

private theorem square_upper :
    (T : ℝ) ^ 2 ≤ 4 * (d * b : ℕ) * energy ℓ D (d * b) := by
  have ht : T ^ 2 ≤ 4 * (d * b) * energy ℓ D (d * b) := calc
    _ ≤ (2 * (d * b * size ℓ D)) ^ 2 := Nat.pow_le_pow_left s.upper _
    _ = _ := by unfold energy; ring
  exact_mod_cast ht

theorem initial_bound :
    (1 + 4 * g : ℕ) * Input.initialEnergy D T b d (probes ℓ D) m (energy ℓ D (d * b)) ≤
      (budget g * D ^ 2 * m * energy ℓ D (d * b) : ℕ) := by
  let H := energy ℓ D (d * b)
  have ht : 8 * (200 * (D : ℝ) * T) ^ 2 / (d * b : ℕ) ≤ (1280000 * D ^ 2 * H : ℕ) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr s.Rpos)).mpr
    calc
      _ = (320000 * (D : ℝ) ^ 2) * T ^ 2 := by ring
      _ ≤ (320000 * (D : ℝ) ^ 2) * (4 * (d * b : ℕ) * H) :=
        mul_le_mul_of_nonneg_left s.square_upper (by positivity)
      _ = _ := by push_cast; ring
  let A := 2000 * (energyConstant + 1)
  have r : Input.reserve D b d (probes ℓ D) m H ≤ A * D ^ 2 * m * H :=
    s.reserve_bound.trans (by gcongr; exact Nat.le_self_pow (by decide) _)
  have hx : Input.initialEnergy D T b d (probes ℓ D) m H ≤
      (A * D ^ 2 * m * H + m * (1280000 * D ^ 2 * H) : ℕ) := by
    rw [Input.initialEnergy, Nat.cast_add, Nat.cast_mul m]
    exact add_le_add (Nat.cast_le.mpr r) (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))
  apply (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)).trans
  rw [← Nat.cast_mul, Nat.cast_le]
  change _ ≤ budget g * D ^ 2 * m * H
  calc
    _ = (A + 1280000) * ((1 + 4 * g) * D ^ 2 * m * H) := by ring
    _ ≤ (10000000 * (energyConstant + 1)) * ((1 + 4 * g) * D ^ 2 * m * H) :=
      Nat.mul_le_mul_right _ (by unfold A; omega)
    _ = _ := by unfold budget; ring

theorem global_bound (N : ℕ) (W : ℝ) (hN : (N : ℝ) * D * T ≤ W) :
    (1 + 4 * g : ℕ) * (N * (Input.reserve D b d (probes ℓ D) m (energy ℓ D (d * b)) : ℝ) +
      m * (8 * W * T / (d * b : ℕ))) ≤ budget g * (m : ℝ) * size ℓ D * W := by
  have hw : 0 ≤ W := le_trans (by positivity) hN
  let A := size ℓ D
  let Q := 2000 * (energyConstant + 1)
  have hr : Input.reserve D b d (probes ℓ D) m (energy ℓ D (d * b)) ≤ Q * D * m * (T * A) :=
    s.reserve_bound.trans (Nat.mul_le_mul_left _ s.smallH)
  have hx : N * (Input.reserve D b d (probes ℓ D) m (energy ℓ D (d * b)) : ℝ) ≤ (Q : ℝ) * m * A * W := calc
    _ ≤ (N : ℝ) * (Q * D * m * (T * A) : ℕ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr) (Nat.cast_nonneg _)
    _ = (Q : ℝ) * m * A * (N * D * T) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)
  have ht : 8 * W * T / (d * b : ℕ) ≤ 16 * W * A := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr s.Rpos)).mpr
    calc
      _ ≤ 8 * W * (2 * (d * b * A) : ℕ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr s.upper) (by positivity)
      _ = _ := by push_cast; ring
  apply (mul_le_mul_of_nonneg_left (add_le_add hx (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg m)))
    (Nat.cast_nonneg _)).trans
  have h : (1 + 4 * g) * (Q + 16) ≤ budget g := by
    rw [budget, mul_comm 10000000, mul_assoc]
    exact Nat.mul_le_mul_left (1 + 4 * g) (constants energyConstant).2
  calc
    _ = ((1 + 4 * g) * (Q + 16) : ℕ) * ((m : ℝ) * A * W) := by push_cast; ring
    _ ≤ (budget g : ℝ) * ((m : ℝ) * A * W) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (by positivity)
    _ = _ := by unfold A; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale.Scales
end

section
/-! # Polynomial bounds for cell slots and ordinary key counts -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale

open Sphere.Layout.Sharing
variable {g ℓ D T m b d : ℕ} (s : Scales g ℓ D T m b d)
include s

theorem Scales.budget_le : budget g ≤ D := by have := s.large; omega

theorem Scales.hits_le : budget g * D ^ 2 ≤ D ^ 3 := calc
  _ ≤ D * D ^ 2 := Nat.mul_le_mul_right _ s.budget_le
  _ = _ := by ring

theorem Scales.room_le : room ℓ D g ≤ D ^ allocation g ℓ := by
  let a := size ℓ D
  have ha : 1 ≤ a := s.apos
  have hD := s.bound
  have hl : 100 * D + 2 * g + 1 ≤ 200 * D := by have := s.degree; omega
  have hD' : 1800 * D ≤ D ^ 2 := by nlinarith
  calc
    _ = (100 * D + 2 * g + 1) + 1600 * D * a + budget g * D ^ 2 := by unfold room slots probes a; ring
    _ ≤ 200 * D * a + 1600 * D * a + D ^ 3 * a := Nat.add_le_add
      (Nat.add_le_add_right (hl.trans (Nat.le_mul_of_pos_right _ ha)) _)
      (s.hits_le.trans (Nat.le_mul_of_pos_right _ ha))
    _ = (1800 * D + D ^ 3) * a := by ring
    _ ≤ D ^ 4 * a := by
      apply Nat.mul_le_mul_right
      have h₂ := hD'.trans (Nat.pow_le_pow_right s.Dpos (by decide : 2 ≤ 3))
      have h₃ := Nat.mul_le_mul_right (D ^ 3) (by omega : 2 ≤ D)
      rw [show D * D ^ 3 = D ^ 4 by ring] at h₃
      omega
    _ = D ^ (4 + (ℓ + 32) * 8) := by unfold a size q; rw [pow_add D 4, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right s.Dpos (by unfold allocation; omega)

theorem Scales.chunks_le : chunks ℓ D ≤ D ^ allocation g ℓ := by
  unfold chunks q
  rw [← pow_mul]
  exact Nat.pow_le_pow_right s.Dpos (by unfold allocation; omega)

theorem Scales.footprint_le :
    budget g * D ^ 2 * Sphere.Surface.Stage.loadLimit (D ^ 5) (budget g * D ^ 2) + 1 ≤ D ^ 14 := by
  have hd := s.bound
  have h₁ := Nat.le_self_pow (by decide : 5 ≠ 0) D
  have h₂ := Nat.le_self_pow (by decide : 3 ≠ 0) D
  have h₃ := Nat.le_self_pow (by decide : 8 ≠ 0) D
  have hp := s.hits_le
  unfold Sphere.Surface.Stage.loadLimit
  calc
    _ ≤ D ^ 3 * ((2 * D ^ 5) * (2 * D ^ 3) + 1) + 1 := by gcongr <;> omega
    _ = 4 * D ^ 11 + D ^ 3 + 1 := by ring
    _ ≤ 6 * D ^ 11 := by have := Nat.pow_le_pow_right s.Dpos (by decide : 3 ≤ 11); omega
    _ ≤ D ^ 3 * D ^ 11 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-! # Energy, space, and visitation bounds throughout a motion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open SphereScale (Scales size budget probes room depth)
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g ℓ m U : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)
  [Field F] [Field K] [Algebra K F] (p : P.Kits K m (probes ℓ D) ε)
  (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "H" => SphereScale.energy ℓ D (d * b)
local notation "N" => depth ℓ D g m (d * b)

variable (sc : Scales g ℓ D T m b d)
  {z : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam (P.Parameters p)}
  (reach : (P.plant p s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) U z)

include sc

private theorem initial_local (c : P.Occupied) :
    let a := (P.plant p s).ledger m H
    (1 + 2 * (2 * g)) * (a.mobile c + a.collected c + ∑ e ∈ (P.plant p s).edges c, a.seam e) ≤ N := by
  rw [show 2 * (2 * g) = 4 * g by omega]
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_left (P.plant_local_energy p s sc.Rpos H c)
    (Nat.cast_nonneg _)).trans sc.initial_bound

private theorem initial_seam_bound (c : P.Occupied) :
    (∑ e ∈ (P.plant p s).edges c, ((P.plant p s).ledger m H).seam e) ≤ N :=
  (Nat.le_add_left _ _).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans
    (P.initial_local p s sc c))

include reach

theorem moved_room : z.Room (room ℓ D g) N := by
  refine P.plant_room p s sc.Rpos sc.pos sc.Hpos _ _ ?_ sc.initial_bound reach
  let e := initialEnergy D T b d (probes ℓ D) m H
  have h₀ : 0 ≤ e := by unfold e initialEnergy; positivity
  have he : e ≤ (N : ℝ) := (le_mul_of_one_le_left h₀ (by norm_cast; omega)).trans sc.initial_bound
  have h₁ : 2 * m * H * (100 * D + probes ℓ D + 1 + 2 * g) + N ≤ 2 * m * H * room ℓ D g := by
    conv_rhs => rw [room, SphereScale.slots, mul_add]
    rw [show 100 * D + 2 * g + probes ℓ D + 1 = 100 * D + probes ℓ D + 1 + 2 * g by omega]
    apply Nat.add_le_add_left
    change budget g * D ^ 2 * m * H ≤ _
    rw [show 2 * m * H * (budget g * D ^ 2) = 2 * (budget g * D ^ 2 * m * H) by ring]
    omega
  exact (add_le_add_right he _).trans (by exact_mod_cast h₁)

theorem moved_visits (c : P.Occupied) : z.visits c ≤ budget g * D ^ 2 := by
  have ht := (reach.budget.limits (fun _ => rfl) (P.plant_zero p s H) rfl).2.2.1 c
  have hb := ht.trans (P.initial_seam_bound p s sc c)
  have hv : 2 * m * H * z.visits c ≤ N := by
    unfold Stage.visits
    rw [reach.edges_eq]
    exact hb
  have pos : 0 < m * H := Nat.mul_pos sc.pos sc.Hpos
  apply Nat.le_of_mul_le_mul_left _ pos
  exact ((Nat.mul_le_mul_right _ (show m * H ≤ 2 * m * H by rw [mul_assoc]; omega)).trans hv).trans_eq
    (by unfold depth; ring)

theorem moved_seam (e : P.grid.Seam) : z.scene.level e ≤ budget g * D ^ 2 * H := by
  let c := e.val.1
  have he : e ∈ (P.plant p s).edges c := by
    rw [P.plant_edges]
    simp [Grid.ports, c]
  have hi : ((P.plant p s).ledger m H).seam e ≤ N :=
    (single_le_sum (fun _ _ => Nat.zero_le _) he).trans (P.initial_seam_bound p s sc c)
  have ht := reach.budget.edge e
  change m * z.scene.level e + _ ≤ ((P.plant p s).ledger m H).seam e + 2 * m * H * 0 at ht
  rw [mul_zero, add_zero] at ht
  apply Nat.le_of_mul_le_mul_left _ sc.pos
  exact ((Nat.le_add_right _ _).trans (ht.trans hi)).trans_eq (by unfold depth; ring)

omit reach sc in
private theorem item_sum (v : P.Occupied) :
    (∑ i : Fin (z.scene.cell v).stations.length, energyOf m (Layout.item z.scene.cell ⟨v, i⟩)) ≤
      (z.ledger m H).mobile v + (z.ledger m H).collected v := by
  refine le_trans ?_ (z.energy_le m H v)
  dsimp only [Layout.item, energyOf]
  rw [sum_add_distrib, ← mul_sum]
  have he (f : z.St → ℕ) : ∑ i, f ((z.scene.cell v).stations.get i) =
      ((z.scene.cell v).stations.map f).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn (f ∘ (z.scene.cell v).stations.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [he Station.a, he Station.b]
  exact le_rfl

theorem moved_energy (i : Layout.Place z.scene.cell) :
    energyOf m (Layout.item z.scene.cell i) ≤ N := by
  rcases i with ⟨v, i⟩
  have ht := (reach.budget.limits (fun _ => rfl) (P.plant_zero p s H) rfl).2.1 v
  exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
    ((P.item_sum p (z := z) v).trans (ht.trans (P.initial_local p s sc v)))

theorem moved_total (frozen : Layout.Place z.scene.cell → Prop) :
    (∑ i : {i // frozen i}, (energyOf m (Layout.item z.scene.cell i.val) : ℝ)) ≤
      budget g * (m : ℝ) * size ℓ D * W := by
  let f (i : Layout.Place z.scene.cell) := energyOf m (Layout.item z.scene.cell i)
  have ht := (reach.budget.limits (fun _ => rfl) (P.plant_zero p s H) rfl).1
  have hs : (∑ i : {i // frozen i}, f i.val) ≤ ∑ i, f i := by
    rw [← sum_subtype (univ.filter frozen) (fun _ => mem_filter_univ _) f]
    exact sum_le_sum_of_subset (subset_univ _)
  rw [Fintype.sum_sigma] at hs
  have h₁ := (hs.trans (sum_le_sum fun c _ => P.item_sum p (z := z) c)).trans ht
  have hc : (Fintype.card P.Occupied : ℝ) * D * T ≤ W := by
    rw [show Fintype.card P.Occupied = (univ.image P.place).card from Fintype.card_coe _]
    exact P.occupied
  rw [← Nat.cast_sum]
  apply ((Nat.cast_le (α := ℝ)).mpr h₁).trans
  rw [Nat.cast_mul, show 2 * (2 * g) = 4 * g by omega]
  exact (mul_le_mul_of_nonneg_left (P.plant_global_energy p s sc.Rpos H) (Nat.cast_nonneg _)).trans
    (sc.global_bound _ _ hc)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Expansion of one terminal surface into padded bit diagrams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)

abbrev Tools (K : Type) [Field K] [Algebra K F] (ℓ m : ℕ) :=
  P.Kits K m (SphereScale.probes ℓ D) (SphereScale.rate ℓ D)

abbrev Configuration (p : P.Tools K ℓ m) :=
  Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam ((Val x × Val y) × Template.Keys p)

def termsBound (ℓ m : ℕ) :=
  (SphereScale.depth ℓ D g m (d * b) + 1) ^
    (SphereScale.chunks ℓ D * (Fintype.card P.grid.Seam + 2 * SphereScale.room ℓ D g *
      Fintype.card P.Occupied))

def Emitted (p : P.Tools K ℓ m) (z : P.Configuration p) (u C a : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (Q : I → LocalTerm F x y h u) (c : I → F),
    Fintype.card I ≤ P.termsBound ℓ m ∧
    (∀ x y, ∑ i, c i * (Q i).diagram.eval x y = ∑ j, z.value m ((x, y), j)) ∧
    ∀ i, Concentrated P (Q i) C a ℓ

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Exterior bits stay at named collectors

The place of each immobile station is unique, including its index
within the cell. Charging exterior bits to the original station then
preserves the initial maximum and square bounds.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open Sphere.Layout (Place item)
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ H U : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)
  (p : P.Tools K ℓ m) (s : P.Occupied → Shape (SphereScale.probes ℓ D) b d)
  {z : P.Configuration p} (hz : (P.plant p s).Reach m (2 * g) H U z)

include hz in
private theorem name_unique {v : P.diagram.V} (i j : Place z.scene.cell)
    (hi : (item z.scene.cell i).label.name = some v)
    (hj : (item z.scene.cell j).label.name = some v) : i = j := by
  obtain ⟨a, i⟩ := i
  obtain ⟨b, j⟩ := j
  have hab : a = b := (P.reached_name p s hz (List.get_mem _ i) hi).2.symm.trans
    (P.reached_name p s hz (List.get_mem _ j) hj).2
  subst b
  have hn := (hz.names (P.plant_controls p s) a).nodup_iff.mpr (P.plant_nodup p s a)
  have hp := List.pairwise_iff_get.mp (List.pairwise_filterMap.mp hn)
  rcases lt_trichotomy i j with he | rfl | he
  · exact (hp i j he _ hi _ hj rfl).elim
  · rfl
  · exact (hp j i he _ hj _ hi rfl).elim

include hz in
private theorem exists_named (q : slots x ⊕ slots y) :
    ∃ i : Place z.scene.cell, (item z.scene.cell i).label.name = some (Packing.portEnd P.diagram q) := by
  obtain ⟨⟨c, a⟩, ⟨hm, he⟩, _⟩ := P.reached_unique p s hz _ (P.ext q)
  change a ∈ (z.scene.cell c).stations at hm
  obtain ⟨j, rfl⟩ := List.get_of_mem hm
  exact ⟨⟨c, j⟩, he⟩

def draw (q : slots x ⊕ slots y) : Place z.scene.cell := (P.exists_named p s hz q).choose

theorem draw_name (q : slots x ⊕ slots y) :
    (item z.scene.cell (P.draw p s hz q)).label.name = some (Packing.portEnd P.diagram q) :=
  (P.exists_named p s hz q).choose_spec

theorem draw_eq (q : slots x ⊕ slots y) (i : Place z.scene.cell)
    (hi : (item z.scene.cell i).label.name = some (Packing.portEnd P.diagram q)) :
    P.draw p s hz q = i :=
  P.name_unique p s hz _ _ (P.draw_name p s hz q) hi

theorem draw_collector (q : slots x ⊕ slots y) :
    (item z.scene.cell (P.draw p s hz q)).label.role = .collector :=
  (hz.controls (P.plant_controls p s) _ _ (List.get_mem ..)).named
    (fun h => by have := (P.draw_name p s hz q).symm.trans h; cases this)

def drawLoad (i : Place z.scene.cell) :=
  Fintype.card {j // P.draw p s hz (.inl j) = i} + Fintype.card {j // P.draw p s hz (.inr j) = i}

private theorem draw_load (i : Place z.scene.cell) : (P.drawLoad p s hz i : ℝ) ≤
    ((item z.scene.cell i).label.name.elim 0 P.diagram.arity : ℕ) := by
  have he q : P.draw p s hz q = i ↔ (item z.scene.cell i).label.name = some (Packing.portEnd P.diagram q) :=
    ⟨fun h => h ▸ P.draw_name p s hz q, P.draw_eq p s hz q i⟩
  cases hn : (item z.scene.cell i).label.name with
  | none => simp [drawLoad, he, hn]
  | some v =>
    have ho : P.drawLoad p s hz i = Packing.exterior P.diagram id v := by
      simp only [drawLoad, Packing.exterior, Fintype.card_subtype, he, hn, Option.some.injEq,
        Packing.portEnd, Sum.elim_inl, Sum.elim_inr, id_eq, eq_comm (a := v)]
    have hw := Packing.site_arity P.diagram id v
    simp only [Packing.push, id_eq, sum_ite_eq', mem_univ, ite_true] at hw
    simpa [ho] using (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans_eq hw.symm

theorem draw_max (i : Place z.scene.cell) : (P.drawLoad p s hz i : ℝ) ≤ 100 * D * T := by
  refine (P.draw_load p s hz i).trans ?_
  cases hn : (item z.scene.cell i).label.name with
  | none => simp; positivity
  | some v =>
    refine le_trans ?_ (P.mass (P.place v))
    unfold Packing.push
    simpa using single_le_sum (s := univ)
      (f := fun w => if P.place w = P.place v then (P.diagram.arity w : ℝ) else 0)
      (fun _ _ => by positivity) (mem_univ v)

theorem draw_squares :
    (∑ i : Place z.scene.cell, (P.drawLoad p s hz i : ℝ) ^ 2) ≤ W * T := by
  calc
    _ ≤ ∑ i : Place z.scene.cell, ∑ v,
        if (item z.scene.cell i).label.name = some v then (P.diagram.arity v : ℝ) ^ 2 else 0 := by
      refine sum_le_sum fun i _ => ?_
      have hd := pow_le_pow_left₀ (Nat.cast_nonneg _) (P.draw_load p s hz i) 2
      cases hn : (item z.scene.cell i).label.name <;> simpa [hn] using hd
    _ ≤ ∑ v, (P.diagram.arity v : ℝ) ^ 2 := by
      rw [sum_comm]
      refine sum_le_sum fun v _ => ?_
      by_cases he : ∃ i, (item z.scene.cell i).label.name = some v
      · obtain ⟨i, hi⟩ := he
        have hq j : (item z.scene.cell j).label.name = some v ↔ j = i :=
          ⟨fun hj => P.name_unique p s hz j i hj hi, fun h => h ▸ hi⟩
        simp only [hq, sum_ite_eq', mem_univ, ite_true, le_refl]
      · push Not at he
        simp [he]
    _ ≤ _ := P.squares

theorem draw_fixed_squares :
    (∑ i : {i : Place z.scene.cell // (item z.scene.cell i).label.role = .collector},
      (P.drawLoad p s hz i.val : ℝ) ^ 2) ≤ W * T := by
  refine le_trans ?_ (P.draw_squares p s hz)
  rw [← sum_subtype (univ.filter fun i => (item z.scene.cell i).label.role = .collector)
    (by simp) (fun i => (P.drawLoad p s hz i : ℝ) ^ 2)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Unchunked motion bounds for a terminal stage -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Sphere Finset Surface
open Sphere.Layout (Place item Alphabet)
open SphereScale (budget room depth size probes q)
open scoped Classical

variable {F T X : Type} [Field F] {x y : Wire} {h D u b d g r t : ℕ} {W : ℝ}
  (P : Input F x y h D u (d * b) g W) {Y : Alphabet P.Occupied}
  {z : Stage F r t T P.Occupied P.grid.Seam X} (A : Layout.Key.Source Y x y z)

def fixed (i : Place z.scene.cell) := (item z.scene.cell i).label.role = .collector

def exterior (i : Place z.scene.cell) :=
  Fintype.card {j // A.left j = i} + Fintype.card {j // A.right j = i}

/-- Numerical inputs before reindexing public and private species by
chunks. All dimensions are energies or counts on the original cells. -/
structure FinalBounds (ℓ m : ℕ) : Prop where
  near : ∀ e, let v := (A.src e).val; let w := (A.dst e).val
    w.2 = v.2 ∧ (w.1 = v.1 ∨ w.1 ∈ P.adj v.1)
  left : ∀ i, P.fixed (A.left i)
  right : ∀ i, P.fixed (A.right i)
  positions : ∀ v, (z.scene.cell v).stations.length ≤ room ℓ D g
  seams : ∀ v, Packing.degree (fun e => (A.src e, A.dst e)) v ≤ budget g
  seamEnergy : ∀ i, z.scene.level i ≤ budget g * D ^ 2 * SphereScale.energy ℓ D (d * b)
  energy : ∀ i, energyOf m (item z.scene.cell i) ≤ depth ℓ D g m (d * b)
  collected : (∑ i : {i : Place z.scene.cell // P.fixed i}, (energyOf m (item z.scene.cell i.val) : ℝ)) ≤
    budget g * (m : ℝ) * size ℓ D * W
  collectors : (Fintype.card {i : Place z.scene.cell // P.fixed i} : ℝ) * D * u ≤ budget g * W
  extMax : ∀ i, P.fixed i → P.exterior A i ≤ budget g * D * u
  extSquare : (∑ i : {i : Place z.scene.cell // P.fixed i}, (P.exterior A i.val : ℝ) ^ 2) ≤
    budget g * W * u
  light : ∀ v, Fintype.card {i : Fin (z.scene.cell v).stations.length //
    thinStation (item z.scene.cell ⟨v, i⟩)} ≤ probes ℓ D
  heavy : ∀ v, Fintype.card {i : Fin (z.scene.cell v).stations.length //
    ¬thinStation (item z.scene.cell ⟨v, i⟩)} ≤ D ^ 5
  aux : ∀ i, thinStation (item z.scene.cell i) →
    (item z.scene.cell i).a ≤ d * b ∧ (item z.scene.cell i).b ≤ d * (Routing.Private.energyConstant * b ^ 2)
  residue : ∀ i, ¬thinStation (item z.scene.cell i) → ¬P.fixed i → (item z.scene.cell i).a = 0
  keys : ∀ v, (z.footprint v).card ≤ D ^ 14
  hidden : ∀ j ∈ z.hidden, j ≤ depth ℓ D g m (d * b)
  selector : ∀ i, (Y.width i : ℝ) ≤ d * b / (q ℓ D : ℝ)

def terminalExponent (g ℓ : ℕ) :=
  Layout.Fanout.exponent (Layout.Sharing.radius (Layout.Sharing.allocation g ℓ)) ℓ

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Numerical bounds after the movers have stopped -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Surface
open SphereScale (q budget room depth probes)
open scoped Classical
variable {F K : Type} {x y : Wire} {h D T b d g m ℓ : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W)

private theorem seam_degree (hr : 0 < d * b) (v : P.Occupied) :
    Packing.degree (fun e : P.grid.Seam => e.val) v ≤ budget g := by
  have side (f : P.grid.Seam → P.Occupied)
      (hf : ∀ e, f e = e.val.1 ∨ f e = e.val.2) : Fintype.card {e // f e = v} ≤ 2 * g := by
    refine le_trans ?_ (P.ports_bound hr v)
    rw [Fintype.card_subtype]
    apply card_le_card
    intro e he
    have hv := (mem_filter.mp he).2
    simp only [Grid.ports, mem_filter_univ]
    rcases hf e with h|h
    · exact .inl (h.symm.trans hv)
    · exact .inr (h.symm.trans hv)
  have h₁ := side (fun e => e.val.1) (fun _ => .inl rfl)
  have h₂ := side (fun e => e.val.2) (fun _ => .inr rfl)
  have hh : 10000000 * (1 + 4 * g) ≤ budget g := Nat.le_mul_of_pos_right _ (by omega)
  simp only [Packing.degree, ← Nat.card_eq_fintype_card] at h₁ h₂ ⊢
  omega

variable [Field F] [Field K] [Algebra K F] (p : P.Tools K ℓ m)
  (s : P.Occupied → Routing.Private.Shape (probes ℓ D) b d)
  (sc : SphereScale.Scales g ℓ D T m b d) {z : P.Configuration p}
  (hz : (P.plant p s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) (D ^ 5) z)

include sc hz in
theorem reached_bounds (hs : z.Stopped) {Y : Layout.Alphabet P.Occupied}
    (A : Layout.Key.Source Y x y z) (hsrc : ∀ e, A.src e = e.val.1) (hdst : ∀ e, A.dst e = e.val.2)
    (hl : ∀ i, P.fixed (A.left i)) (hr : ∀ i, P.fixed (A.right i))
    (hm : ∀ i, P.fixed i → P.exterior A i ≤ budget g * D * T)
    (he : (∑ i : {i : Layout.Place z.scene.cell // P.fixed i}, (P.exterior A i.val : ℝ) ^ 2) ≤
      budget g * W * T)
    (hy : ∀ i, (Y.width i : ℝ) ≤ d * b / (q ℓ D : ℝ)) :
    P.FinalBounds A ℓ m := by
  have hv := P.moved_visits p s sc hz
  obtain ⟨hlight, hheavy, haux, hres⟩ := P.plant_final p s sc hz hs hv
  refine ⟨?_, hl, hr, ?_, ?_, P.moved_seam p s sc hz, P.moved_energy p s sc hz,
    P.moved_total p s sc hz _, ?_, hm, he, hlight, hheavy, haux, hres, ?_, ?_, hy⟩
  · intro e
    obtain ⟨i, hi, hj⟩ := e.property.2
    rw [hsrc, hdst, ← hi, ← hj]
    exact P.contact sc.Rpos i
  · intro v
    have h := (P.moved_room p s sc hz v).1
    simp only [Cell.positions, List.length_append, List.length_map] at h
    exact (Nat.le_add_right _ _).trans h
  · simp only [hsrc, hdst, Prod.mk.eta]
    exact P.seam_degree sc.Rpos
  · have h : Fintype.card {i : Layout.Place z.scene.cell // P.fixed i} = z.collectors := by
      refine Eq.trans ?_ (Stage.card_collectors z)
      exact Fintype.card_congr (Equiv.refl _)
    rw [h]
    exact P.final_count p s sc hz hv
  · intro v
    refine (hz.footprint_bound (Stage.init_load (P.plant_controls p s) (fun _ => rfl))
      (fun _ reach => P.moved_visits p s sc reach) v).trans sc.footprint_le
  · apply Stage.Reach.hidden_le hz (by simp [plant])
    intro z hz v a ha
    obtain ⟨i, rfl⟩ := List.get_of_mem ha
    exact (Nat.le_add_left _ _).trans (P.moved_energy p s sc hz ⟨v, i⟩)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Enough auxiliary marks for every occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)

omit [Field F] in
theorem probe_width (sc : SphereScale.Scales g ℓ D T m b d) (v : P.Occupied) :
    ∑ i, 4 * P.grid.width v i ≤ SphereScale.probes ℓ D := by
  apply Nat.le_of_mul_le_mul_right _ sc.Rpos
  rw [← mul_sum, mul_assoc]
  calc
    _ ≤ 4 * (200 * D * T) := Nat.mul_le_mul_left _ (P.grid_width v)
    _ ≤ 4 * (200 * D * (2 * (d * b * SphereScale.size ℓ D))) := by gcongr; exact sc.upper
    _ = _ := by unfold SphereScale.probes; ring

theorem tools_exist (sc : SphereScale.Scales g ℓ D T m b d)
    (hK : SphereScale.Ready K ℓ D g m b d) : Nonempty (P.Tools K ℓ m) := by
  refine ⟨fun v => Classical.choice ?_⟩
  exact hK F _ _ _ inferInstance inferInstance (P.grid.template K P.weight v)
    (P.probe_width sc v) (P.stations_bound v) (P.ports_bound sc.Rpos v)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Binary width of the original private selectors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere SphereScale

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) (p : P.Tools K ℓ m)

abbrev selectors : Layout.Alphabet P.Occupied where
  state i := Fin (p i).program.labels
  width i := Nat.clog 2 (p i).program.labels
  code i := Layout.binaryCode (Fin (p i).program.labels) _ (by
    rw [Fintype.card_fin]
    exact Nat.le_pow_clog (by decide) _)

/-- The species ratio makes the target width integral. -/
theorem selector_le (hc : Scales g ℓ D T m b d) (i : P.Occupied) :
    ((P.selectors p).width i : ℝ) ≤ d * b / (q ℓ D : ℝ) := by
  let n := d * m * q ℓ D ^ 3
  have hn : d * b = n * q ℓ D := by unfold n; rw [hc.block]; ring
  have hq : (0 : ℝ) < q ℓ D := Nat.cast_pos.mpr hc.qpos
  have hd : (d : ℝ) * b = n * (q ℓ D : ℝ) := by exact_mod_cast hn
  have hr : rate ℓ D * d * b = (n : ℝ) / 4 := by
    unfold rate
    rw [mul_assoc, hd]
    field_simp
  have hlog : (1 / 4 : ℝ) ≤ Real.log 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
    rw [Real.log_inv] at ht
    linarith
  have bound : ((p i).program.labels : ℝ) ≤ (2 : ℝ) ^ n := calc
    _ ≤ Real.exp (rate ℓ D * d * b) := (p i).small
    _ ≤ Real.exp ((n : ℝ) * Real.log 2) := by
      rw [hr, div_eq_mul_one_div]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hd, mul_div_cancel_right₀ _ hq.ne']
  exact Nat.cast_le.mpr (Nat.clog_le_of_le_pow (by exact_mod_cast bound))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Realizing the ordinary inputs of a reachable stage -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface SphereScale Routing.Private
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ H U : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) (p : P.Tools K ℓ m)
  (s : P.Occupied → Shape (probes ℓ D) b d)
  {z : P.Configuration p} (hz : (P.plant p s).Reach m (2 * g) H U z)

/-- The original port names still determine all exterior bits. Other
information enters only through connected footprints. -/
def shared (hR : 0 < d * b) :
    Layout.Key.Source (P.selectors p) x y z where
  src e := e.val.1
  dst e := e.val.2
  meets v j hj := by
    apply ((P.plant_layout p s hR).incident v j.1).mp
    rw [← hz.ports_eq]
    exact List.mem_map_of_mem hj
  tracks := hz.tracks (P.plant_layout p s hR) (P.plant_controls p s) tracks_init
  left i := P.draw p s hz (.inl i)
  right i := P.draw p s hz (.inr i)
  init a b c := ((a, b), c)
  keys := P.keyEq p
  ext := P.extEq p
  controls := hz.controls (P.plant_controls p s)
  original := fun _ _ _ _ _ _ _ h => h
  exterior i j he _ _ _ _ _ _ hl hr k hk := by
    have hh := P.draw_eq p s hz k i (he.trans (congrArg some hk.symm))
    cases k with
    | inl k => exact hl k hh
    | inr k => exact hr k hh

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Combining the three finite expansions

The ordinary selector remains summed inside every surface term. The
outer choices are energy profiles, movement branches and level splits
in the final diagrams. Bounds grow exponentially only in the number
of occupied cells.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Finset Sphere Surface Routing.Private SphereScale
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g m ℓ u C a : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W)

private theorem seams_bound (hr : 0 < d * b) :
    Fintype.card P.grid.Seam ≤ 2 * g * Fintype.card P.Occupied := by
  let f (e : P.grid.Seam) : Σ v, ↥(P.grid.ports v) :=
    ⟨e.val.1, e, by simp [Grid.ports]⟩
  have inj : Function.Injective f := fun i j h => congrArg (fun x : Σ v, ↥(P.grid.ports v) => x.2.val) h
  refine (Fintype.card_le_of_injective f inj).trans ?_
  rw [Fintype.card_sigma]
  simpa [mul_comm] using sum_le_sum (s := univ) (fun i _ => P.ports_bound hr i)

private theorem terminal_bound (hr : 0 < d * b) :
    P.termsBound ℓ m ≤ finalChoices g ℓ D m b d ^ Fintype.card P.Occupied := by
  unfold termsBound finalChoices
  rw [← pow_mul, mul_assoc (chunks ℓ D) _ (Fintype.card P.Occupied), add_mul]
  exact Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (P.seams_bound hr) _))

variable [Field F] [Field K] [Algebra K F] (kit : P.Tools K ℓ m)

private theorem potential_bound (s : P.Occupied → Shape (probes ℓ D) b d) :
    (P.plant kit s).potential (D ^ 5) ≤ ((2 + 2 * D ^ 5) * (100 * D + probes ℓ D + 1)) * Fintype.card P.Occupied := by
  refine ((P.plant kit s).potential_le _).trans ?_
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  simpa [mul_comm] using sum_le_sum (s := univ) (fun i _ => P.plant_length kit s i)

def SumOf (good : LocalTerm F x y h u → Prop) (n : ℕ) (f : Val x → Val y → F) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (Q : I → LocalTerm F x y h u) (c : I → F),
    Fintype.card I ≤ n ∧ (∀ x y, ∑ i, c i * (Q i).diagram.eval x y = f x y) ∧
      ∀ i, good (Q i)

variable {good : LocalTerm F x y h u → Prop}

private theorem SumOf.mono {n n' : ℕ} {f} (hs : SumOf good n f) (hn : n ≤ n') :
    SumOf good n' f := by
  obtain ⟨I, fi, Q, c, hc, he, hq⟩ := hs
  exact ⟨I, fi, Q, c, hc.trans hn, he, hq⟩

private theorem combine {I : Type} [Fintype I] {n : ℕ} (k : I → F)
    (f : I → Val x → Val y → F) (hs : ∀ i, SumOf good n (f i)) :
    SumOf good (Fintype.card I * n) (fun x y => ∑ i, k i * f i x y) := by
  unfold SumOf at hs ⊢
  choose J fj Q c hc he hq using hs
  let _ := fj
  refine ⟨Σ i, J i, inferInstance, fun i => Q i.1 i.2, fun i => k i.1 * c i.1 i.2,
    ?_, fun x y => ?_, fun i => hq _ _⟩
  · rw [Fintype.card_sigma]
    simpa using sum_le_sum (s := univ) (fun i _ => hc i)
  · simp only [Fintype.sum_sigma, mul_assoc, ← mul_sum, he]

def ordinary (z : P.Configuration kit) (v : Val x) (w : Val y) := ∑ i, z.value m ((v, w), i)

variable (sc : Scales g ℓ D T m b d)
variable (terminal : ∀ s (z : P.Configuration kit), (P.plant kit s).Reach m (2 * g)
    (SphereScale.energy ℓ D (d * b)) (D ^ 5) z → z.Valid (D ^ 5) → z.Stopped → Input.SumOf good (P.termsBound ℓ m) (P.ordinary kit z))

include sc terminal in
private theorem emit_stage (s : P.Occupied → Shape (probes ℓ D) b d)
    (hs : Stage.Terms m (fun z => (P.plant kit s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) (D ^ 5) z ∧
      z.Valid (D ^ 5) ∧ z.Stopped) (branches m (2 * g) (SphereScale.energy ℓ D (d * b)) (room ℓ D g)
        (depth ℓ D g m (d * b)) ^ (P.plant kit s).potential (D ^ 5)) ((P.plant kit s).value m)) :
    SumOf good ((moveChoices g ℓ D m b d * finalChoices g ℓ D m b d) ^ Fintype.card P.Occupied)
      (P.ordinary kit (P.plant kit s)) := by
  obtain ⟨I, fi, k, z, hc, hz, he⟩ := hs
  have hc' : Fintype.card I ≤ moveChoices g ℓ D m b d ^ Fintype.card P.Occupied := by
    rw [moveChoices, ← pow_mul]
    exact hc.trans (Nat.pow_le_pow_right (branches_pos _ _ _ _ _) (P.potential_bound kit s))
  have emit (i : I) : SumOf good (P.termsBound ℓ m) (P.ordinary kit (z i)) :=
    terminal s (z i) (hz i).1 (hz i).2.1 (hz i).2.2
  have eqn : P.ordinary kit (P.plant kit s) = fun x y => ∑ i, k i * P.ordinary kit (z i) x y := by
    funext v w
    simp only [ordinary, he, mul_sum]
    rw [sum_comm]
  rw [eqn, mul_pow]
  exact (combine k _ emit).mono (Nat.mul_le_mul hc' (P.terminal_bound sc.Rpos))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale

open Finset Sphere.Surface Routing.Private
open scoped Classical

/-- Select the field threshold and bit-count constant before the
input width, working field and family of diagrams are specified. -/
theorem stack_with (g ℓ D m b : ℕ) :
    ∃ A : ℕ, ∀ {T d} (_ : Scales g ℓ D T m b d) (F K : Type) [Field F] [Fintype F]
      [Field K] [Algebra K F] (p l : ℕ) [ExpChar F p], m = p ^ l →
      A * (1 + T) ^ A ≤ Fintype.card F →
      ∀ {x y h W} (P : Input F x y h D T (d * b) g W) (kit : P.Tools K ℓ m) (u : ℕ) (good : LocalTerm F x y h u → Prop),
      (∀ s (z : P.Configuration kit), (P.plant kit s).Reach m (2 * g) (energy ℓ D (d * b)) (D ^ 5) z →
        z.Valid (D ^ 5) → z.Stopped → Input.SumOf good (P.termsBound ℓ m) (P.ordinary kit z)) →
      Input.SumOf good (2 ^ (A * (1 + Nat.clog 2 (T + 1)) * (univ.image P.place).card)) P.diagram.eval := by
  obtain ⟨A, hA⟩ := choice_bound g ℓ D m b
  refine ⟨A, ?_⟩
  intro T d sc F K _ _ _ _ p l _ hm hF x y h W P kit u good terminal
  subst m
  obtain ⟨hroom, hindex⟩ := hA sc
  let I := P.Occupied → Shape (probes ℓ D) b d
  let n := (moveChoices g ℓ D (p ^ l) b d * finalChoices g ℓ D (p ^ l) b d) ^ Fintype.card P.Occupied
  have terms (s : I) : Input.SumOf good n (P.ordinary kit (P.plant kit s)) := by
    apply P.emit_stage kit sc terminal s
    exact (P.plant kit s).complete p l (P.plant_layout kit s sc.Rpos)
      (P.plant_valid kit s _) (fun _ reach => P.moved_room kit s sc reach) (hroom.trans_le hF)
  have total := Input.combine (fun _ : I => 1) _ terms
  simp only [one_mul] at total
  have eqn : (fun v w => ∑ s : I, P.ordinary kit (P.plant kit s) v w) = P.diagram.eval :=
    funext fun v => funext fun w => P.eval_plant kit v w
  rw [eqn] at total
  apply total.mono
  have hI : Fintype.card I = initialChoices ℓ D b d ^ Fintype.card P.Occupied := by
    unfold I
    rw [Fintype.card_fun, card_shape]
    rfl
  unfold n
  rw [hI, ← mul_pow, ← mul_assoc, pow_mul, ← Fintype.card_coe (univ.image P.place)]
  exact Nat.pow_le_pow_left hindex _

theorem stack (g ℓ D m b : ℕ) :
    ∃ A : ℕ, ∀ {T d} (_ : Scales g ℓ D T m b d) (F K : Type) [Field F] [Fintype F]
      [Field K] [Algebra K F] (p l : ℕ) [ExpChar F p], m = p ^ l →
      A * (1 + T) ^ A ≤ Fintype.card F →
      ∀ {x y h W} (P : Input F x y h D T (d * b) g W) (kit : P.Tools K ℓ m) (u C a : ℕ),
      (∀ s (z : P.Configuration kit), (P.plant kit s).Reach m (2 * g) (energy ℓ D (d * b)) (D ^ 5) z →
        z.Valid (D ^ 5) → z.Stopped → P.Emitted kit z u C a) →
      LocalExpansion P u C a ℓ A := by
  obtain ⟨A, hA⟩ := stack_with g ℓ D m b
  refine ⟨A, ?_⟩
  intro T d sc F K _ _ _ _ p l _ hm hF x y h W P kit u C a terminal
  exact hA sc F K p l hm hF P kit u (fun Q => Concentrated P Q C a ℓ) terminal

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end
