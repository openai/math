import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Remnants
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Install
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Owners
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic

section
/-! # Polynomial cardinality estimates for local data -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
def Poly (f : ℕ → ℕ) := ∃ k : ℕ, ∀ d, f d ≤ (d + 2) ^ k

theorem Poly.const (a : ℕ) : Poly (fun _ => a) :=
  ⟨a, fun _ => Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) a)⟩

theorem Poly.var : Poly (fun d => d) := ⟨1, by simp⟩

theorem Poly.add {f g : ℕ → ℕ} (a : Poly f) (b : Poly g) : Poly (fun d => f d + g d) := by
  obtain ⟨i, hi⟩ := a
  obtain ⟨j, hj⟩ := b
  refine ⟨max i j + 1, fun d => ?_⟩
  have hf := (hi d).trans (Nat.pow_le_pow_right (by omega) (le_max_left i j))
  have hg := (hj d).trans (Nat.pow_le_pow_right (by omega) (le_max_right i j))
  rw [pow_succ]
  exact (Nat.add_le_add hf hg).trans (by rw [← Nat.mul_two]; gcongr; omega)

theorem Poly.mul {f g : ℕ → ℕ} (a : Poly f) (b : Poly g) : Poly (fun d => f d * g d) := by
  obtain ⟨i, hi⟩ := a
  obtain ⟨j, hj⟩ := b
  exact ⟨i + j, fun d => by rw [pow_add]; exact Nat.mul_le_mul (hi d) (hj d)⟩

theorem Poly.pow {f : ℕ → ℕ} (a : Poly f) (n : ℕ) : Poly (fun d => f d ^ n) := by
  obtain ⟨i, hi⟩ := a
  exact ⟨i * n, fun d => by rw [pow_mul]; exact Nat.pow_le_pow_left (hi d) _⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-! # A designated active insertion and its stationary marks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T V E X : Type} {r t P g H U M N : ℕ}

def width (P g H N K : ℕ) := window P g H N * (N + 1) * K ^ 2

structure Move (s : Stage F r t T V E X) where
  atCell : V
  rest : s.Ct
  mover : s.St
  clock : ℕ
  cell : s.scene.cell atCell = rest.insert mover
  role : mover.label.role = .active clock
  ready : s.Ready atCell rest.stations

namespace Move

variable {s : Stage F r t T V E X} (u : Move s)

theorem distinct (hv : s.Valid U) : u.rest.positions.Nodup ∧ u.mover.pos ∉ u.rest.sites := by
  have h := hv.distinct u.atCell
  rw [u.cell, Cell.positions_insert, List.nodup_cons] at h
  exact ⟨h.2, fun e => h.1 (List.mem_toFinset.mp e)⟩

theorem collector (hv : s.Valid U) : ∃ a ∈ u.rest.stations, a.label.role = .collector := by
  obtain ⟨a, ha, h⟩ := hv.collector u.atCell
  rw [u.cell] at ha
  rcases List.mem_cons.mp ha with rfl|ha
  · simp [u.role] at h
  · exact ⟨a, ha, h⟩

theorem room (hr : s.Room M N) :
    u.rest.sites.card ≤ M ∧ u.mover.a + u.mover.b + u.rest.bigA s.scene.level + sumB u.rest.stations ≤ N := by
  obtain ⟨h, k⟩ := hr u.atCell
  rw [u.cell, Cell.positions_insert, List.length_cons] at h
  refine ⟨u.rest.sizes (by omega), ?_⟩
  rw [u.cell] at k
  simp only [Cell.bigA, Cell.insert, sumA, sumB, List.map_cons, List.sum_cons] at k ⊢
  omega

def threshold (P H : ℕ) := energyOf P u.mover + 2 * P * H

theorem threshold_le (hr : s.Room M N) : u.threshold P H ≤ P * N + N + 2 * P * H := by
  have h := (u.room hr).2
  have e := Nat.mul_le_mul_left P (by omega : u.mover.a ≤ N)
  unfold threshold energyOf
  omega

variable [Field F]

def order (P : ℕ) := poleOrder P ((s.scene.cell u.atCell).orderA s.scene.level)
  (s.scene.cell u.atCell).orderB u.rest.inserts

omit [Field F] in
theorem order_le (hr : s.Room M N) (z : F) : u.order P z ≤ P * N + N := by
  obtain ⟨h₁, h₂⟩ := (s.scene.cell u.atCell).order_bounds s.scene.level (hr u.atCell).2
  have h := Nat.mul_le_mul_left P h₁
  unfold order poleOrder
  split_ifs <;> omega

def test (P : ℕ) (z : F) (j : ℤ) : Test F r t := coefficient P (powered P u.rest.sites) u.rest.inserts z j

end Move
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Selecting the destination of an insertion collision -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Function Motion Stage
open scoped Classical
variable {F T V E X : Type} {r t P g H U M N : ℕ} {s : Stage F r t T V E X}

theorem Stage.Room.perm (h : s.Room M N) (v : V) (ls : List s.St) (hl : (s.scene.cell v).stations.Perm ls) :
    (s.put v ⟨(s.scene.cell v).ports, ls⟩).Room M N := by
  intro w
  by_cases hv : w = v
  · subst w
    have hA := (hl.map Station.a).sum_eq
    have hB := (hl.map Station.b).sum_eq
    have hn := hl.length_eq
    simpa only [put, Scene.put, update_self, Cell.positions, List.length_append, List.length_map,
      Cell.bigA, sumA, sumB, hA, hB, hn] using h v
  · simpa only [put, Scene.put, update_of_ne hv] using h w

variable [Field F] [Fintype V] [Fintype E]

theorem Move.absorb (u : Move s) (p l : ℕ) [ExpChar F p]
    (hv : s.Valid U) (hr : s.Room M N) (a : s.St) (ha : a ∈ u.rest.stations) (j : ℤ)
    (hj : j ≤ if a.label.role = .collector then (g * u.threshold (p ^ l) H : ℕ) else 0) :
    Terms (p ^ l) (s.Gain (p ^ l) g H U) (width (p ^ l) g H N (M * (2 * N) + 1))
      (s.observe (p ^ l) u.atCell (u.test (p ^ l) a.pos j)) := by
  let P := p ^ l
  obtain ⟨ls, rs, hc⟩ := List.append_of_mem ha
  let c : s.Ct := ⟨u.rest.ports, ls ++ rs⟩
  let n := s.reord u.atCell (u.mover :: ls) [a] rs
  have hk : (s.scene.cell u.atCell).stations = (u.mover :: ls) ++ [a] ++ rs := by
    simp [u.cell, Cell.insert, hc]
  have perm : (s.scene.cell u.atCell).stations.Perm ([a] ++ (u.mover :: ls) ++ rs) := by
    rw [hk]
    exact List.perm_append_comm.append_right rs
  have hv' : n.Valid U := hv.perm _ _ perm
  have hr' : n.Room M N := hr.perm _ _ perm
  have e : n.scene.cell u.atCell = (c.insert u.mover).insert a := by
    simp [n, reord, put, Scene.put, u.cell, c, Cell.insert]
  have ready : n.Ready u.atCell (a :: c.stations) := by
    constructor
    · intro b hb
      apply u.ready.1
      rw [hc]
      exact List.perm_middle.mem_iff.mpr hb
    · intro w hw b hb
      apply u.ready.2 w hw
      simp only [n, reord, put, Scene.put, update_of_ne hw] at hb
      exact hb
  have he : u.rest.positions.Perm (a.pos :: c.positions) := by
    simp only [Cell.positions, hc, c, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append]
    exact List.perm_middle
  have h₁ : a.pos ∉ c.sites := fun h =>
    (List.nodup_cons.mp (he.nodup_iff.mp (u.distinct hv).1)).1 (List.mem_toFinset.mp h)
  have h₂ : c.sites ⊆ u.rest.sites := fun i hi =>
    List.mem_toFinset.mpr (he.mem_iff.mpr (.tail _ (List.mem_toFinset.mp hi)))
  have h₃ : c.inserts ⊆ u.rest.inserts.erase a.pos := by
    intro z hz
    refine mem_erase.mpr ⟨fun h => h₁ (h ▸ c.inserts_sub hz), ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    apply u.rest.mem_inserts
    rw [hc]
    exact List.perm_middle.mem_iff.mpr (.tail _ hi)
  let A := powered P u.rest.sites
  let B := u.rest.inserts
  have aB : a.pos ∈ B := u.rest.mem_inserts ha
  have old := merge_terms p l rfl hv' u.atCell c a u.mover u.clock e u.role ready A B
    (mem_image_of_mem _ (u.rest.inserts_sub aB)) aB
    ((powered_iff p l _ _).not.mpr (u.distinct hv).2)
    (fun h => (u.distinct hv).2 (u.rest.inserts_sub h))
    (c.fixed_erase p l a.pos h₁ _ _ h₂ h₃) j hj
  refine rotate_terms u.atCell _ (coefficient_signed _ _ _ _ _) _ _ _ hk (old.mono ?_)
  have bound : j ≤ (g * (P * N + N + 2 * P * H) : ℕ) := by
    have ht := Nat.mul_le_mul_left g (u.threshold_le (P := P) (H := H) hr)
    unfold P at *
    split_ifs at hj <;> omega
  obtain ⟨hA, hB⟩ := (n.scene.cell u.atCell).order_bounds n.scene.level (hr' u.atCell).2
  refine (card_filter_le _ _).trans ((pairs_card hA hB bound).trans ?_)
  unfold width
  exact (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by positivity))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Availability and size of a seam crossing -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion Stage
open scoped Classical
variable {F T V E X : Type} [Field F] [Fintype F] [Fintype E] [Fintype V]
  {r t P g H U M N : ℕ} {s : Stage F r t T V E X}

omit [Field F] [Fintype F] in
theorem hop_card (d e m : ℕ) (j : ℤ) (A B : Finset F) (K : ℕ)
    (ha : A.card ≤ K) (hb : B.card ≤ K) (hd : d ≤ N) (hm : m ≤ N) (hj : j ≤ 0) :
    Fintype.card (Hop P d e m j A B) ≤ width P g H N K := by
  have h : (crossings P d e m j).card ≤ window P g H N :=
    (card_filter_le _ _).trans (pairs_card hd (Nat.zero_le _) (hj.trans (Int.natCast_nonneg _)))
  simp only [Hop, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
  calc
    _ ≤ window P g H N * (K * ((N + 1) * K)) :=
      Nat.mul_le_mul h (Nat.mul_le_mul ha (Nat.mul_le_mul (Nat.succ_le_succ hm) hb))
    _ = _ := by unfold width; ring

theorem Move.exit (u : Move s) (p l : ℕ) [ExpChar F p] {src dst : E → V}
    (hl : s.Layout src dst g) (hv : s.Valid U) (hr : s.Room M N) (hc : u.clock < U)
    (hs : M * (2 * N + 1) < Fintype.card F) (i : E) (z : F) (hi : (i, z) ∈ u.rest.ports)
    (j : ℤ) (hj : u.threshold (p ^ l) H ≤ -j) :
    Terms (p ^ l) (s.Gain (p ^ l) g H U) (width (p ^ l) g H N (M * (2 * N) + 1))
      (s.observe (p ^ l) u.atCell (u.test (p ^ l) z j)) := by
  let P := p ^ l
  have hi' : (i, z) ∈ s.ports u.atCell := by unfold ports; rw [u.cell]; exact hi
  obtain ⟨w, y, R, ne, hw, other⟩ := hl.partner hi'
  obtain ⟨L, hL⟩ := Socket.exists_of_mem hi
  let A := u.rest.sites
  let B := u.rest.inserts
  let C := (s.scene.cell w).sites
  have vz : z ∈ u.rest.seams := u.rest.mem_seams hi
  have vy : y ∈ C := by unfold C; rw [hw, Socket.sites]; exact mem_insert_self _ _
  have hz : z ∉ B := disjoint_right.mp (u.rest.disjoint (u.distinct hv).1) vz
  have hA : A.card ≤ M := (u.room hr).1
  have hB : B.card ≤ M := (card_le_card u.rest.inserts_sub).trans hA
  have hC : C.card ≤ M := (s.scene.cell w).sizes (hr w).1
  obtain ⟨U', hu', hcu⟩ := exists_subset_card_eq (Nat.succ_le_of_lt (fresh_size hA hs))
  obtain ⟨W', hw', hcw⟩ := exists_subset_card_eq (Nat.succ_le_of_lt (fresh_size hC hs))
  let V' := powered P W'
  have hcv : V'.card = M * (2 * N) + 1 := (card_image_of_injective _ (power_injective p l)).trans hcw
  have hAf : M * (2 * N) < U'.card := by omega
  have hCf : M * (2 * N) < V'.card := by omega
  have bound₁ : u.mover.a + u.mover.b + (s.scene.level i + L.base.bigA s.scene.level) +
      sumB L.stations ≤ N := by
    have h := (u.room hr).2
    rw [← hL, Socket.bigA] at h
    exact h
  have bound₂ : s.scene.level i + R.base.bigA s.scene.level ≤ N := by
    have h := (hr w).2
    rw [hw, Socket.bigA] at h
    omega
  choose f hf hf' using fun j : V' => mem_image.mp j.property
  let a : Passage P u.mover :=
    { z := z, y := y, A := powered P A, B := B, C := powered P C, U := U', V := V'
      root := f, hroot := hf'
      hz := mem_image_of_mem _ (u.rest.seams_sub vz)
      hy := mem_image_of_mem _ vy
      hb := hz
      hu := (powered_iff p l A _).not.mpr (u.distinct hv).2
      hu' := fun h => (u.distinct hv).2 (u.rest.inserts_sub h)
      hU := disjoint_left.mpr fun k hk e => (mem_sdiff.mp (hu' hk)).2 (u.rest.inserts_sub e)
      hV := disjoint_left.mpr (by
        intro k hk e
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hk
        exact (mem_sdiff.mp (hw' hy)).2 ((powered_iff p l C y).mp e))
      e := s.scene.level i, a := L.base.bigA s.scene.level, b := sumB L.stations
      c := R.base.bigA s.scene.level
      sizeU := (Nat.mul_le_mul hB (by omega)).trans_lt hAf
      sizeV := (Nat.mul_le_mul (card_image_le.trans hC) (by omega)).trans_lt hCf
      H := H, j := j, low := hj }
  have fits : a.Fits L.base R.base s.scene.level := by
    refine ⟨?_, ⟨R.base.inserts, ?_⟩, rfl, rfl, rfl⟩
    · have e : A = insert z L.base.sites := by unfold A; rw [← hL, Socket.sites]
      have hz := L.avoids i z (hL.symm ▸ (u.distinct hv).1)
      exact L.base.fixed_erase p l z hz A B (by rw [e]; exact subset_insert _ _)
        (by unfold B; rw [← hL]; rfl)
    · have e : C = insert y R.base.sites := by unfold C; rw [hw, Socket.sites]
      have hy := R.avoids i y (hw ▸ hv.distinct w)
      exact R.base.fixed_erase p l y hy C R.base.inserts (by rw [e]; exact subset_insert _ _) Subset.rfl
  have vhere : s.scene.cell u.atCell = (L.plug i z).insert u.mover := by rw [hL, u.cell]
  have vl : Unused i L.base.ports := L.unused i z (by
    have h := hl.unique u.atCell; rw [ports, vhere] at h; exact h)
  have vr : Unused i R.base.ports := R.unused i y (by
    have h := hl.unique w; rw [ports, hw] at h; exact h)
  have ready : s.Ready u.atCell L.stations := by
    have h := u.ready; rw [← hL] at h; exact h
  have old := cross_terms (g := g) p l rfl hv u.atCell w i L R u.mover a u.clock
    vhere hw ne rfl rfl u.role hc ready fits vl vr other
    (fun k hk => (mem_sdiff.mp (hu' k.2)).2 (List.mem_toFinset.mpr (hL ▸ hk)))
    (fun k hk => (mem_sdiff.mp (hw' (hf k))).2 (List.mem_toFinset.mpr (hw.symm ▸ hk)))
  apply old.mono
  exact hop_card ((s.scene.level i + u.mover.a + L.base.bigA s.scene.level) / 2)
    (s.scene.level i) u.mover.a j U' V' _ hcu.le hcv.le (by omega) (by omega) (by omega)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # One productive step at any active insertion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion Stage
open scoped Classical
variable {F T V E X : Type} [Field F] [Fintype F] [Fintype E] [Fintype V]
  {r t g H U M N : ℕ} {s : Stage F r t T V E X} {src dst : E → V}

/-- The number of branches in one step is bounded independently of the
actual field cardinality. -/
def branches (P g H M N : ℕ) := breadth P g H M N (M * (2 * N) + 1)

theorem branches_pos (P g H M N : ℕ) : 0 < branches P g H M N := by
  unfold branches breadth window
  positivity

theorem Move.run (u : Move s) (p l : ℕ) [ExpChar F p] (hl : s.Layout src dst g)
    (hv : s.Valid U) (hr : s.Room M N) (hs : M * (2 * N + 1) < Fintype.card F) :
    Terms (p ^ l) (s.Gain (p ^ l) g H U) (branches (p ^ l) g H M N) (s.value (p ^ l)) := by
  let P := p ^ l
  let K := M * (2 * N) + 1
  by_cases old : u.clock = U
  · exact (freeze_terms hv u.atCell u.rest u.mover u.cell (u.role.trans (by rw [old])) u.ready).mono
      (branches_pos _ _ _ _ _)
  have ht : u.clock < U := by
    have he := hv.bound u.atCell u.mover (by rw [u.cell]; exact List.mem_cons_self)
    rw [u.role] at he
    exact lt_of_le_of_ne he old
  obtain ⟨c, hc, hc'⟩ := u.collector hv
  let Z := u.rest.sites
  let B := u.rest.inserts
  let D := u.rest.seams
  have cz : c.pos ∈ Z := u.rest.inserts_sub (u.rest.mem_inserts hc)
  have cd : c.pos ∉ D := disjoint_left.mp (u.rest.disjoint (u.distinct hv).1) (u.rest.mem_inserts hc)
  have hd : D.card ≤ g := by
    have e := hl.degree u.atCell
    rw [ports, u.cell] at e
    exact (List.toFinset_card_le _).trans ((List.length_map _).le.trans e)
  let L := u.threshold P H
  obtain ⟨w, hw⟩ := s.scene.reconstruct p l u.atCell Z B D u.rest.inserts_sub u.rest.seams_sub
    c.pos cz cd g L hd u.mover.pos (u.distinct hv).2 (by
      rw [u.cell]; intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact .inl rfl
      · exact .inr (u.rest.mem_inserts ha)) (by
      rw [u.cell]; exact fun _ h => u.rest.seams_sub (u.rest.mem_seams h))
  let I := Σ y : Z, Fin (orders D c.pos (u.order P) g L y.val)
  let order (i : I) : ℤ := (i.2.val : ℤ) - u.order P i.1.val
  let term (i : I) := s.observe P u.atCell (u.test P i.1.val (order i))
  have eqn : s.value P = fun x => ∑ i : I, w i * term i x := by
    funext x
    unfold value
    rw [funext hw, trace_sum]
    exact sum_congr rfl fun i _ => trace_mul _ _ _ _ _
  have inter (i : I) : Terms P (s.Gain P g H U) (width P g H N K) (term i) := by
    let z := i.1.val
    have hi : i.2.val < orders D c.pos (u.order P) g L z := i.2.isLt
    change Terms _ _ _ (s.observe P u.atCell (u.test P z (order i)))
    by_cases seam : z ∈ D
    · have he : (L : ℤ) ≤ -(order i) := by
        conv at hi => rhs; rw [orders, ite_eq_left seam]
        dsimp only [order, z] at *
        omega
      obtain ⟨⟨j, y⟩, hj, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp seam)
      exact u.exit p l hl hv hr ht hs j z (hy ▸ hj) _ he
    conv at hi => rhs; rw [orders, ite_eq_right seam]
    by_cases dest : z = c.pos
    · rw [ite_eq_left dest] at hi
      have he : order i ≤ (g * L : ℕ) := by dsimp only [order, z] at *; omega
      rw [dest]
      exact u.absorb p l hv hr c hc _ (by rw [ite_eq_left hc']; exact he)
    rw [ite_eq_right dest] at hi
    have he : order i ≤ 0 := by dsimp only [order, z] at *; omega
    have hz : z ∈ B := by
      have hz : z ∈ u.rest.sites := i.1.property
      rw [Cell.sites_eq] at hz
      exact (mem_union.mp hz).resolve_right seam
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    rw [← heq]
    exact u.absorb p l hv hr a ha _ (by split_ifs <;> omega)
  have bound : Fintype.card I ≤ M * window P g H N :=
    orders_card (u.order_le hr) (u.threshold_le hr) (u.room hr).1
  rw [eqn]
  refine (Terms.combine w term inter).mono ?_
  calc
    _ ≤ (M + 1) * window P g H N * width P g H N K :=
      Nat.mul_le_mul_right _ (bound.trans (Nat.mul_le_mul_right _ (Nat.le_succ M)))
    _ = _ := by unfold branches breadth width K P; ring

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# Elimination of all active insertions

Each productive step lowers an integer potential. The bound counts
only outer choices. All seam states and ordinary residue indices
remain inside the terms.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset
open scoped Classical
variable {F T V E X : Type} [Field F] [Fintype F] [Fintype V] [Fintype E]
  {r t g H U M N : ℕ} {src dst : E → V} (s : Stage F r t T V E X)

private theorem one_step (p l : ℕ) [ExpChar F p] (hl : s.Layout src dst g)
    (hv : s.Valid U) (hr : s.Room M N) (hs : M * (2 * N + 1) < Fintype.card F)
    (active : ¬s.Stopped) :
    Terms (p ^ l) (s.Gain (p ^ l) g H U) (branches (p ^ l) g H M N) (s.value (p ^ l)) := by
  obtain ⟨v, a, b, u, n, hc, ha, _, hk⟩ := hv.choose active
  let y := s.reord v a [u] b
  have perm : (s.scene.cell v).stations.Perm ([u] ++ a ++ b) := by
    rw [hc]
    exact List.perm_middle
  have step : s.Step (p ^ l) g H U y := .perm s v _ perm
  have valid : y.Valid U := hv.perm v _ perm
  have room : y.Room M N := hr.perm v _ perm
  let c : y.Ct := ⟨(s.scene.cell v).ports, a ++ b⟩
  have he : y.scene.cell v = c.insert u := by simp [y, reord, put, Scene.put, Cell.insert, c]
  have ready : y.Ready v c.stations := by
    refine ⟨hk.1, fun w hw t ht => hk.2 w hw t ?_⟩
    simp only [y, reord, put, Scene.put, Function.update_of_ne hw] at ht
    exact ht
  let m : Move y := ⟨v, c, u, n, he, ha, ready⟩
  have go := m.run (H := H) p l (step.layout hl) valid room hs
  rw [← observe_forms y v] at go
  rw [← observe_forms s v]
  exact rotate_terms v forms forms_signed a [u] b (by simpa using hc) go

/-- Eliminate every mover, uniformly over ordinary inputs. The local
room requirement follows from the initial bounds in `Reach.room`. -/
theorem complete (p l : ℕ) [ExpChar F p] (hl : s.Layout src dst g) (hv : s.Valid U)
    (room : ∀ y, s.Reach (p ^ l) g H U y → y.Room M N) (hF : M * (2 * N + 1) < Fintype.card F) :
    Terms (p ^ l) (fun y => s.Reach (p ^ l) g H U y ∧ y.Valid U ∧ y.Stopped)
      (branches (p ^ l) g H M N ^ s.potential U) (s.value (p ^ l)) := by
  let P := p ^ l
  let good (y) := s.Reach P g H U y ∧ y.Valid U ∧ y.Stopped
  let k := branches P g H M N
  have hk : 0 < k := branches_pos _ _ _ _ _
  have layout (y) (h : s.Reach P g H U y) : y.Layout src dst g := by
    induction h with
    | refl => exact hl
    | tail _ h ih => exact h.layout ih
  have go (n : ℕ) (y : Stage F r t T V E X) (hy : s.Reach P g H U y) (valid : y.Valid U)
      (hdecr : y.potential U ≤ n) : Terms P good (k ^ n) (y.value P) := by
    induction n using Nat.strong_induction_on generalizing y with
    | h n ih =>
      by_cases stop : y.Stopped
      · exact (Terms.one (good := good) ⟨hy, valid, stop⟩).mono (pow_pos hk _)
      obtain ⟨I, fi, c, z, hc, hz, he⟩ :=
        y.one_step (H := H) p l (layout y hy) valid (room y hy) hF stop
      cases n with
      | zero =>
        have e (i : I) : False := by have := (hz i).2.2; omega
        have : IsEmpty I := ⟨e⟩
        exact ⟨I, fi, c, z, by simp, fun i => (e i).elim, he⟩
      | succ n =>
        have h (i : I) : Terms P good (k ^ n) ((z i).value P) := by
          obtain ⟨reach, hv, lt⟩ := hz i
          exact ih n (by omega) (z i) (hy.trans reach) hv (by omega)
        rw [funext he, pow_succ']
        exact (Terms.combine c _ h).mono (Nat.mul_le_mul_right _ hc)
  exact go _ s .refl hv le_rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# Scales of one local concentration

The accuracy parameter `q` sets the private-wire rate. There are `d*b`
public species and `d` private ones. Their ratio `b` equals the
Frobenius power `P` times `q^4`. Only the number of blocks `d`
grows with the input scale `T`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale

open Routing.Private

def q (ℓ D : ℕ) := D ^ (ℓ + 32)
def size (ℓ D : ℕ) := q ℓ D ^ 8
def chunks (ℓ D : ℕ) := q ℓ D ^ 2
def probes (ℓ D : ℕ) := 1600 * D * size ℓ D
def energy (ℓ D R : ℕ) := R * size ℓ D ^ 2
def budget (g : ℕ) := 10000000 * (1 + 4 * g) * (energyConstant + 1)
def rate (ℓ D : ℕ) := 1 / (4 * (q ℓ D : ℝ))

/-- Enough distinct points for all original and auxiliary marks. -/
def slots (ℓ D g : ℕ) := 100 * D + 2 * g + probes ℓ D + 1

def room (ℓ D g : ℕ) := slots ℓ D g + budget g * D ^ 2
def depth (ℓ D g m R : ℕ) := budget g * D ^ 2 * m * energy ℓ D R

structure Scales (g ℓ D T P b d : ℕ) : Prop where
  large : 2 * budget g ≤ D
  pos : 0 < P
  block : b = P * q ℓ D ^ 4
  divides : chunks ℓ D ∣ d
  many : q ℓ D ^ 4 ≤ d * b
  lower : d * b * size ℓ D ≤ T
  upper : T ≤ 2 * (d * b * size ℓ D)

theorem budget_large (g : ℕ) : 10000000 ≤ budget g := by
  unfold budget
  calc
    10000000 = 10000000 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr <;> omega

namespace Scales
variable {g ℓ D T P b d : ℕ} (h : Scales g ℓ D T P b d)
include h

theorem bound : 10000000 ≤ D := (budget_large _).trans ((Nat.le_mul_of_pos_left _ (by decide)).trans h.large)
theorem Dpos : 0 < D := lt_of_lt_of_le (by decide) h.bound
theorem Dle : D ≤ q ℓ D := by
  simpa only [q, pow_one] using Nat.pow_le_pow_right h.Dpos (by omega : 1 ≤ ℓ + 32)
theorem qpos : 0 < q ℓ D := h.Dpos.trans_le h.Dle
theorem apos : 0 < size ℓ D := pow_pos h.qpos _
theorem Mpos : 0 < chunks ℓ D := pow_pos h.qpos _
theorem Rpos : 0 < d * b := (pow_pos h.qpos _).trans_le h.many
theorem Tpos : 0 < T := (Nat.mul_pos h.Rpos h.apos).trans_le h.lower
theorem Hpos : 0 < energy ℓ D (d * b) := Nat.mul_pos h.Rpos (pow_pos h.apos _)
theorem rate_pos : 0 < rate ℓ D := by have := h.qpos; unfold rate; positivity

theorem smallR : d * b * D ^ 2 ≤ T := by
  refine (Nat.mul_le_mul_left _ ?_).trans h.lower
  exact (Nat.pow_le_pow_left h.Dle 2).trans (Nat.pow_le_pow_right h.qpos (by decide))

theorem smallH : energy ℓ D (d * b) ≤ T * size ℓ D := by
  simpa only [energy, pow_two, mul_assoc] using Nat.mul_le_mul_right (size ℓ D) h.lower

theorem smallM : chunks ℓ D ≤ d * b :=
  (Nat.pow_le_pow_right h.qpos (by decide : 2 ≤ 4)).trans h.many

omit h in
theorem overhead : energyConstant + 1 ≤ budget g := by
  unfold budget
  apply Nat.le_mul_of_pos_left
  positivity

theorem degree : 2 * g ≤ D := by
  have hl := h.large
  have : 10000000 * (1 + 4 * g) ≤ budget g := Nat.le_mul_of_pos_right _ (by omega)
  omega

end Scales
end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-! # Polynomial bounds for the local expansion at one occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale

open Sphere.Surface Routing.Private

def initialChoices (ℓ D b d : ℕ) := ((d * b + 1) * (d * (energyConstant * b ^ 2) + 1)) ^ probes ℓ D
def moveChoices (g ℓ D m b d : ℕ) :=
  branches m (2 * g) (energy ℓ D (d * b)) (room ℓ D g) (depth ℓ D g m (d * b)) ^
    ((2 + 2 * D ^ 5) * (100 * D + probes ℓ D + 1))
def finalChoices (g ℓ D m b d : ℕ) :=
  (depth ℓ D g m (d * b) + 1) ^ (chunks ℓ D * (2 * g + 2 * room ℓ D g))

private theorem polynomial (g ℓ D m b : ℕ) :
    Poly (fun d => room ℓ D g * (2 * depth ℓ D g m (d * b) + 1) + 1 +
      initialChoices ℓ D b d * moveChoices g ℓ D m b d * finalChoices g ℓ D m b d) := by
  let M := room ℓ D g
  let H d := energy ℓ D (d * b)
  let N d := depth ℓ D g m (d * b)
  have he : Poly H := (Poly.var.mul (.const b)).mul (.const _)
  have hd : Poly N := (Poly.const _).mul he
  have hf : Poly (fun d => M * (2 * N d + 1) + 1) :=
    ((Poly.const M).mul (((Poly.const 2).mul hd).add (.const 1))).add (.const 1)
  have h₁ : Poly (initialChoices ℓ D b) :=
    (((Poly.var.mul (.const b)).add (.const 1)).mul
      ((Poly.var.mul (.const _)).add (.const 1))).pow _
  have hr : Poly (fun d => m * N d + N d) := ((Poly.const m).mul hd).add hd
  have hw : Poly (fun d => window m (2 * g) (H d) (N d)) :=
    (hr.add ((Poly.const _).mul (hr.add ((Poly.const _).mul he)))).add (.const 1)
  have hk : Poly (fun d => M * (2 * N d) + 1) :=
    ((Poly.const M).mul ((Poly.const 2).mul hd)).add (.const 1)
  have h₂ : Poly (moveChoices g ℓ D m b) :=
    ((((Poly.const (M + 1)).mul (hw.pow 2)).mul (hd.add (.const 1))).mul (hk.pow 2)).pow _
  have h₃ : Poly (finalChoices g ℓ D m b) := (hd.add (.const 1)).pow _
  exact hf.add ((h₁.mul h₂).mul h₃)

theorem choice_bound (g ℓ D m b : ℕ) :
    ∃ A : ℕ, ∀ {T d : ℕ}, Scales g ℓ D T m b d →
      room ℓ D g * (2 * depth ℓ D g m (d * b) + 1) < A * (1 + T) ^ A ∧
      initialChoices ℓ D b d * moveChoices g ℓ D m b d * finalChoices g ℓ D m b d ≤
        2 ^ (A * (1 + Nat.clog 2 (T + 1))) := by
  obtain ⟨k, hk⟩ := polynomial g ℓ D m b
  refine ⟨2 ^ k, fun {T d} sc => ?_⟩
  have ht : d ≤ T := by
    have := sc.Rpos
    exact (Nat.le_mul_of_pos_right d (Nat.pos_of_mul_pos_left sc.Rpos)).trans
      ((Nat.le_mul_of_pos_right _ sc.apos).trans sc.lower)
  have ub := (hk d).trans (Nat.pow_le_pow_left (by omega : d + 2 ≤ 2 * (1 + T)) k)
  have hb : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  constructor
  · have h : (2 * (1 + T)) ^ k ≤ 2 ^ k * (1 + T) ^ (2 ^ k) := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hb)
    exact (Nat.lt_of_succ_le (Nat.le_add_right _ _)).trans_le (ub.trans h)
  · refine (Nat.le_add_left _ _).trans (ub.trans ?_)
    calc
      _ ≤ (2 ^ (1 + Nat.clog 2 (T + 1))) ^ k := by
        apply Nat.pow_le_pow_left
        rw [pow_add, pow_one, Nat.add_comm 1 T]
        exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
      _ ≤ _ := by rw [← pow_mul, Nat.mul_comm]; exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hb)

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-!
# Choosing a field and block sizes

The planting field, positions, Frobenius power and block size can all
be fixed before the width tends to infinity. Rounding the number of
blocks to a multiple of the chunk count loses at most half the width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale

open Filter Finset Sphere

private theorem large_subfield (k : Type) [Field k] [Finite k] (M : ℕ) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Algebra k F)
      (_ : Algebra F (AlgebraicClosure k)), M ≤ Fintype.card F := by
  classical
  let x : Fin M ↪ AlgebraicClosure k := Fin.valEmbedding.trans (Infinite.natEmbedding _)
  let K := IntermediateField.adjoin k (Set.range x)
  have : Finite (Set.range x) := Set.finite_range _ |>.to_subtype
  have : Module.Finite k K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  have : Finite K := Module.finite_of_finite k
  let _ : Fintype K := Fintype.ofFinite K
  let f (i : Fin M) : K := ⟨x i, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    by simpa using Fintype.card_le_of_injective f (fun _ _ h => x.injective (congrArg Subtype.val h))⟩

variable {g ℓ D : ℕ}

private theorem scales_eventual (large : 2 * budget g ≤ D)
    (P b : ℕ) (hp : 0 < P) (hb : b = P * q ℓ D ^ 4) (d₀ : ℕ) :
    ∀ᶠ T : ℕ in atTop, ∃ d ≥ d₀, Scales g ℓ D T P b d := by
  have hd : 0 < D := by have := budget_large g; omega
  have hq : 0 < q ℓ D := pow_pos hd _
  have ha : 0 < size ℓ D := pow_pos hq _
  have hm : 0 < chunks ℓ D := pow_pos hq _
  have hb' : 0 < b := by rw [hb]; positivity
  let v := chunks ℓ D * b * size ℓ D
  have hv : 0 < v := by unfold v; positivity
  filter_upwards [eventually_ge_atTop ((d₀ + 1) * v)] with T hT
  have h : d₀ + 1 ≤ T / v := (Nat.le_div_iff_mul_le hv).mpr hT
  let d := chunks ℓ D * (T / v)
  have h₀ : d₀ + 1 ≤ d := h.trans (Nat.le_mul_of_pos_left _ hm)
  have he : d * b * size ℓ D = T / v * v := by unfold d v; ring
  refine ⟨d, by omega, large, hp, hb, ⟨T / v, rfl⟩, ?_, ?_, ?_⟩
  · exact (show q ℓ D ^ 4 ≤ b by rw [hb]; exact Nat.le_mul_of_pos_left _ hp).trans
      (Nat.le_mul_of_pos_left b (by omega))
  · rw [he]; exact Nat.div_mul_le_self _ _
  · rw [he]
    have hh := Nat.le_mul_of_pos_left v (by omega : 0 < T / v)
    have := Nat.div_add_mod' T v
    have := Nat.mod_lt T hv
    omega

def Ready (F : Type) [Field F] (ℓ D g P b d : ℕ) : Prop :=
  ∀ (B T E X : Type) (_ : Field B) (_ : Algebra F B) (u : Template F B T E X (d * b)),
    (∑ i, 4 * u.width i) ≤ probes ℓ D → u.stations ≤ 100 * D → u.ports ≤ 2 * g →
    Nonempty (u.Patch P (probes ℓ D) (rate ℓ D))

theorem choose (k : Type) [Field k] [Finite k] (sync : Prices.SharedPrice (AlgebraicClosure k))
    (large : 2 * budget g ≤ D) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Algebra k F)
      (p l b : ℕ) (_ : CharP F p) (_ : Fact p.Prime),
      ∀ᶠ T : ℕ in atTop, ∃ d, Scales g ℓ D T (p ^ l) b d ∧ Ready F ℓ D g (p ^ l) b d := by
  have hd : 0 < D := by have := budget_large g; omega
  have hq : 0 < q ℓ D := pow_pos hd _
  have ha : 0 < size ℓ D := pow_pos hq _
  have : NeZero (probes ℓ D) := ⟨by unfold probes; positivity⟩
  obtain ⟨F, _, _, _, _, hF⟩ := large_subfield k (slots ℓ D g)
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨b₀, hb⟩ := eventually_atTop.mp
    (Template.patches (F := F) (n := probes ℓ D) sync (show 0 < rate ℓ D by unfold rate; positivity))
  let b := p ^ b₀ * q ℓ D ^ 4
  have hp' : 0 < p := (Fact.out : p.Prime).pos
  have big : b₀ ≤ b := (Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le _)).trans (Nat.le_mul_of_pos_right _ (pow_pos hq _))
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp (hb b big)
  refine ⟨F, inferInstance, inferInstance, inferInstance, p, b₀, b, hp, inferInstance, ?_⟩
  filter_upwards [scales_eventual large _ b (pow_pos hp' b₀) rfl d₀] with T hT
  obtain ⟨d, hd, hs⟩ := hT
  refine ⟨d, hs, ?_⟩
  intro B V E X _ _ u hw hu hv
  apply hd₀ d hd _ ?_ B V E X inferInstance inferInstance u hw (by unfold slots at hF; omega)
  exact (iterateFrobenius F p b₀).injective

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end
