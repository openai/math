import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.Basic

/-! Sites, groups, and fibers for the planar sunflower placement. -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

/-- Each anchor has an endpoint at each extreme height and one site at each satellite
height. Each satellite group consists of a single site. -/
abbrev Site (n : ℕ) := Fin (n + 2) ⊕ (Fin (n + 2) ⊕ Fin n)

variable {n : ℕ}

def a (j : Fin (n + 2)) : Site n := Sum.inl j
def b (j : Fin (n + 2)) : Site n := Sum.inr (Sum.inl j)
def z (i : Fin n) : Site n := Sum.inr (Sum.inr i)

/-- The index of the anchor site at the height of satellite `i`. -/
def interior (i : Fin n) : Fin (n + 2) := i.succ.castSucc

@[simp] theorem interior_val (i : Fin n) : (interior i).val = i.val + 1 := rfl

theorem interior_pos (i : Fin n) : 0 < interior i := by
  change 0 < i.val + 1
  omega

theorem interior_lt_last (i : Fin n) : interior i < Fin.last (n + 1) := by
  change i.val + 1 < n + 1
  omega

/-- Group 0 is the first anchor, group 1 the second, and group `i+2` a satellite. -/
def group : Site n → Fin (n + 2)
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr i) => i.succ.succ

@[simp] theorem group_a (j : Fin (n + 2)) : group (a j) = 0 := rfl
@[simp] theorem group_b (j : Fin (n + 2)) : group (b j) = 1 := rfl
@[simp] theorem group_z (i : Fin n) : group (z i) = i.succ.succ := rfl

private theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'

private theorem sat_ne_zero (i : Fin n) : i.succ.succ ≠ (0 : Fin (n + 2)) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'

private theorem sat_ne_one (i : Fin n) : i.succ.succ ≠ (1 : Fin (n + 2)) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'

def fiber (g : Fin (n + 2)) : Finset (Site n) := Finset.univ.filter (group · = g)

@[simp] theorem mem_fiber {s : Site n} {g : Fin (n + 2)} : s ∈ fiber g ↔ group s = g := by
  simp [fiber]

theorem fiber_zero : fiber (0 : Fin (n + 2)) = Finset.univ.image a := by
  ext s
  rcases s with j | (j | i)
  · exact iff_of_true (mem_fiber.mpr (group_a j)) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · simp [group, a, zero_ne_one.symm]
  · simp [group, a]

theorem fiber_one : fiber (1 : Fin (n + 2)) = Finset.univ.image b := by
  ext s
  rcases s with j | (j | i)
  · simp [group, b]
  · exact iff_of_true (mem_fiber.mpr (group_b j)) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · simp [group, b, sat_ne_one]

@[simp] theorem fiber_satellite (i : Fin n) : fiber i.succ.succ = {z i} := by
  ext s
  rcases s with j | (j | k)
  · simp [group, z, (sat_ne_zero i).symm]
  · simp [group, z, (sat_ne_one i).symm]
  · simp [group, z]

theorem fiber_nonempty (g : Fin (n + 2)) : (fiber g).Nonempty := by
  refine Fin.cases ?_ (fun g' => ?_) g
  · exact ⟨a 0, mem_fiber.mpr rfl⟩
  refine Fin.cases ?_ (fun i => ?_) g'
  · exact ⟨b 0, mem_fiber.mpr rfl⟩
  · exact ⟨z i, mem_fiber.mpr rfl⟩

theorem group_surjective : Function.Surjective (@group n) :=
  fun g => let ⟨s, hs⟩ := fiber_nonempty g; ⟨s, mem_fiber.mp hs⟩

/-- Every group other than the anchors is uniquely indexed by its satellite. -/
theorem exists_satellite_index {g : Fin (n + 2)} (h0 : g ≠ 0) (h1 : g ≠ 1) :
    ∃ i : Fin n, g = i.succ.succ := by
  revert h0 h1
  refine Fin.cases (by simp) (fun j => ?_) g
  refine Fin.cases (by simp) (fun i _ _ => ⟨i, rfl⟩) j

/-- Satellites are singletons, so only the two anchor terms contribute to any sum of
group prices that vanishes on singletons. -/
theorem sum_fibers_eq_add_of_zero_satellites {M : Type*} [AddCommMonoid M]
    (v : Finset (Site n) → M) (hz : ∀ i : Fin n, v {z i} = 0) :
    ∑ g : Fin (n + 2), v (fiber g) = v (fiber 0) + v (fiber 1) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hz]

end Placement
end Sunflower
end Combinatorics
end OAI
