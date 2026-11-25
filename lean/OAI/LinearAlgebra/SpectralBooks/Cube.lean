import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! # Exterior splitting of a many-index endpoint price table

Each mark has two endpoints. The gap of a coordinate is the price at its
first endpoint minus that at its second, holding the other marks fixed.
Splitting clips that gap at the midpoint of its range and preserves the
bounds on all other gaps.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

abbrev CubeTable (r : ℕ) := (Fin r → Bool) → ℝ

namespace CubeTable

open Finset Function Set
noncomputable section
variable {r : ℕ}

def gap (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) : ℝ :=
  N (update x i false) - N (update x i true)

def lower (N : CubeTable r) (i : Fin r) : ℝ :=
  univ.inf' univ_nonempty (gap N i)

def upper (N : CubeTable r) (i : Fin r) : ℝ :=
  univ.sup' univ_nonempty (gap N i)

def width (N : CubeTable r) (i : Fin r) : ℝ := upper N i - lower N i

def midpoint (N : CubeTable r) (i : Fin r) : ℝ := (upper N i + lower N i) / 2

theorem gap_mem (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) :
    gap N i x ∈ Icc (lower N i) (upper N i) :=
  ⟨univ.inf'_le _ (mem_univ x), univ.le_sup' _ (mem_univ x)⟩

theorem lower_le_upper (N : CubeTable r) (i : Fin r) : lower N i ≤ upper N i :=
  let h := gap_mem N i (fun _ ↦ false)
  h.1.trans h.2

theorem lower_ge_of_forall (N : CubeTable r) (i : Fin r) {l : ℝ}
    (h : ∀ x, l ≤ gap N i x) : l ≤ lower N i :=
  Finset.le_inf' _ _ (fun x _ ↦ h x)

theorem upper_le_of_forall (N : CubeTable r) (i : Fin r) {u : ℝ}
    (h : ∀ x, gap N i x ≤ u) : upper N i ≤ u :=
  Finset.sup'_le _ _ (fun x _ ↦ h x)

theorem midpoint_mem (N : CubeTable r) (i : Fin r) : midpoint N i ∈ Icc (lower N i) (upper N i) := by
  unfold midpoint
  constructor <;> linarith [lower_le_upper N i]

theorem abs_gap_sub_gap_le_width (N : CubeTable r) (i : Fin r) (x y : Fin r → Bool) :
    |gap N i x - gap N i y| ≤ width N i := by
  have hx := gap_mem N i x
  have hy := gap_mem N i y
  rw [width, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The false child clips the first slice downward, and the true child clips
the second slice downward. -/
def child (N : CubeTable r) (i : Fin r) (b : Bool) : CubeTable r := fun x ↦
  if x i = b then min (N x) (N (update x i (!b)) + (if b then -midpoint N i else midpoint N i))
  else N x

abbrev plus (N : CubeTable r) (i : Fin r) := child N i false
abbrev minus (N : CubeTable r) (i : Fin r) := child N i true

theorem child_le (N : CubeTable r) (i : Fin r) (b : Bool) : child N i b ≤ N := by
  intro x
  unfold child
  split_ifs <;> first | exact min_le_left _ _ | rfl

theorem gap_plus (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) :
    gap (plus N i) i x = min (gap N i x) (midpoint N i) := by
  simp [gap, plus, child, ← min_sub_sub_right]

theorem gap_minus (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) :
    gap (minus N i) i x = max (gap N i x) (midpoint N i) := by
  simp [gap, minus, child, ← max_sub_sub_left]

private theorem gap_child_other_mem (N : CubeTable r) (i j : Fin r) (b : Bool)
    (hji : j ≠ i) (x : Fin r → Bool) :
    gap (child N i b) j x ∈ Icc (lower N j) (upper N j) := by
  have h := gap_mem N j x
  have h' := gap_mem N j (update x i (!b))
  simp only [gap, Set.mem_Icc] at h h'
  simp only [gap, child, update_of_ne hji.symm, update_comm hji]
  split_ifs <;> grind

theorem gap_child_mem (N : CubeTable r) (i j : Fin r) (b : Bool) (x : Fin r → Bool) :
    gap (child N i b) j x ∈ Icc (lower N j) (upper N j) := by
  by_cases hji : j = i
  · subst j
    have h := gap_mem N i x
    have hc := midpoint_mem N i
    cases b
    · rw [show child N i false = plus N i from rfl, gap_plus]
      exact ⟨le_min h.1 hc.1, (min_le_left _ _).trans h.2⟩
    · rw [show child N i true = minus N i from rfl, gap_minus]
      exact ⟨h.1.trans (le_max_left _ _), max_le h.2 hc.2⟩
  · exact gap_child_other_mem N i j b hji x

theorem lower_le_child (N : CubeTable r) (i j : Fin r) (b : Bool) :
    lower N j ≤ lower (child N i b) j :=
  lower_ge_of_forall _ _ (fun x ↦ (gap_child_mem N i j b x).1)

theorem upper_child_le (N : CubeTable r) (i j : Fin r) (b : Bool) :
    upper (child N i b) j ≤ upper N j :=
  upper_le_of_forall _ _ (fun x ↦ (gap_child_mem N i j b x).2)

theorem width_child_le (N : CubeTable r) (i j : Fin r) (b : Bool) :
    width (child N i b) j ≤ width N j :=
  sub_le_sub (upper_child_le N i j b) (lower_le_child N i j b)

/-- Halving the gap interval at the chosen mark. -/
theorem width_child (N : CubeTable r) (i : Fin r) (b : Bool) :
    width (child N i b) i ≤ width N i / 2 := by
  cases b
  · have h := upper_le_of_forall (plus N i) i (u := midpoint N i)
      (fun x ↦ by rw [gap_plus]; exact min_le_right _ _)
    dsimp [plus] at h
    unfold width
    linarith [lower_le_child N i i false, show 2 * midpoint N i = upper N i + lower N i by unfold midpoint; ring]
  · have h := lower_ge_of_forall (minus N i) i (l := midpoint N i)
      (fun x ↦ by rw [gap_minus]; exact le_max_right _ _)
    dsimp [minus] at h
    unfold width
    linarith [upper_child_le N i i true, show 2 * midpoint N i = upper N i + lower N i by unfold midpoint; ring]

end
end CubeTable

end SpectralBooks
end LinearAlgebra
end OAI
