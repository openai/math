import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Distances in the union of midpoint extensions

The finite stages in Corollary 2.5 preserve distances between parties
that have already appeared. The distance of two points in the union can
therefore be read at their first common stage. A single later stage suffices
to realize the entire distance matrix of a finite tuple.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {X : Type*}

/-- Read a distance at the first stage containing both arguments. -/
def unionDist (birth : X → ℕ) (d : ℕ → X → X → ℝ) (x y : X) : ℝ :=
  d (max (birth x) (birth y)) x y

/-- Each stage containing both points gives the distance in the union. -/
theorem unionDist_eq_stage {birth : X → ℕ} {d : ℕ → X → X → ℝ}
    (stable : ∀ n x y, birth x ≤ n → birth y ≤ n → d (n + 1) x y = d n x y)
    {n : ℕ} {x y : X} (hx : birth x ≤ n) (hy : birth y ≤ n) :
    unionDist birth d x y = d n x y := by
  have hn := max_le hx hy
  clear hx hy
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => rfl
  | succ m ih =>
    exact ih.trans (stable _ x y (by omega) (by omega)).symm

/-- The stage distances give a pseudometric on the union. The triangle
inequality can be checked in any stage containing the three points. -/
@[instance_reducible] noncomputable def unionPseudoMetric (birth : X → ℕ) (d : ℕ → X → X → ℝ)
    (stable : ∀ n x y, birth x ≤ n → birth y ≤ n → d (n + 1) x y = d n x y)
    (self : ∀ n x, d n x x = 0) (comm : ∀ n x y, d n x y = d n y x)
    (triangle : ∀ n x y z, d n x z ≤ d n x y + d n y z) : PseudoMetricSpace X where
  dist := unionDist birth d
  dist_self x := self _ x
  dist_comm x y := by
    simp only [unionDist, max_comm (birth y) (birth x)]
    exact comm _ _ _
  dist_triangle x y z := by
    let n := max (birth x) (max (birth y) (birth z))
    have hx : birth x ≤ n := le_max_left _ _
    have hy : birth y ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    have hz : birth z ≤ n := (le_max_right _ _).trans (le_max_right _ _)
    rw [unionDist_eq_stage stable hx hz, unionDist_eq_stage stable hx hy, unionDist_eq_stage stable hy hz]
    exact triangle n x y z

/-- All distances of a finite configuration are read at one common stage,
including for an empty tuple. -/
theorem unionDist_finite_stage {birth : X → ℕ} {d : ℕ → X → X → ℝ}
    (stable : ∀ n x y, birth x ≤ n → birth y ≤ n → d (n + 1) x y = d n x y)
    {ι : Type*} [Fintype ι] (f : ι → X) :
    ∃ n, (∀ i, birth (f i) ≤ n) ∧ ∀ i j, unionDist birth d (f i) (f j) = d n (f i) (f j) := by
  let n := Finset.univ.sup (birth ∘ f)
  have h (i : ι) : birth (f i) ≤ n := Finset.le_sup (f := birth ∘ f) (Finset.mem_univ i)
  exact ⟨n, h, fun i j ↦ unionDist_eq_stage stable (h i) (h j)⟩

end SpectralGeometry

end VPVNP
end Computability
end OAI
