import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Basic.Real.Basic
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SplitIfs

/-! Integer difference constraints and the Floyd–Warshall construction in §7.1.
The entry `c i j` bounds `v j - v i`. Box constraints supply finite bounds even
for pairs with no explicit comparison. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Paths

abbrev Costs (ι : Type*) := ι → ι → ℤ

def relax {ι : Type*} (k : ι) (d : Costs ι) : Costs ι :=
  fun i j => min (d i j) (d i k + d k j)

def sweep {ι : Type*} : List ι → Costs ι → Costs ι
  | [], d => d
  | k :: ks, d => sweep ks (relax k d)

theorem sweep_le {ι : Type*} (ks : List ι) (d : Costs ι) (i j : ι) :
    sweep ks d i j ≤ d i j := by
  induction ks generalizing d with
  | nil => exact le_rfl
  | cons k ks ih => exact (ih (relax k d)).trans (min_le_left _ _)

def TriangleAt {ι : Type*} (d : Costs ι) (k : ι) : Prop :=
  ∀ i j, d i j ≤ d i k + d k j

private theorem relax_at_pivot {ι : Type*} (k : ι) (d : Costs ι)
    (hk : 0 ≤ d k k) : TriangleAt (relax k d) k := by
  intro i j
  have hik : d i k ≤ d i k + d k k := by omega
  have hkj : d k j ≤ d k k + d k j := by omega
  simpa only [relax, min_eq_left hik, min_eq_left hkj] using
    (min_le_right (d i j) (d i k + d k j))

private theorem relax_preserves_triangle {ι : Type*} (p k : ι) (d : Costs ι)
    (hp : 0 ≤ d p p) (ht : TriangleAt d k) : TriangleAt (relax p d) k := by
  intro i j
  have h₁ := ht i j
  have h₂ := ht i p
  have h₃ := ht p j
  have h₄ := ht p p
  simp only [relax, min_def]
  split_ifs <;> omega

private theorem sweep_preserves_triangle {ι : Type*} (ks : List ι) (d : Costs ι)
    (k : ι) (hs : ∀ i, 0 ≤ sweep ks d i i) (ht : TriangleAt d k) :
    TriangleAt (sweep ks d) k := by
  induction ks generalizing d with
  | nil => exact ht
  | cons p ks ih =>
    apply ih (relax p d) hs
    exact relax_preserves_triangle p k d ((hs p).trans (sweep_le (p :: ks) d p p)) ht

theorem sweep_triangle {ι : Type*} (ks : List ι) (d : Costs ι) (k : ι)
    (hk : k ∈ ks) (hs : ∀ i, 0 ≤ sweep ks d i i) : TriangleAt (sweep ks d) k := by
  induction ks generalizing d with
  | nil => simp at hk
  | cons p ks ih =>
    rcases List.mem_cons.mp hk with rfl | hk
    · apply sweep_preserves_triangle ks (relax k d) k hs
      exact relax_at_pivot k d ((hs k).trans (sweep_le (k :: ks) d k k))
    · exact ih (relax p d) hk hs

/-- Include each empty walk. -/
def initial {ι : Type*} [DecidableEq ι] (c : Costs ι) : Costs ι :=
  fun i j => if i = j then min 0 (c i j) else c i j

def distance {n : ℕ} (c : Costs (Fin n)) : Costs (Fin n) :=
  sweep (List.finRange n) (initial c)

theorem distance_le {n : ℕ} (c : Costs (Fin n)) (i j : Fin n) : distance c i j ≤ c i j := by
  apply (sweep_le _ _ _ _).trans
  simp only [initial]
  split <;> simp

theorem distance_triangle {n : ℕ} (c : Costs (Fin n)) (h : ∀ i, 0 ≤ distance c i i)
    (k i j : Fin n) : distance c i j ≤ distance c i k + distance c k j :=
  sweep_triangle _ _ k (List.mem_finRange _) h i j

theorem distance_diag {n : ℕ} (c : Costs (Fin n)) (h : ∀ i, 0 ≤ distance c i i) (i : Fin n) :
    distance c i i = 0 := by
  apply le_antisymm _ (h i)
  exact (sweep_le _ _ _ _).trans (by simp [initial])

/-- A potential in an ordered ring, including both the real polytope and its lattice points. -/
def Feasible {ι K : Type*} [Ring K] [LinearOrder K] (c : Costs ι) (v : ι → K) : Prop :=
  ∀ i j, v j - v i ≤ (c i j : K)

private theorem feasible_relax {ι K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    {c : Costs ι} {v : ι → K} (hc : Feasible c v) (k : ι) : Feasible (relax k c) v := by
  intro i j
  rw [relax, Int.cast_min, Int.cast_add]
  apply le_min (hc i j)
  calc
    v j - v i = (v k - v i) + (v j - v k) := by abel
    _ ≤ _ := add_le_add (hc i k) (hc k j)

private theorem feasible_sweep {ι K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    (ks : List ι) {c : Costs ι} {v : ι → K} (hc : Feasible c v) : Feasible (sweep ks c) v := by
  induction ks generalizing c with
  | nil => exact hc
  | cons k ks ih => exact ih (feasible_relax hc k)

theorem feasible_distance {n : ℕ} {K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    {c : Costs (Fin n)} {v : Fin n → K} (hc : Feasible c v) : Feasible (distance c) v := by
  apply feasible_sweep
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [initial] using hc i i
  · simpa [initial, hij] using hc i j

theorem feasible_diagonal {n : ℕ} {K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    {c : Costs (Fin n)} {v : Fin n → K} (hc : Feasible c v) : ∀ i, 0 ≤ distance c i i := by
  intro i
  have h : (0 : K) ≤ (distance c i i : K) := by simpa using feasible_distance hc i i
  exact_mod_cast h

def potential {n : ℕ} (c : Costs (Fin n)) (dummy s : Fin n) : Fin n → ℤ :=
  fun i => distance c s i - distance c s dummy

theorem potential_feasible {n : ℕ} {c : Costs (Fin n)} (h : ∀ i, 0 ≤ distance c i i)
    (dummy s : Fin n) : Feasible c (potential c dummy s) := by
  intro i j
  simp only [potential, Int.cast_id]
  have := distance_triangle c h i s j
  have := distance_le c i j
  omega

@[simp] theorem potential_dummy {n : ℕ} (c : Costs (Fin n)) (dummy s : Fin n) :
    potential c dummy s dummy = 0 := by simp [potential]

theorem potential_attains {n : ℕ} {c : Costs (Fin n)} (h : ∀ i, 0 ≤ distance c i i)
    (dummy s j : Fin n) : potential c dummy s j - potential c dummy s s = distance c s j := by
  simp [potential, distance_diag c h]

theorem feasible_iff_diagonal {n : ℕ} (c : Costs (Fin n)) (dummy : Fin n) :
    (∃ v : Fin n → ℤ, v dummy = 0 ∧ Feasible c v) ↔ ∀ i, 0 ≤ distance c i i := by
  constructor
  · rintro ⟨v, _, h⟩
    exact feasible_diagonal h
  · intro h
    exact ⟨_, potential_dummy c dummy dummy, potential_feasible h dummy dummy⟩

/-- Walk costs in the complete directed graph, including the empty walk. -/
inductive Walk {ι : Type*} (c : Costs ι) : ι → ι → ℤ → Prop where
  | nil (i) : Walk c i i 0
  | edge (i j) : Walk c i j (c i j)
  | append {i k j x y} : Walk c i k x → Walk c k j y → Walk c i j (x + y)

private theorem initial_walk {ι : Type*} [DecidableEq ι] (c : Costs ι) (i j : ι) :
    Walk c i j (initial c i j) := by
  by_cases h : i = j
  · subst j
    simp only [initial, ite_true]
    by_cases h : 0 ≤ c i i
    · rw [min_eq_left h]
      exact .nil i
    · rw [min_eq_right (le_of_not_ge h)]
      exact .edge i i
  · simpa [initial, h] using Walk.edge (c := c) i j

private theorem sweep_walk {ι : Type*} {c : Costs ι} (ks : List ι) (d : Costs ι)
    (h : ∀ i j, Walk c i j (d i j)) : ∀ i j, Walk c i j (sweep ks d i j) := by
  induction ks generalizing d with
  | nil => exact h
  | cons k ks ih =>
    apply ih (relax k d)
    intro i j
    by_cases hle : d i j ≤ d i k + d k j
    · simpa [relax, min_eq_left hle] using h i j
    · simpa [relax, min_eq_right (le_of_not_ge hle)] using (h i k).append (h k j)

theorem distance_walk {n : ℕ} (c : Costs (Fin n)) (i j : Fin n) :
    Walk c i j (distance c i j) := sweep_walk _ _ (initial_walk c) i j

theorem feasible_walk {ι : Type*} {c : Costs ι} {v : ι → ℤ} (hv : Feasible c v)
    {i j : ι} {w : ℤ} (walk : Walk c i j w) : v j - v i ≤ w := by
  induction walk with
  | nil i => simp
  | edge i j => exact hv i j
  | append _ _ h₁ h₂ => omega

theorem distance_is_shortest {n : ℕ} {c : Costs (Fin n)} (hs : ∀ i, 0 ≤ distance c i i)
    {i j : Fin n} {w : ℤ} (walk : Walk c i j w) : distance c i j ≤ w := by
  rw [← potential_attains hs i i j]
  exact feasible_walk (potential_feasible hs i i) walk

theorem negative_walk_iff {n : ℕ} (c : Costs (Fin n)) :
    (∃ i w, Walk c i i w ∧ w < 0) ↔ ∃ i, distance c i i < 0 := by
  constructor
  · rintro ⟨i, w, hw, hneg⟩
    by_contra! hn
    have hle := distance_is_shortest hn hw
    have hz := hn i
    omega
  · rintro ⟨i, hi⟩
    exact ⟨i, _, distance_walk c i i, hi⟩

/-- All intermediate weights have at most one additional magnitude bit per pivot,
even for inconsistent constraints. -/
theorem sweep_abs_le {ι : Type*} (ks : List ι) (d : Costs ι) {B : ℤ}
    (hB : 0 ≤ B) (hd : ∀ i j, |d i j| ≤ B) (i j : ι) :
    |sweep ks d i j| ≤ 2 ^ ks.length * B := by
  induction ks generalizing d B with
  | nil => simpa [sweep] using hd i j
  | cons k ks ih =>
    have hstep : ∀ i j, |relax k d i j| ≤ 2 * B := by
      intro i j
      by_cases hle : d i j ≤ d i k + d k j
      · rw [relax, min_eq_left hle]
        have := hd i j
        omega
      · rw [relax, min_eq_right (le_of_not_ge hle)]
        calc
          |d i k + d k j| ≤ |d i k| + |d k j| := abs_add_le _ _
          _ ≤ 2 * B := by have := hd i k; have := hd k j; omega
    simpa [sweep, pow_succ, mul_assoc] using ih (relax k d) (by omega : 0 ≤ 2 * B) hstep

theorem exists_integer_iff_real {n : ℕ} (c : Costs (Fin n)) (dummy : Fin n) :
    (∃ v : Fin n → ℤ, v dummy = 0 ∧ Feasible c v) ↔
    (∃ v : Fin n → ℝ, v dummy = 0 ∧ Feasible c v) := by
  constructor
  · rintro ⟨v, hz, hv⟩
    refine ⟨fun i => (v i : ℝ), by simp [hz], ?_⟩
    intro i j
    change (v j : ℝ) - (v i : ℝ) ≤ (c i j : ℝ)
    rw [← Int.cast_sub, Int.cast_le]
    exact hv i j
  · rintro ⟨v, _, hv⟩
    exact (feasible_iff_diagonal c dummy).2 (feasible_diagonal hv)

/-- The concrete representation materializes every stage. Evaluating a cell can therefore
never cause a prior stage to be recomputed. -/
abbrev Table (n : ℕ) := Vector (Vector ℤ n) n

def tabulate {n : ℕ} (d : Costs (Fin n)) : Table n :=
  Vector.ofFn fun i => Vector.ofFn (d i)

def read {n : ℕ} (a : Table n) (i j : Fin n) : ℤ := (a.get i).get j

@[simp] theorem read_tabulate {n : ℕ} (d : Costs (Fin n)) (i j : Fin n) :
    read (tabulate d) i j = d i j := by simp [read, tabulate]

def run {n : ℕ} : List (Fin n) → Table n → Table n
  | [], a => a
  | k :: ks, a => run ks (tabulate (relax k (read a)))

theorem read_run {n : ℕ} (ks : List (Fin n)) (a : Table n) :
    read (run ks a) = sweep ks (read a) := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    rw [run, ih, sweep]
    congr 1
    funext i j
    exact read_tabulate _ _ _

def compute {n : ℕ} (c : Costs (Fin n)) : Table n :=
  run (List.finRange n) (tabulate (initial c))

theorem compute_correct {n : ℕ} (c : Costs (Fin n)) : read (compute c) = distance c := by
  rw [compute, read_run]
  congr 1
  funext i j
  exact read_tabulate _ _ _

end Paths
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
