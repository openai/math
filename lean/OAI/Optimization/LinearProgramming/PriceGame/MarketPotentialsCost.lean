import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentials
import OAI.Optimization.LinearProgramming.PriceGame.MarketNumberBounds
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Execution counts and rational register sizes for the finite residual-network Bellman table. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Potentials
namespace Cost

open Quiver
open scoped BigOperators

variable {V : Type*} [Quiver V] {n : ℕ} (index : V ≃ Fin n)

/-- Each vertex owns a materialized list of its outgoing arcs in input order. -/
abbrev Rows := Layer (fun j : Fin n => List (Σ b : V, index.symm j ⟶ b))

/-- Constructing this table evaluates the supplied adjacency list once for each vertex. -/
def prepare (out : (a : V) → List (Σ b : V, a ⟶ b)) : Rows index :=
  Layer.tabulate index out

def outgoing (rows : Rows index) (a : V) : List (Σ b : V, a ⟶ b) :=
  Layer.lookup (T := fun i => List (Σ j : V, i ⟶ j)) index rows a

@[simp] theorem outgoing_prepare (out : (a : V) → List (Σ b : V, a ⟶ b)) (a : V) :
    outgoing index (prepare index out) a = out a := Layer.lookup_tabulate index out a

/-- Dense input presents one optional arc for each ordered pair of numbered vertices. -/
def denseRow (edge : (a b : V) → Option (a ⟶ b)) (a : V) : List (Σ b : V, a ⟶ b) :=
  (List.finRange n).filterMap fun j => (edge a (index.symm j)).map (fun e => ⟨index.symm j, e⟩)

def prepareDense (edge : (a b : V) → Option (a ⟶ b)) : Rows index :=
  prepare index (denseRow index edge)

theorem dense_complete (edge : (a b : V) → Option (a ⟶ b)) {a b : V} (e : a ⟶ b)
    (he : edge a b = some e) : (⟨b, e⟩ : Σ z : V, a ⟶ z) ∈
      outgoing index (prepareDense index edge) a := by
  simp only [prepareDense, outgoing_prepare, denseRow]
  apply List.mem_filterMap.mpr
  refine ⟨index b, List.mem_finRange _, ?_⟩
  let pack (v : V) := (edge a v).map (fun t => (⟨v, t⟩ : Σ z : V, a ⟶ z))
  change pack (index.symm (index b)) = _
  rw [index.symm_apply_apply]
  simp [pack, he]

theorem denseRow_length_le (edge : (a b : V) → Option (a ⟶ b)) (a : V) :
    (denseRow index edge a).length ≤ n := by
  exact (List.length_filterMap_le ..).trans (by simp)

def arcCount (rows : Rows index) : ℕ :=
  ∑ j : Fin n, (outgoing index rows (index.symm j)).length

theorem dense_arcCount_le (edge : (a b : V) → Option (a ⟶ b)) :
    arcCount index (prepareDense index edge) ≤ n * n := by
  calc
    _ ≤ ∑ _j : Fin n, n :=
      Finset.sum_le_sum fun j _ => by
        simpa [prepareDense] using denseRow_length_le index edge (index.symm j)
    _ = _ := by simp

/-- `visits` counts the individual list entries examined by the maximum scan. -/
structure RowResult where
  best : ℚ
  visits : ℕ

def scan {E : Type*} (score : E → ℚ) (best : ℚ) : List E → RowResult
  | [] => ⟨best, 0⟩
  | e :: es =>
    let result := scan score (max best (score e)) es
    ⟨result.best, result.visits + 1⟩

theorem scan_visits {E : Type*} (score : E → ℚ) (best : ℚ) (es : List E) :
    (scan score best es).visits = es.length := by
  induction es generalizing best <;> simp [scan, *]

theorem scan_le_iff {E : Type*} (score : E → ℚ) (best limit : ℚ) (es : List E) :
    (scan score best es).best ≤ limit ↔ best ≤ limit ∧ ∀ e ∈ es, score e ≤ limit := by
  induction es generalizing best with
  | nil => simp [scan]
  | cons e es ih => simp [scan, ih, and_assoc]

def read (values : Vector ℚ n) (v : V) : ℚ := values[(index v).val]

variable (w : ∀ {i j : V}, (i ⟶ j) → ℚ) (r : V → ℚ)

def evaluateRow (rows : Rows index) (previous : Vector ℚ n) (i : V) : RowResult :=
  scan (fun je : Σ j : V, i ⟶ j => w je.2 + read index previous je.1)
    (r i) (outgoing index rows i)

/-- The counters accumulate the visits made by the row scans.
The table stores one rational per vertex and discards the preceding layer once consumed. -/
structure Run (n : ℕ) where
  values : Vector ℚ n
  visits : ℕ
  written : ℕ

def execute (rows : Rows index) : ℕ → Run n
  | 0 => ⟨Vector.ofFn (fun j => r (index.symm j)), 0, n⟩
  | k + 1 =>
    let previous := execute rows k
    let results := Vector.ofFn fun j => evaluateRow index w r rows previous.values (index.symm j)
    ⟨results.map RowResult.best, previous.visits + ∑ j : Fin n, results[j.val].visits,
      previous.written + n⟩

/-- Running `k` Bellman layers adds and compares one cost at each actual edge visit,
and writes exactly one output per vertex in the initial and subsequent layers. -/
theorem execute_counts (rows : Rows index) (k : ℕ) :
    (execute index w r rows k).visits = k * arcCount index rows ∧
    (execute index w r rows k).written = (k + 1) * n := by
  induction k with
  | zero => simp [execute]
  | succ k ih => simp [execute, evaluateRow, scan_visits, ih.1, ih.2, arcCount, Nat.succ_mul]

theorem dense_execute_counts (edge : (a b : V) → Option (a ⟶ b)) (k : ℕ) :
    (execute index w r (prepareDense index edge) k).visits ≤ k * (n * n) ∧
    (execute index w r (prepareDense index edge) k).written = (k + 1) * n := by
  obtain ⟨hv, hw⟩ := execute_counts index w r (prepareDense index edge) k
  exact ⟨hv ▸ Nat.mul_le_mul_left k (dense_arcCount_le index edge), hw⟩

section Correctness
variable [Fintype V] [∀ i j : V, Fintype (i ⟶ j)]
variable (rows : Rows index)
variable (full : ∀ {i j : V} (e : i ⟶ j), (⟨j,e⟩ : Σ z : V, i ⟶ z) ∈ outgoing index rows i)

include full in
theorem evaluateRow_eq (prev : Vector ℚ n) (i : V) :
    (evaluateRow index w r rows prev i).best = relax w r (read index prev) i := by
  apply le_antisymm
  · apply (scan_le_iff ..).mpr
    exact ⟨score_le_relax w r (read index prev) i none,
      fun je _ => score_le_relax w r (read index prev) i (some je)⟩
  · apply Finset.sup'_le
    intro o _
    have h := (scan_le_iff (fun je : Σ j : V, i ⟶ j => w je.2 + read index prev je.1)
      (r i) (evaluateRow index w r rows prev i).best (outgoing index rows i)).mp le_rfl
    cases o with
    | none => exact h.1
    | some o => exact h.2 o (full o.2)

include full in
theorem execute_correct (k : ℕ) (a : V) :
    read index (execute index w r rows k).values a = value w r k a := by
  induction k generalizing a with
  | zero => simp [execute, read, value]
  | succ k ih =>
    simp only [read, execute, Vector.getElem_map, Vector.getElem_ofFn, value]
    rw [evaluateRow_eq index w r rows full]
    change relax w r _ (index.symm (index a)) = _
    rw [index.symm_apply_apply]
    exact congrArg (fun z => relax w r z a) (funext ih)

/-- Materialize all longest-walk potentials in one table. Subsequent reads do no relaxations. -/
def computedPotential (adj : Rows index) : Vector ℚ n :=
  (execute index w r adj (n - 1)).values

include full in
theorem computedPotential_correct (a : V) :
    read index (computedPotential index w r rows) a = potential w r a := by
  have hn : Fintype.card V = n := (Fintype.card_congr index).trans (Fintype.card_fin _)
  simpa [computedPotential, potential, hn] using execute_correct index w r rows full (n-1) a

end Correctness


/-- This instruments the same accumulator and comparison function used by `List.argmax`. -/
def tracedArgmax {α β : Type*} [LinearOrder β] (key : α → β) (xs : List α) : Option α × ℕ :=
  xs.foldl (fun state x =>
    (List.argAux (fun x y => key y < key x) state.1 x, state.2 + if state.1.isSome then 1 else 0))
    (none, 0)

theorem tracedArgmax_eq {α β : Type*} [LinearOrder β] (key : α → β) (a : α) (xs : List α) :
    tracedArgmax key (a :: xs) = ((a :: xs).argmax key, xs.length) := by
  let cmp (x y : α) := key y < key x
  let step (s : Option α × ℕ) (x : α) :=
    (List.argAux cmp s.1 x, s.2 + if s.1.isSome then 1 else 0)
  have run (ys : List α) (best : α) (n : ℕ) :
      ys.foldl step (some best,n) = (ys.foldl (List.argAux cmp) (some best), n+ys.length) := by
    induction ys generalizing best n with
    | nil => simp
    | cons y ys ih =>
      simp only [List.foldl_cons, List.length_cons]
      by_cases h : key best < key y
      · simpa [step, cmp, List.argAux, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih y (n+1)
      · simpa [step, cmp, List.argAux, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih best (n+1)
  simpa [tracedArgmax, List.argmax, step, cmp, List.argAux] using run xs a 0

/-- A witness table row uses exactly one real argmax comparison per outgoing arc. The first
(stopping) candidate initializes the accumulator for free. -/
theorem actual_argmax_count {α β : Type*} [LinearOrder β] (key : α → β) (a : α) (xs : List α) :
    (tracedArgmax key (a :: xs)).2 = xs.length := by rw [tracedArgmax_eq]

/-- Count one comparison for each non-stop candidate examined by the witness-producing table. -/
def witnessComparisons (rows : Rows index) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, ∑ v : Fin n,
    (Plan.scan (Plan.stop w r (index.symm v)) ((outgoing index rows (index.symm v)).map
      (fun je => Plan.prepend je.2 (Layer.lookup index (plans index w r (outgoing index rows) k) je.1)))).2

theorem witnessComparisons_eq (rows : Rows index) (K : ℕ) :
    witnessComparisons index w r rows K = K * arcCount index rows := by
  simp [witnessComparisons, arcCount, Plan.scan_eq]

/-- The quiver represents walks by snoc. Prepending an arc to a cached route thus copies one
constructor per old arc, plus the new arc. This counts even candidates discarded at that row. -/
def witnessNodes (rows : Rows index) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, ∑ v : Fin n,
    ((outgoing index rows (index.symm v)).map (fun je =>
      (Layer.lookup index (plans index w r (outgoing index rows) k) je.1).path.length + 1)).sum

private theorem sum_list_le {α : Type*} (xs : List α) (f : α → ℕ) (b : ℕ) (hf : ∀ x, f x ≤ b) :
    (xs.map f).sum ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (hf x) ih

theorem witnessNodes_le (rows : Rows index) (K : ℕ) :
    witnessNodes index w r rows K ≤ K * (arcCount index rows * K) := by
  unfold witnessNodes
  calc
    _ ≤ ∑ _k ∈ Finset.range K, arcCount index rows * K := by
      apply Finset.sum_le_sum
      intro k hk
      have hK : k < K := Finset.mem_range.mp hk
      rw [arcCount, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      apply sum_list_le
      intro je
      let z := Layer.lookup index (plans index w r (outgoing index rows) k) je.1
      have hlen : z.path.length ≤ k := z.steps_spec ▸ plans_steps_le index w r (outgoing index rows) k je.1
      change z.path.length + 1 ≤ K
      omega
    _ = _ := by simp

theorem witness_dense_bounds (edge : (a b : V) → Option (a ⟶ b)) (K : ℕ) :
    witnessComparisons index w r (prepareDense index edge) K ≤ K * (n * n) ∧
    witnessNodes index w r (prepareDense index edge) K ≤ K * ((n * n) * K) := by
  have h := dense_arcCount_le index edge
  exact ⟨(witnessComparisons_eq index w r _ K).le.trans (Nat.mul_le_mul_left _ h),
    (witnessNodes_le index w r _ K).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h))⟩

private theorem product_bits (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (Nat.two_pow_pos _))

private theorem add_bits (a b : ℕ) : (a+b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2^(a.size + b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2^(a.size + b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]
  omega

/-- Reduced numerator and denominator widths when a common integer scale and magnitude are known. -/
theorem rational_bits {q : ℚ} {D M : ℕ} (hD : 0 < D) (hgrid : ∃ z : ℤ, (D : ℚ)*q = z)
    (hmag : |q| ≤ (M : ℚ)) :
    q.den.size ≤ D.size ∧ q.num.natAbs.size ≤ M.size + D.size := by
  have hden := Nat.le_of_dvd hD ((NumberBounds.grid_iff_den_dvd hD q).mp hgrid)
  have hnum := (NumberBounds.numerator_le_of_abs_le hmag).trans (Nat.mul_le_mul_left M hden)
  exact ⟨Nat.size_le_size hden, (Nat.size_le_size hnum).trans (product_bits M D)⟩

/-- A score is the sum of at most `k` arc weights and one terminal reward. This bounds its
reduced numerator/denominator in bits, including scores evaluated for losing candidates. -/
theorem path_score_bits (D C R k : ℕ) (hD : 0 < D)
    (edgegrid : ∀ {i j : V} (e : i ⟶ j), ∃ z : ℤ, (D : ℚ)*w e = z)
    (endgrid : ∀ j, ∃ z : ℤ, (D : ℚ)*r j = z)
    (hedge : ∀ {i j : V} (e : i ⟶ j), |w e| ≤ (C : ℚ))
    (hend : ∀ j, |r j| ≤ (R : ℚ)) {a b : V} (p : Path a b) (hp : p.length ≤ k) :
    (p.addWeight w + r b).den.size ≤ D.size ∧
    (p.addWeight w + r b).num.natAbs.size ≤ k.size+C.size+R.size+D.size+1 := by
  obtain ⟨z, hz⟩ := weight_denominator w D edgegrid p
  obtain ⟨y, hy⟩ := endgrid b
  have hg : ∃ t : ℤ, (D : ℚ) * (p.addWeight w + r b) = t :=
    ⟨z+y, by rw [mul_add, hz, hy, Int.cast_add]⟩
  have hm : |p.addWeight w + r b| ≤ ((k*C + R : ℕ) : ℚ) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    have hk : (p.length : ℚ) * C ≤ (k : ℚ) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hp)
      (Nat.cast_nonneg _)
    exact (abs_add_le _ _).trans (add_le_add ((abs_weight_le w C hedge p).trans hk) (hend b))
  obtain ⟨hd, hn⟩ := rational_bits hD hg hm
  have hA := add_bits (k*C) R
  have hB := product_bits k C
  exact ⟨hd, by omega⟩

/-- The path length used to break score ties fits in the binary size of the current layer. -/
theorem tieLength_bits (rows : Rows index) (k : ℕ) (a : V) :
    (Layer.lookup index (plans index w r (outgoing index rows) k) a).steps.size ≤ k.size :=
  Nat.size_le_size (plans_steps_le index w r (outgoing index rows) k a)

/-- Instrumented dense enumeration includes unsuccessful arc probes. -/
def filterProbes {α β : Type*} (f : α → Option β) : List α → List β × ℕ
  | [] => ([], 0)
  | a :: rest =>
    let result := filterProbes f rest
    match f a with
    | some b => (b :: result.1, result.2+1)
    | none => (result.1, result.2+1)

theorem filterProbes_eq {α β : Type*} (f : α → Option β) (xs : List α) :
    filterProbes f xs = (xs.filterMap f, xs.length) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : f a <;> simp [filterProbes, ih, h]

def preparationProbes (edge : (a b : V) → Option (a ⟶ b)) : ℕ :=
  ∑ i : Fin n, (filterProbes (fun j : Fin n =>
    (edge (index.symm i) (index.symm j)).map fun e => (⟨index.symm j, e⟩ : Σ b : V, index.symm i ⟶ b))
    (List.finRange n)).2

theorem preparationProbes_eq (edge : (a b : V) → Option (a ⟶ b)) :
    preparationProbes index edge = n * n := by simp [preparationProbes, filterProbes_eq]

/-- For the `n-1`-round longest-walk computation these counts include dense adjacency
construction, every candidate comparison, every newly copied path node, and all stored rows. -/
theorem full_horizon_work (edge : (a b : V) → Option (a ⟶ b)) (K : ℕ) (hk : K ≤ n) :
    preparationProbes index edge = n ^ 2 ∧
    witnessComparisons index w r (prepareDense index edge) K ≤ n ^ 3 ∧
    witnessNodes index w r (prepareDense index edge) K ≤ n ^ 4 ∧
    (execute index w r (prepareDense index edge) K).visits ≤ n ^ 3 ∧
    (execute index w r (prepareDense index edge) K).written ≤ (n+1)*n := by
  obtain ⟨hc, hnodes⟩ := witness_dense_bounds index w r edge K
  obtain ⟨he, hw⟩ := dense_execute_counts index w r edge K
  have h₃ : K*(n*n) ≤ n^3 := by
    calc _ ≤ n*(n*n) := Nat.mul_le_mul_right _ hk
         _ = _ := by ring
  have h₄ : K*((n*n)*K) ≤ n^4 := by
    calc _ ≤ n*((n*n)*n) := Nat.mul_le_mul hk (Nat.mul_le_mul_left _ hk)
         _ = _ := by ring
  exact ⟨by simpa [pow_two] using preparationProbes_eq index edge, hc.trans h₃, hnodes.trans h₄,
    he.trans h₃, hw.le.trans (Nat.mul_le_mul_right _ (by omega))⟩

section Intermediate
variable [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] (rows : Rows index)
variable (full : ∀ {i j : V} (e : i ⟶ j), (⟨j,e⟩ : Σ z : V, i ⟶ z) ∈ outgoing index rows i)
variable (D C R : ℕ) (hD : 0 < D)
variable (edgegrid : ∀ {i j : V} (e : i ⟶ j), ∃ z : ℤ, (D : ℚ)*w e = z)
variable (endgrid : ∀ j, ∃ z : ℤ, (D : ℚ)*r j = z)
variable (hedge : ∀ {i j : V} (e : i ⟶ j), |w e| ≤ (C : ℚ)) (hend : ∀ j, |r j| ≤ (R : ℚ))

include full hD edgegrid endgrid hedge hend in
theorem stored_score_bits (k : ℕ) (v : V) :
    let q := read index (execute index w r rows k).values v
    q.den.size ≤ D.size ∧ q.num.natAbs.size ≤ k.size+C.size+R.size+D.size+1 := by
  dsimp only
  rw [execute_correct index w r rows full k v]
  obtain ⟨u, p, hp, h⟩ := value_attained w r k v
  rw [h]
  exact path_score_bits w r D C R k hD edgegrid endgrid hedge hend p hp

include full hD edgegrid endgrid hedge hend in
/-- Before comparison, including for an edge whose candidate loses, the resulting rational
already has the same polynomial width as the output of the next layer. -/
theorem candidate_score_bits (k : ℕ) {u v : V} (e : u ⟶ v) :
    let q := w e + read index (execute index w r rows k).values v
    q.den.size ≤ D.size ∧ q.num.natAbs.size ≤ (k+1).size+C.size+R.size+D.size+1 := by
  dsimp only
  rw [execute_correct index w r rows full k v]
  obtain ⟨z, p, hp, hh⟩ := value_attained w r k v
  have hlen : (e.toPath.comp p).length ≤ k+1 := by simpa [Nat.add_comm] using Nat.succ_le_succ hp
  rw [hh]
  simpa [Quiver.Hom.toPath, add_assoc] using
    path_score_bits w r D C R (k+1) hD edgegrid endgrid hedge hend (e.toPath.comp p) hlen


include full hD edgegrid endgrid hedge hend in
/-- A bound in precisely the signed numerator and positive denominator encoding of the LP RAM. -/
theorem stored_ratBits (k : ℕ) (a : V) :
    RAM.ratBits (read index (execute index w r rows k).values a) ≤
      4+k.size+C.size+R.size+2*D.size := by
  rw [execute_correct index w r rows full]
  have hg := NumberBounds.intermediate_grid w (D := D) edgegrid r endgrid k a
  have hm := NumberBounds.intermediate_abs w (Nat.cast_nonneg (α := ℚ) C) hedge r hend k a
  have he : |value w r k a| ≤ ((k*C+R : ℕ) : ℚ) := by simpa using hm
  have h₁ := NumberBounds.ratBits_grid hD hg he
  have h₂ := add_bits (k*C) R
  have h₃ := product_bits k C
  omega

include full hD edgegrid endgrid hedge hend in
theorem candidate_ratBits (k : ℕ) {a b : V} (e : a ⟶ b) :
    RAM.ratBits (w e + read index (execute index w r rows k).values b) ≤
      4+(k+1).size+C.size+R.size+2*D.size := by
  rw [execute_correct index w r rows full]
  have hg := NumberBounds.OnGrid.add (edgegrid e)
    (NumberBounds.intermediate_grid w (D := D) edgegrid r endgrid k b)
  have hb := NumberBounds.intermediate_abs w (Nat.cast_nonneg (α := ℚ) C) hedge r hend k b
  have hm : |w e + value w r k b| ≤ (((k+1)*C+R : ℕ) : ℚ) := by
    calc _ ≤ |w e| + |value w r k b| := abs_add_le _ _
         _ ≤ (C : ℚ) + ((k:ℚ)*C+R) := add_le_add (hedge e) hb
         _ = _ := by push_cast; ring
  have h₁ := NumberBounds.ratBits_grid hD hg hm
  have h₂ := add_bits ((k+1)*C) R
  have h₃ := product_bits (k+1) C
  omega

end Intermediate

end Cost
end Potentials
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
