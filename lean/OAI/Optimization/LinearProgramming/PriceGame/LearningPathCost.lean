import OAI.Optimization.LinearProgramming.PriceGame.LearningPaths
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-! A costed execution of the dense integer difference-constraint algorithm.
The counter increments inside the computation of each matrix entry. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Paths

private def spend {α : Type} (a : α) (k : ℕ) : StateM ℕ α := fun s => (a, s + k)

private theorem ofFnM_spend {α : Type} {n : ℕ} (f : Fin n → α) (k : ℕ) :
    Vector.ofFnM (fun i => spend (f i) k) = spend (Vector.ofFn f) (n * k) := by
  induction n with
  | zero =>
    rw [Vector.ofFnM_zero]
    funext s
    change (#v[], s) = (Vector.ofFn f, s + 0 * k)
    apply Prod.ext _ (by simp)
    ext i hi
    omega
  | succ n ih =>
    rw [Vector.ofFnM_succ, Vector.ofFn_succ, ih]
    funext s
    change ((Vector.ofFn (fun i : Fin n => f i.castSucc)).push (f (Fin.last n)),
      s + n * k + k) = (_, s + (n + 1) * k)
    simp [Nat.add_mul, Nat.add_assoc]
    rfl

/-- One costed operation per evaluated cell, charged at the point it is produced. -/
def countTable {n : ℕ} (d : Costs (Fin n)) : StateM ℕ (Table n) :=
  Vector.ofFnM fun i => Vector.ofFnM fun j => spend (d i j) 1

private theorem countTable_eq {n : ℕ} (d : Costs (Fin n)) :
    countTable d = spend (tabulate d) (n ^ 2) := by
  simp [countTable, ofFnM_spend, tabulate, pow_two]

def countRun {n : ℕ} : List (Fin n) → Table n → StateM ℕ (Table n)
  | [], a => pure a
  | k :: ks, a => do
    let next ← countTable (relax k (read a))
    countRun ks next

private theorem countRun_eq {n : ℕ} (ks : List (Fin n)) (a : Table n) :
    countRun ks a = spend (run ks a) (ks.length * n ^ 2) := by
  induction ks generalizing a with
  | nil =>
    funext s
    simp [countRun, run, spend]
    rfl
  | cons k ks ih =>
    rw [countRun, countTable_eq]
    funext s
    change countRun ks (tabulate (relax k (read a))) (s + n ^ 2) =
      (_, s + (k :: ks).length * n ^ 2)
    rw [ih]
    change (_, s + n ^ 2 + ks.length * n ^ 2) = (_, s + (ks.length + 1) * n ^ 2)
    exact Prod.ext rfl (by ring)

/-- The initial table and each pivot table are materialized by counted cell computations. -/
def countCompute {n : ℕ} (c : Costs (Fin n)) : StateM ℕ (Table n) := do
  let a ← countTable (initial c)
  countRun (List.finRange n) a

theorem countCompute_correct {n : ℕ} (c : Costs (Fin n)) (s : ℕ) :
    (countCompute c).run s = (compute c, s + n ^ 2 + n ^ 3) := by
  rw [countCompute, countTable_eq]
  change countRun (List.finRange n) (tabulate (initial c)) (s + n ^ 2) = _
  rw [countRun_eq]
  exact Prod.ext rfl (by simp [spend]; ring)

/-- A sign-and-magnitude integer requires at most one sign bit beyond this magnitude width. -/
theorem sweep_magnitude_bits {ι : Type*} (ks : List ι) (d : Costs ι) (B : ℕ)
    (hd : ∀ i j, (d i j).natAbs ≤ B) (i j : ι) :
    (sweep ks d i j).natAbs.size ≤ ks.length + B.size := by
  have h₁ (i j) : |d i j| ≤ (B : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hd i j
  have h₂ := sweep_abs_le ks d (Int.natCast_nonneg B) h₁ i j
  have h₃ : (sweep ks d i j).natAbs ≤ 2 ^ ks.length * B := by
    exact_mod_cast (show ((sweep ks d i j).natAbs : ℤ) ≤ (2 : ℤ) ^ ks.length * B by
      simpa only [Int.natCast_natAbs] using h₂)
  apply Nat.size_le.mpr
  rw [pow_add]
  exact h₃.trans_lt (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self B) (Nat.two_pow_pos _))

/-- Each lookup in the eager matrix reads a row and an entry. An initial cell reads
its input, tests the diagonal, clamps by zero, selects its value, and writes it. -/
private def initEntry {n : ℕ} (a : Table n) (i j : Fin n) : StateM ℕ ℤ := do
  let x ← spend (read a i j) 2
  let same ← spend (decide (i = j)) 1
  let capped ← spend (min 0 x) 1
  let value ← spend (if same then capped else x) 1
  spend value 1

/-- The counter distinguishes the input reads, addition, comparison, choice, and output
write of a single relaxation. -/
private def relaxEntry {n : ℕ} (a : Table n) (k i j : Fin n) : StateM ℕ ℤ := do
  let direct ← spend (read a i j) 2
  let left ← spend (read a i k) 2
  let right ← spend (read a k j) 2
  let candidate ← spend (left + right) 1
  let short ← spend (decide (direct ≤ candidate)) 1
  let value ← spend (if short then direct else candidate) 1
  spend value 1

private theorem initEntry_eq {n} (a : Table n) (i j : Fin n) :
    initEntry a i j = spend (initial (read a) i j) 6 := by
  funext s
  change (if decide (i = j) = true then min 0 (read a i j) else read a i j, _) = _
  simp [initial, spend]

private theorem relaxEntry_eq {n} (a : Table n) (k i j : Fin n) :
    relaxEntry a k i j = spend (relax k (read a) i j) 10 := by
  funext s
  change (if decide (read a i j ≤ read a i k + read a k j) = true then _ else _, _) = _
  simp [relax, min_def, spend]

private def tabulateM {n : ℕ} (f : Fin n → Fin n → StateM ℕ ℤ) : StateM ℕ (Table n) :=
  Vector.ofFnM fun i => Vector.ofFnM (f i)

private theorem tabulateM_spend {n : ℕ} (d : Costs (Fin n)) (k : ℕ) :
    tabulateM (fun i j => spend (d i j) k) = spend (tabulate d) (n ^ 2 * k) := by
  simp [tabulateM, ofFnM_spend, tabulate, pow_two, Nat.mul_assoc]

private def primitiveRun {n : ℕ} : List (Fin n) → Table n → StateM ℕ (Table n)
  | [], a => pure a
  | k :: ks, a => do
    let next ← tabulateM (relaxEntry a k)
    primitiveRun ks next

private theorem primitiveRun_eq {n : ℕ} (ks : List (Fin n)) (a : Table n) :
    primitiveRun ks a = spend (run ks a) (ks.length * (n ^ 2 * 10)) := by
  induction ks generalizing a with
  | nil =>
    funext s
    simp [primitiveRun, run, spend]
    rfl
  | cons k ks ih =>
    have hr : relaxEntry a k = fun i j => spend (relax k (read a) i j) 10 :=
      funext fun i => funext fun j => relaxEntry_eq a k i j
    rw [primitiveRun, hr, tabulateM_spend]
    funext s
    change primitiveRun ks (tabulate (relax k (read a))) (s + n ^ 2 * 10) = _
    rw [ih]
    exact Prod.ext rfl (by change s + n ^ 2 * 10 + ks.length * (n ^ 2 * 10) =
      s + (ks.length + 1) * (n ^ 2 * 10); ring)

/-- Count actual scalar operations and table-element accesses in all matrix cells. -/
def primitiveCompute {n : ℕ} (a : Table n) : StateM ℕ (Table n) := do
  let initialTable ← tabulateM (initEntry a)
  primitiveRun (List.finRange n) initialTable

theorem primitiveCompute_correct {n : ℕ} (a : Table n) (s : ℕ) :
    (primitiveCompute a).run s = (compute (read a), s + 6 * n ^ 2 + 10 * n ^ 3) := by
  have hi : initEntry a = fun i j => spend (initial (read a) i j) 6 :=
    funext fun i => funext fun j => initEntry_eq a i j
  rw [primitiveCompute, hi, tabulateM_spend]
  change primitiveRun (List.finRange n) (tabulate (initial (read a))) (s + n ^ 2 * 6) = _
  rw [primitiveRun_eq]
  exact Prod.ext rfl (by simp [spend]; ring)

private theorem initial_magnitude_le {n : ℕ} (c : Costs (Fin n)) (B : ℕ)
    (h : ∀ i j, (c i j).natAbs ≤ B) (i j : Fin n) : (initial c i j).natAbs ≤ B := by
  by_cases hij : i = j
  · by_cases hc : 0 ≤ c i j
    · simp [initial, hij, hij ▸ hc]
    · simpa [initial, hij, min_eq_right (le_of_not_ge (hij ▸ hc))] using h i j
  · simpa [initial, hij] using h i j

theorem compute_magnitude_bits {n : ℕ} (c : Costs (Fin n)) (B : ℕ)
    (h : ∀ i j, (c i j).natAbs ≤ B) (i j : Fin n) :
    (read (compute c) i j).natAbs.size ≤ n + B.size := by
  simpa [compute_correct, distance] using
    sweep_magnitude_bits (List.finRange n) (initial c) B (initial_magnitude_le c B h) i j

end Paths
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
