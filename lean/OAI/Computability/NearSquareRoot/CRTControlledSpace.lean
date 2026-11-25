import OAI.Computability.NearSquareRoot.PrecisionGridPassSpace
import OAI.Computability.NearSquareRoot.BoundedProduct
import OAI.Computability.IntegerMultiplication.Code.List
import OAI.Computability.IntegerMultiplication.Code.Carry

/-! # Reusing workspace between independent controlled rows

The input forest contains consecutive complete rows, each with its own control data. While
one row is active, the output prefix and unread suffix are parked on the same fixed decks.
Consequently an ordinary time estimate for a single row suffices to bound all physical
stack heights, even if the sum of the row times exceeds stream volume.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Space
open IntegerMultiplication.Code.Task (forest)

private theorem reversedPrefix_count (output : ℕ → Tree) {a b : ℕ} (h : a ≤ b) :
    (forest output (List.range a).reverse).count ≤ (forest output (List.range b)).count := by
  rw [show b = a+(b-a) from by omega, List.range_add, Task.forest_count, Task.forest_count,
    List.length_reverse, List.length_append, costSum_cat]
  simp only [costSum, List.map_reverse, List.sum_reverse]
  omega

theorem physicalRows {X : Type*} (rows volume : X → ℕ) (input output : X → ℕ → Tree)
    (cost : X → ℕ → ℕ)
    (step : Code.Task (fun x : (i : X) × Fin (rows i) => cost x.1 x.2.val)
      (fun x => input x.1 x.2.val) (fun x => output x.1 x.2.val))
    (streamIn : ∀ x, (forest (input x) (List.range (rows x))).count ≤ volume x)
    (streamOut : ∀ x, (forest (output x) (List.range (rows x))).count ≤ volume x)
    (rowRoom : ∀ x j, j < rows x → (input x j).count + cost x j ≤ volume x) :
    BoundedTask (fun x => (∑ j ∈ Finset.range (rows x), (cost x j + (input x j).count + 1)) +
        2 * volume x + 2)
      (fun x => 2 * volume x + 3)
      (fun x => forest (input x) (List.range (rows x)))
      (fun x => forest (output x) (List.range (rows x))) := by
  let src := fun x => forest (input x) (List.range (rows x))
  let st := fun x j => forest (output x) (List.range j).reverse
  have start := BoundedTask.of_time
    ((Task.supply (.atom false) src).compose (Task.exchange (fun _ => .atom false) src))
  have localStep := (BoundedTask.of_time step).left fun x => st x.1 x.2.val
  let mem := fun x j => (input x j).count + cost x j + (st x j).count
  have pass := BoundedTask.indexedPasses rows input st cost mem (fun x => 2 * volume x)
    (localStep.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun x => by
      simp [st, List.range_succ]))
    (fun x => by have := streamIn x; omega)
    (fun x j hj => by have := (reversedPrefix_count (output x) hj).trans (streamOut x); dsimp [st]; omega)
    (fun x j hj => by
      have hp := (reversedPrefix_count (output x) hj.le).trans (streamOut x)
      have hr := rowRoom x j hj
      dsimp [mem, st]
      omega)
  have restore := BoundedTask.of_time ((Task.reversal (id : Tree → Tree)).on fun x =>
    ((List.range (rows x)).reverse).map (output x))
  have reorder : BoundedTask (fun x => (st x (rows x)).count)
      (fun x => (st x (rows x)).count + (st x (rows x)).count)
      (fun x => st x (rows x)) (fun x => forest (output x) (List.range (rows x))) :=
    restore.conform (fun x => by simp only [st, Task.forest_map, id_eq]) (fun x => by simp only [st, Task.forest_map, id_eq])
      (fun x => by simp only [st, Task.forest_map, id_eq]) (fun x => by simp only [← List.map_reverse, List.reverse_reverse, Task.forest_map, id_eq])
  have all := (start.compose pass).compose reorder
  apply all.mono
  · intro x
    have hi := streamIn x
    have ho := (reversedPrefix_count (output x) (le_refl (rows x))).trans (streamOut x)
    simp only [src, st, Tree.count]
    omega
  · intro x
    have hi := streamIn x
    have ho := (reversedPrefix_count (output x) (le_refl (rows x))).trans (streamOut x)
    simp only [src, st, Tree.count]
    omega

private theorem forestRange_count (f : ℕ → Tree) (n : ℕ) :
    (forest f (List.range n)).count = (∑ j ∈ Finset.range n, ((f j).count + 1)) + 1 := by
  induction n with
  | zero => simp [Task.forest_nil, Tree.count]
  | succ n ih =>
    rw [Task.forest_count, List.range_succ, List.length_append, costSum_cat,
      List.length_range, List.length_cons, List.length_nil, costSum_cons, costSum_nil,
      Finset.sum_range_succ]
    rw [Task.forest_count, List.length_range] at ih
    omega

/-- A row costing `width * rate` fits in the whole stream whenever the unchanged
prefix has at least `rate` distinct values. All physical tape rows, including their
headers and the output forest, are charged to volume. -/
theorem physicalRowsOfCarries {X : Type*} (rows width rate volume : X → ℕ)
    (input output : X → ℕ → Tree)
    (step : Carries (fun z : (x : X) × Fin (rows x) => ((width z.1 * rate z.1 : ℕ) : ℝ))
       (fun z => input z.1 z.2.val) (fun z => output z.1 z.2.val))
    (streamIn : ∀ x, (forest (input x) (List.range (rows x))).count ≤ volume x)
    (streamOut : ∀ x, (forest (output x) (List.range (rows x))).count ≤ volume x)
    (occupancy : ∀ x, rows x * width x ≤ volume x) (hprefix : ∀ x, rate x ≤ rows x) :
    BoundedTask (fun x => volume x * rate x + 5 * volume x + 2)
      (fun x => 4 * volume x + 3)
      (fun x => forest (input x) (List.range (rows x)))
      (fun x => forest (output x) (List.range (rows x))) := by
  obtain ⟨_, b, runner, K, hb⟩ := step.runs
  have run := runner.bound (K+1) (b' := fun z => width z.1 * rate z.1) (fun z => by
    have h := hb z
    change (b z : ℝ) + 1 ≤ (K : ℝ) * ((width z.1 * rate z.1 : ℕ) : ℝ) at h
    have v : b z + 1 ≤ K * (width z.1 * rate z.1) := by exact_mod_cast h
    nlinarith)
  have fit := physicalRows rows (fun x => 2*volume x) input output (fun x _ => width x * rate x)
    run (fun x => by have := streamIn x; omega) (fun x => by have := streamOut x; omega)
    (fun x j hj => by
      have v := streamIn x
      rw [forestRange_count] at v
      have row := Finset.single_le_sum (f := fun z => (input x z).count + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
      have clock : width x * rate x ≤ volume x := by
        rw [Nat.mul_comm]; exact (Nat.mul_le_mul_right _ (hprefix x)).trans (occupancy x)
      omega)
  apply fit.mono
  · intro x
    have hin := streamIn x
    rw [forestRange_count] at hin
    have eq : (∑ j ∈ Finset.range (rows x), (width x * rate x + (input x j).count + 1)) =
        rows x * width x * rate x + ∑ j ∈ Finset.range (rows x), ((input x j).count + 1) := by
      simp [Nat.add_assoc, Finset.sum_add_distrib, Nat.mul_assoc]
    rw [eq]
    have budget := Nat.mul_le_mul_right (rate x) (occupancy x)
    omega
  · intro x; omega

end Controlled

end NearSquareRoot
end Computability
end OAI
