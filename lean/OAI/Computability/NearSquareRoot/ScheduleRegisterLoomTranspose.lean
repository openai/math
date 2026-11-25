import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSeries

/-!
# A three-register compiler for P192's narrow transpose

The finite number of fields determines the compiled sequence of scans. The
record dimension is a runtime input. The live data bound contains a single
input matrix, a single output matrix, and fixed multiples of one scan's
working volume. No charge for the number of scans enters the space bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

private theorem sum_add {K : Type} (a b : K → ℕ) (l : List K) :
    costSum (fun k => a k + b k) l = costSum a l + costSum b l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [costSum_cons, ih]; omega

private theorem sum_const {K : Type} (a : ℕ) (l : List K) :
    costSum (fun _ => a) l = l.length * a := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem sum_swap {K A : Type} (f : A → K → ℕ) (rows : List A) (cols : List K) :
    costSum (fun a => costSum (f a) cols) rows =
      costSum (fun k => costSum (fun a => f a k) rows) cols := by
  induction rows with
  | nil => simp only [costSum_nil, sum_const, Nat.mul_zero]
  | cons a rows ih =>
    simp only [costSum_cons]
    rw [sum_add, ih]

private theorem sum_forest {K A : Type} (v : A → K → Tree) (rows : List A) (cols : List K) :
    costSum (fun a => (Task.forest (v a) cols).count) rows =
      rows.length * (cols.length + 1) + costSum (fun a => costSum (fun k => (v a k).count) cols) rows := by
  induction rows with
  | nil => simp
  | cons a rows ih =>
    rw [costSum_cons, costSum_cons, ih, List.length_cons, Nat.succ_mul, Task.forest_count]
    omega

/-- The only volume difference between a forest matrix and its transpose comes from
the two forest constructors per outer row. This also covers empty dimensions. -/
theorem forest_transpose_volume {K A : Type} (cols : List K) (rows : List A) (v : A → K → Tree) :
    (Task.forest (fun k => Task.forest (fun a => v a k) rows) cols).count + 2 * rows.length =
      (Task.forest (fun a => Task.forest (v a) cols) rows).count + 2 * cols.length := by
  rw [Task.forest_count, Task.forest_count]
  rw [sum_forest, sum_forest, sum_swap (fun k a => (v a k).count)]
  ring

theorem transpose_volume {K A : Type} (cols : Series K) (rows : Series A) (v : A → K → Tree) :
    (stripe cols (fun k => stripe rows (fun a => v a k))).count + 2 * rows.count =
      (stripe rows (stripe cols ∘ v)).count + 2 * cols.count := by
  simpa only [Function.comp_def, stripe_simple, Series.count] using
    forest_transpose_volume cols.explore rows.explore v

/-- Extract each field from the same matrix and retain its column in output order. -/
def transposeCommand {K : Type} [DecidableEq K] (cols : Series K) : Cmd :=
  seriesCommand (fun k => columnCommand (cols.explore.idxOf k)) cols.explore

theorem transpose_within {K : Type} [DecidableEq K] (cols : Series K) :
    Within 3 (transposeCommand cols) :=
  series_within (le_refl 3) _ _ (fun _ => column_within _)

/-- A uniform narrow transpose for raw serialized P192 matrices. A pass
per output field keeps its clock linear for each fixed finite field layout.
All layouts use the same three data registers and the same space constants. -/
theorem transpose_bounded {K A : Type} [DecidableEq K] (cols : Series K) (rows : Series A)
    (v : A → K → Tree) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let src := stripe rows (stripe cols ∘ v)
    let dst := stripe cols (fun k => stripe rows (fun a => v a k))
    BoundedFits env (transposeCommand cols) (pile 0 src r) (pile 0 dst r)
      (250 * (cols.count + 1) * (src.count + 1))
      (base + 253 * src.count + 2 * cols.count + 10) (252 * src.count + 10) := by
  let src := stripe rows (stripe cols ∘ v)
  let dst := stripe cols (fun k => stripe rows (fun a => v a k))
  have volume := transpose_volume cols rows v
  change dst.count + _ = src.count + _ at volume
  have run := series_bounded (fun k => columnCommand (cols.explore.idxOf k)) src
    (fun k => stripe rows (fun a => v a k)) (fun _ => 191 * src.count) (192 * src.count)
    (fun k env r base h =>
      (column_bounded cols rows v k env r base h).mono le_rfl le_rfl (by dsimp [src]; omega))
    cols.explore env r base hr
  rw [← stripe_simple] at run
  apply run.mono
  · change seriesClock src.count (fun _ => 191 * src.count) cols.explore ≤
      250 * (cols.count + 1) * (src.count + 1)
    simp only [seriesClock, sum_const, Series.count]
    ring_nf
    omega
  · change base + 60 * src.count + dst.count + 192 * src.count + 10 ≤
      base + 253 * src.count + 2 * cols.count + 10
    omega
  · change 60 * src.count + 192 * src.count + 10 ≤ 252 * src.count + 10
    omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
