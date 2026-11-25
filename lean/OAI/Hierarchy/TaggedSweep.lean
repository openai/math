import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace OAI
/-! # Observing finite rectangles in row-major order -/

namespace Hierarchy.Tagged.Radix
variable {α : Type*}

def sweep (n : ℕ) (f : Fin n → List α) : List α := (List.ofFn f).flatten

theorem sweep_eq_flatMap (n : ℕ) (f : Fin n → List α) : sweep n f = (List.ofFn id).flatMap f := by
  simp [sweep,List.flatMap_def,List.map_ofFn]

theorem sweep_extend {m n : ℕ} (size : m ≤ n) (x : Fin m → List α) (y : Fin n → List α)
    (keep : ∀ i : Fin m, y (i.castLE size) = x i) (empty : ∀ i : Fin n, m ≤ i.val → y i=[]) :
    sweep n y = sweep m x := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le size
  unfold sweep
  rw [List.ofFn_add,List.flatten_append]
  simp only [keep]
  have last : (fun i : Fin k => y (i.natAdd m)) = (fun _ => []) := funext fun i => empty _ (Nat.le_add_right ..)
  simp [last,List.ofFn_const]

theorem sweep_rect {m n : ℕ} (x : Fin (m*n) → List α) :
    sweep (m*n) x = sweep m (fun b => sweep n (fun i => x (finProdFinEquiv (b,i)))) := by
  unfold sweep
  rw [List.ofFn_mul,List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg x
  apply Fin.ext
  change b.val*n+i.val = i.val+n*b.val
  ac_rfl

end Hierarchy.Tagged.Radix

end OAI
