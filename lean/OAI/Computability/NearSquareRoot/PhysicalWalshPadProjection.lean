import OAI.Computability.NearSquareRoot.PhysicalWalshPadding
import OAI.Computability.IntegerMultiplication.Grid.Value
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Coordinates and Euclidean error for padded spectator rows

Padding appends entire zero rows to the original prefix. Truncation reads the
same low ordinals after the computation. Each spectator transform acts within
one row, so the original result survives projection even if rounded operations
introduced error on the extra rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Padding

open IntegerMultiplication
open scoped BigOperators

variable {n m e R : ℕ}

/-- The prefix selected by the physical truncate command. -/
def project {α : Type*} (h : n ≤ m) (y : Fin m → α) : Fin n → α :=
  fun i => y (i.castLE h)

/-- Embed an array in a longer flat array with zeros at all new coordinates. -/
def extend {α : Type*} [Zero α] (m : ℕ) (x : Fin n → α) : Fin m → α :=
  fun i => if lo : i.val < n then x ⟨i.val, lo⟩ else 0

@[simp] theorem project_extend {α : Type*} [Zero α] (h : n ≤ m) (x : Fin n → α) :
    project h (extend m x) = x := by
  funext i
  simp [project, extend, i.isLt]

theorem extend_append {α : Type*} [Zero α] (x : Fin n → α) (e : ℕ) :
    extend (n+e) x = Fin.append x (fun _ : Fin e => 0) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [extend, j.isLt]
  · rw [Fin.append_right]; simp [extend, Fin.natAdd]

/-- The order and serialization coincide exactly with the actual padded tape. -/
theorem padded_ofFn {w : ℕ} (e : ℕ) (x : Fin n → Dusk.Grain w) :
    padded e (List.ofFn x) = (List.ofFn (extend (n+e) x)).map Dusk.mark := by
  simp [padded, extend_append, List.ofFn_fin_append, List.ofFn_const]

/-- Recover the original ordinal from an arbitrary padded output (also when
the output has nonzero entries on the extra rows). -/
theorem take_ofFn {α : Type*} (h : n ≤ m) (y : Fin m → α) :
    (List.ofFn y).take n = List.ofFn (project h y) := by
  apply List.ext_getElem
  · simp [min_eq_left h]
  · intro i h₁ h₂
    simp [project]

theorem meaning_zero (p w : ℕ) : Grid.meaning p w (0 : Dusk.Grain w) = 0 := by
  have f : Grid.focus w (0 : Grid.Cell) := by
    simp [Grid.focus, Grid.tiny]
  have e : Grid.aspect (0 : Dusk.Grain w) = 0 := by simpa using Grid.recovers _ f
  simp [Grid.meaning, e]

theorem meaning_extend {w : ℕ} (p : ℕ) (x : Fin n → Dusk.Grain w) (m : ℕ) :
    Grid.meaning p w ∘ extend m x = extend m (Grid.meaning p w ∘ x) := by
  funext i
  by_cases h : i.val < n <;> simp [extend, h, meaning_zero]

theorem norm_extend (n e : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖(WithLp.toLp 2 (extend (n+e) (fun i => x i)) : EuclideanSpace ℂ _)‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_add]
  simp [extend_append]

/-- Arbitrary prefix lengths contract the Euclidean norm, including the
case in which the prefix is empty. -/
theorem norm_project (h : n ≤ m) (y : EuclideanSpace ℂ (Fin m)) :
    ‖(WithLp.toLp 2 (project h (fun i => y i)) : EuclideanSpace ℂ _)‖ ≤ ‖y‖ := by
  classical
  let inc : Fin n ↪ Fin m := ⟨Fin.castLE h, fun a b hab => Fin.ext (congrArg (fun z : Fin m => z.val) hab)⟩
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  change (∑ i, ‖y (inc i)‖^2) ≤ ∑ i, ‖y i‖^2
  rw [← Finset.sum_map (Finset.univ : Finset (Fin n)) inc (fun j => ‖y j‖^2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)

theorem project_error (h : n ≤ m) (x y : EuclideanSpace ℂ (Fin m)) :
    ‖(WithLp.toLp 2 (project h (fun i => x i)) : EuclideanSpace ℂ _) -
      WithLp.toLp 2 (project h (fun i => y i))‖ ≤ ‖x-y‖ :=
  norm_project h (x-y)

/-- Apply the row transform independently at each physical spectator ordinal.
The last index (the selected coordinates) varies fastest. -/
def onRows {α β : Type*} (q : ℕ) (T : (Fin R → α) → Fin R → β)
    (x : Fin (q*R) → α) (i : Fin (q*R)) : β :=
  let t := finProdFinEquiv.symm i
  T (fun j => x (finProdFinEquiv (t.1,j))) t.2

theorem onRows_apply {α β : Type*} {q : ℕ} (T : (Fin R → α) → Fin R → β)
    (x : Fin (q*R) → α) (a : Fin q) (j : Fin R) :
    onRows q T x (finProdFinEquiv (a,j)) = T (fun b => x (finProdFinEquiv (a,b))) j := by
  simp [onRows]

private theorem growRow {q q' : ℕ} (h : q ≤ q') (a : Fin q) (j : Fin R) :
    (finProdFinEquiv (a,j)).castLE (Nat.mul_le_mul_right R h) = finProdFinEquiv (a.castLE h,j) :=
  Fin.ext rfl

/-- Cropping spectator rows commutes with any independent per-row transform. -/
theorem project_onRows {α β : Type*} {q q' : ℕ} (h : q ≤ q') (T : (Fin R → α) → Fin R → β)
    (y : Fin (q'*R) → α) :
    project (Nat.mul_le_mul_right R h) (onRows q' T y) =
      onRows q T (project (Nat.mul_le_mul_right R h) y) := by
  funext i
  obtain ⟨⟨a,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  simp only [project, onRows_apply, growRow (R := R) h]

/-- A full padded-array error guarantee for the stored row transform also
bounds the retained array against the ideal transform of its initial input. -/
theorem rows_error {q q' : ℕ} (h : q ≤ q') (T : (Fin R → ℂ) → Fin R → ℂ)
    (x : Fin (q*R) → ℂ) (y : EuclideanSpace ℂ (Fin (q'*R))) :
    ‖(WithLp.toLp 2 (project (Nat.mul_le_mul_right R h) (fun i => y i)) : EuclideanSpace ℂ _) -
      WithLp.toLp 2 (onRows q T x)‖ ≤
    ‖y - WithLp.toLp 2 (onRows q' T (extend (q'*R) x))‖ := by
  have b := project_error (Nat.mul_le_mul_right R h) y
    (WithLp.toLp 2 (onRows q' T (extend (q'*R) x)))
  have E := project_onRows h T (extend (q'*R) x)
  rw [project_extend] at E
  simpa only [← E] using b

end PhysicalWalsh.Padding

end NearSquareRoot
end Computability
end OAI
