import OAI.Computability.NearSquareRoot.KernelAutomatonSeries
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

/-! # Finite column series for a parity-indexed selector

A state records one bit per query. A matching pair of address columns updates the
bits simultaneously. The final state selects an exact coefficient from the table.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelAutomatonEquiv

open Matrix
open scoped Matrix

variable {X : Type*} [DecidableEq X] {q : ℕ}

private def encodeState (q : ℕ) : (Fin q → ZMod 2) ≃ Fin (2^q) :=
  finFunctionFinEquiv

private def nextMatrix (tests : X → Fin q → ZMod 2) (pair : X × X) :
    Matrix (Fin (2^q)) (Fin (2^q)) ℚ :=
  fun i j => if pair.1 = pair.2 ∧
    j = encodeState q ((encodeState q).symm i + tests pair.2) then 1 else 0

/-- A selector on whole addresses, with all exponent bits accumulated in a finite state. -/
def phaseSeries (tests : X → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → ℚ) :
    Series (X × X) where
  dim := 2^q
  initial i := if i = encodeState q 0 then 1 else 0
  letter := nextMatrix tests
  final i := table ((encodeState q).symm i)

private theorem phaseStep (tests : X → Fin q → ZMod 2)
    (a : X × X) (s : Fin q → ZMod 2) (v : Fin (2^q) → ℚ) :
    ((nextMatrix tests a) *ᵥ v) (encodeState q s) =
      if a.1 = a.2 then v (encodeState q (s + tests a.2)) else 0 := by
  by_cases h : a.1 = a.2 <;>
    simp [nextMatrix, mulVec, dotProduct, h, ite_mul]

private theorem phaseTail (tests : X → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → ℚ)
    (l : List (X × X)) (s : Fin q → ZMod 2) :
    (((l.map (nextMatrix tests)).prod) *ᵥ
      (fun i => table ((encodeState q).symm i))) (encodeState q s) =
      if l.map Prod.fst = l.map Prod.snd then table (s + (l.map (tests ∘ Prod.snd)).sum)
      else 0 := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, phaseStep, ih]
    have heads : (a :: l).map Prod.fst = (a :: l).map Prod.snd ↔
        a.1 = a.2 ∧ l.map Prod.fst = l.map Prod.snd := List.cons.injEq .. |>.to_iff
    by_cases h : a.1 = a.2
    · by_cases k : l.map Prod.fst = l.map Prod.snd
      · rw [ite_eq_left h, ite_eq_left k, ite_eq_left (heads.mpr ⟨h, k⟩)]
        simp [add_assoc]
      · rw [ite_eq_left h, ite_eq_right k, ite_eq_right (fun ht => k (heads.mp ht).2)]
    · rw [ite_eq_right h, ite_eq_right (fun ht => h (heads.mp ht).1)]

/-- All columns must agree, and a matching address selects the entry with exponent
tuple equal to its columnwise sum in the vector space over two elements. -/
theorem eval_phaseSeries (tests : X → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → ℚ)
    {n : ℕ} (y x : Fin n → X) :
    (phaseSeries tests table).eval (List.ofFn fun c => (y c, x c)) =
      if y = x then table (∑ c, tests (x c)) else 0 := by
  unfold Series.eval weight
  let l := List.ofFn fun c => (y c, x c)
  change (∑ i, (if i = encodeState q 0 then (1 : ℚ) else 0) *
    (((l.map (nextMatrix tests)).prod *ᵥ (fun j => table ((encodeState q).symm j))) i)) = _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [phaseTail]
  simp [l, List.map_ofFn, Function.comp_def, List.sum_ofFn]

end KernelAutomatonEquiv

end NearSquareRoot
end Computability
end OAI
