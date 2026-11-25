import OAI.Computability.BorderVNP.ParseBatchVerifierConjunction
import OAI.Computability.BorderVNP.ParseBatchSortCompare
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange

/-! # First minimizing child in a batch of unsigned exact scores -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckChoice

open VPVNP.VerifierNetwork ParseBatchVerifier ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {m w : ℕ}

/-- Earlier candidates must be strictly more expensive. Later candidates may tie. -/
def wins (i : Fin m) : Expr (Fin m × Fin w) := every (fun j : Fin m =>
  if j < i then .not (leExpr (fun k => (j,k)) (fun k => (i,k)))
  else leExpr (fun k => (i,k)) (fun k => (j,k)))

/-- One-hot first-minimum selector with the original list order for ties. -/
noncomputable def firstMin (m w : ℕ) : Frame (Fin m × Fin w) (Fin m) :=
  (Frame.initial id).step wins

theorem firstMin_size (m w : ℕ) : (firstMin m w).size ≤ m * ((15*w+3)*m+1) := by
  apply (Frame.step_size_le _ _ ((15*w+3)*m+1) ?_).trans (by simp)
  intro i
  apply every_size _ (15*w+2)
  intro j
  split <;> simp [StatementCircuit.Expr.size, leExpr_size]

/-- The selector agrees with the manuscript's first-minimum list routine, including ties. -/
theorem firstMin_eval (z : Fin m × Fin w → Bool) (i : Fin m) :
    (firstMin m w).eval z i = true ↔ (List.finRange m).argmin (fun l => value (fun d => z (l,d))) = some i := by
  let f (j : Fin m) := value (fun d => z (j,d))
  have hi : (Frame.initial (id : Fin m × Fin w → _)).eval z = z := funext (Frame.initial_eval id z)
  have check (j : Fin m) :
      ((if j < i then StatementCircuit.Expr.not (leExpr (fun d : Fin w => (j,d)) (fun d => (i,d)))
        else leExpr (fun d => (i,d)) (fun d => (j,d)))).eval z = true ↔
      if j < i then f i < f j else f i ≤ f j := by
    by_cases h : j < i <;> simp [h, StatementCircuit.Expr.eval, leExpr_eval, f, Function.comp_def]
  simp only [firstMin, Frame.step_eval, hi, wins, every_eval, check, List.argmin_eq_some_iff,
    List.mem_finRange, true_and, true_implies, List.idxOf_finRange]
  change (∀ j, if j < i then f i < f j else f i ≤ f j) ↔
    (∀ j, f i ≤ f j) ∧ ∀ j, f j ≤ f i → i.val ≤ j.val
  constructor
  · intro h
    constructor
    · intro j
      by_cases hji : j < i
      · exact (show f i < f j by simpa [hji] using h j).le
      · simpa [hji] using h j
    · intro j hj
      by_contra! hji
      have hlt : j < i := hji
      exact (not_lt_of_ge hj) (by simpa [hlt] using h j)
  · rintro ⟨hm,ht⟩ j
    by_cases hji : j < i
    · rw [ite_eq_left hji]
      exact lt_of_not_ge (fun h => hji.not_ge (ht j h))
    · simpa [hji] using hm j

/-- Applying a function to an ordered child list commutes with choosing its minimum,
when the compared scores are transported exactly. -/
theorem argmin_map {T S : Type*} [LinearOrder S] (g : Fin m → T) (s : T → S) :
    (List.ofFn g).argmin s = ((List.finRange m).argmin (s ∘ g)).map g := by
  have aux (l : List (Fin m)) : (l.map g).argmin s = (l.argmin (s ∘ g)).map g := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.argmin_cons, ih, List.argmin_cons]
      cases l.argmin (s ∘ g) with
      | none => rfl
      | some b =>
        simp only [Option.map_some, Function.comp_apply]
        split <;> rfl
  simpa [List.finRange, List.map_ofFn, Function.comp_def] using aux (List.finRange m)

/-- Identical weak orders, including ties, give the same first list minimum. -/
theorem argmin_congr {T R S : Type*} [LinearOrder R] [LinearOrder S]
    (a : T → R) (b : T → S) (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j) (l : List T) :
    l.argmin a = l.argmin b := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [List.argmin_cons, List.argmin_cons, ih]
    cases l.argmin b with
    | none => rfl
    | some j =>
      change (if a j < a v then some j else some v) = if b j < b v then some j else some v
      have hlt : a j < a v ↔ b j < b v := by simpa only [not_le] using (h v j).not
      simp only [hlt]

end PackedDeckChoice

end BorderVNP
end Computability
end OAI
