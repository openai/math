import OAI.ThreeFlat.Diagonal.ShrinkTable
import OAI.ThreeFlat.Diagonal.RefreshDemandChoice
import Mathlib.Data.List.OfFn

namespace OAI
/-! # The integer tile index in the RAM and the chosen six-party tensor have identical tie rules -/

namespace ThreeFlat.Diagonal.ShrinkMotif.Table

open MotifIntegerChoice
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

def row (T : Table F) : Fin (T.more.length+1) → T.Row := Fin.cases T.first T.more.get

theorem row_tail (T : Table F) : ((List.finRange T.more.length).map Fin.succ).map T.row = T.more := by
  rw [List.map_map,← List.ofFn_id,List.map_ofFn]
  exact List.ofFn_get _

private theorem best_ordinal {A B : Type} (f : A → B) (v : B → ℕ) (i : A) (xs : List A) :
    f (best (v ∘ f) i xs) = best v (f i) (xs.map f) := by
  induction xs generalizing i with
  | nil => rfl
  | cons j xs ih =>
    simp only [best,List.map_cons,Function.comp_apply]
    split_ifs <;> exact ih _

theorem row_chosen (T : Table F) (b : Fin 2 → ℕ) :
    T.row (RefreshDemandRows.tileNumber b (T.base ∘ T.row)) = best (score b T.base) T.first T.more := by
  change T.row (best ((score b T.base) ∘ T.row) _ _) = _
  rw [best_ordinal T.row (score b T.base),row_tail]
  rfl

end
end ThreeFlat.Diagonal.ShrinkMotif.Table

end OAI
