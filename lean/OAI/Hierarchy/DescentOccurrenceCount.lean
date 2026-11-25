import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI
/-! # Cardinalities of sets of named occurrences -/

namespace Hierarchy.DescentOldOccurrenceRAM
open scoped BigOperators Classical
noncomputable section

def count {I : Type*} [Fintype I] (p : I → Prop) : ℕ := (Finset.univ.filter p).card

theorem count_eq_sum {I : Type*} [Fintype I] (p : I → Prop) :
    count p = ∑ i, if p i then 1 else 0 := Finset.card_filter p Finset.univ

theorem count_congr {I : Type*} [Fintype I] {p q : I → Prop} (h : ∀i,p i ↔ q i) :
    count p=count q := congrArg count (funext (fun i=>propext (h i)))

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
