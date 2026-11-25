import OAI.Computability.BorderVNP.CellProfileGenerator

/-! # Moving the selector test under a fresh candidate-count loop -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Every bit address, including those compared to a zero bit, shifts uniformly
when a word test is nested under one fresh lexical counter. -/
theorem weaken_wordIs (as : List NatExpr) (t : ℕ) :
    (wordIs as t).weaken = wordIs (as.map NatExpr.weaken) t := by
  induction as generalizing t with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,wordIs,Term.equal,Term.weaken,ih]

/-- The prefix-candidate loop uses the same physical bit addresses with the
enclosing copy variable shifted outward by one. -/
theorem Profile.weaken_selectTerm (off : ℕ) (p : Port) (w t : ℕ) (i : NatExpr) :
    (selectTerm off p w t i).weaken = selectTerm off p w t i.weaken := by
  unfold selectTerm
  rw [weaken_wordIs,List.map_map]
  rfl

end CellSparse

end BorderVNP
end Computability
end OAI
