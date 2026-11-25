import OAI.Hierarchy.DescentDatedOperandTagRead
import OAI.Hierarchy.DescentCompactedOperandHeaders

namespace OAI
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentPriorOperandColumns
open scoped Classical Fin.CommRing
noncomputable section
variable {l : Layout}

theorem books_tags_iff (b : Books l) : BookTags b ↔
    ∀x j arg h g,(take j (b x (pageOf arg 0) h g)).val≤2 :=by
  constructor
  · intro known x j arg h g
    have valid:=known (l.index (x,j,arg)) h g
    simpa only [HeaderTag,booksHeader,Equiv.symm_apply_apply] using valid
  · intro known j h g
    exact known (l.index.symm j).1 (l.index.symm j).2.1 (l.index.symm j).2.2 h g

theorem kind_of_typed {b : ℕ} {r : Fin 4→Cell b} (ok : TypedHeader r) : (r 0).val≤2 :=by
  obtain ⟨p,source⟩:=ok
  rw [source 0]
  cases p with
  | privateWord _ => exact Nat.zero_le 2
  | cable _ _ _ => exact Nat.le_succ 1
  | pin _ _ => exact Nat.le_refl 2

end
end Hierarchy.DescentDatedPriorOperand

end OAI
