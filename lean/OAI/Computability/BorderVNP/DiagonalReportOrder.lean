import OAI.Computability.BorderVNP.RoutingISATypedTaskOwnership

/-! # The native report row order is the filtered list of global cell numbers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

variable (l : Layout) (mem : ℕ → ℕ)

/-- At each global cursor the compact rows already filled are exactly the
owned cells below that cursor, in increasing order. -/
theorem globalCell_prefix (c : ℕ) (hc : c ≤ l.cells) :
    (List.ofFn fun i : Fin (l.before mem c) => globalCell l mem i.val) =
      (List.range c).filter fun a => decide (l.owner mem a=l.team) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have before := ih (Nat.le_of_succ_le hc)
    rw [List.range_succ,List.filter_append]
    by_cases owned : l.owner mem c=l.team
    · have extend : l.before mem (c+1)=l.before mem c+1 := by simp only [Layout.before,ite_eq_left owned]
      simp only [extend,List.ofFn_succ',Fin.val_cast,Fin.val_castSucc,Fin.val_last,List.concat_eq_append]
      rw [before,global_at l mem hc owned]
      simp [owned]
    · simp [Layout.before,owned,before]

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
