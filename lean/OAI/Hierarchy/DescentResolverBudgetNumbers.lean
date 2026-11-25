import OAI.Hierarchy.DescentDatedPriorOperand

namespace OAI
/-! Numerical clock and text of the seven-column ordinary operand resolver. -/
namespace Hierarchy.DescentDatedPriorOperand
namespace Layout

def pageFactor (l : Layout) := (l.jobs+1)*(l.columns+l.nodes+1)

theorem resolver_fee (l : Layout) (h : ℕ) (prior : ((l.size+2)*l.nodes)*l.lanes≤h/2)
    (splice : ((l.size+2)+(l.size+2))*l.lanes≤h/2) (lookup : (11*(l.size+2))*l.lanes≤h/2) :
    l.clockBudget+7*l.hardwareBudget≤16384*((l.pageFactor+1)*(1+l.rows)+(l.pageFactor+1)*2^(h/2)) :=by
  have dict : l.dictionary≤l.nodes*2^(h/2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) prior)
  have sl : l.splicePage≤2^(h/2) := Nat.pow_le_pow_right (by decide) splice
  have lut : l.resolverPage≤2^(h/2) := Nat.pow_le_pow_right (by decide) lookup
  unfold clockBudget clockPer hardwareBudget textPer
  calc
    _ ≤ l.jobs*(4+10*(l.nodes*2^(h/2))+(4+l.columns*(4+28*l.rows))+
      ((4+40*2^(h/2)+(4+2*(4+282*l.rows)))+(12+120*2^(h/2)+420*l.rows)))+4+
      7*(l.jobs*(15*(l.nodes*2^(h/2)+1)+(15+l.columns*(11+4*12))+
        (15*(4*2^(h/2)+1)+15+2*(11+4*139)+(841+15*(12*2^(h/2)+l.rows))))+15) :=by gcongr
    _ ≤ _ :=by
      unfold pageFactor
      ring_nf
      omega
end Layout

end Hierarchy.DescentDatedPriorOperand

end OAI
