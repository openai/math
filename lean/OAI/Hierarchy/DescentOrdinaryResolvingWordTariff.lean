import OAI.Hierarchy.DescentResolverBudgetNumbers
import OAI.Hierarchy.DescentDatedOperandProgram
import OAI.Hierarchy.DescentArgumentPageWordTariff

namespace OAI
/-! # The original seven-column resolver at the density of its actual incoming words -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentStaticWordColumn DescentDatedSeedStartup
noncomputable section
theorem Banks.word_bill {l : Layout} (t : Banks l) (floor w h ratio unit : ℕ) (bus : w≤ratio*h)
    (fill : h≤l.lanes*unit) (prior : ((l.size+2)*l.nodes)*l.lanes≤h/2)
    (splice : ((l.size+2)+(l.size+2))*l.lanes≤h/2) (lookup : (11*(l.size+2))*l.lanes≤h/2) :
    (t.ticks floor+7*names (t.program w floor))*w≤
      16384*ratio*(l.pageFactor+1)*(h+l.hosts*h+l.hosts*l.groups*unit)+
      16384*ratio*(l.pageFactor+1)*2^(h/2)*h :=by
  obtain ⟨ticks,code⟩:=t.priced w floor
  exact page_scan_words l.hosts l.groups l.lanes unit h w ratio l.pageFactor 16384 _ fill bus
    ((Nat.add_le_add ticks (Nat.mul_le_mul_left 7 code)).trans (l.resolver_fee h prior splice lookup))
end
end Hierarchy.DescentDatedPriorOperand

end OAI
