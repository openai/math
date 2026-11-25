import Mathlib.Tactic

namespace OAI
/-! # The native seed instruction and execution bill per initialized word -/
namespace Hierarchy.DescentSeedInitialTable

/-- Instructions and cycles for signed pages, stamped copy ordinals, native
operand sweeps and lookup directories. All arguments denote word counts. -/
theorem init_tariff (table plane sign peers args padding jobs batch directory height : ℕ)
    (pad : args ≤ padding) (positive : 0 < batch)
    (space : table+plane+sign+peers+padding+padding+jobs*batch+directory ≤ height) :
    let names:=(15*(table+1)+91)+
      (15*(sign+1)+15*(peers+1)+2*(15*(args+1))+15+jobs*71)+15*(directory+1)
    let ticks:=(8+10*table+44*plane)+
      ((4+10*sign+(4+10*peers)+(4+10*args))+(4+10*args+(4+jobs*(4+34*batch))))+
      (4+10*directory)
    ticks+7*names ≤ 1600*(height+1) := by
  have work : jobs≤jobs*batch:=Nat.le_mul_of_pos_right _ positive
  have repeated : jobs*(4+34*batch)=4*jobs+34*(jobs*batch) := by ring
  dsimp only
  rw [repeated]
  omega

end Hierarchy.DescentSeedInitialTable

end OAI
