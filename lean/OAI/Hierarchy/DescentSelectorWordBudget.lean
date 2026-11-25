import OAI.Hierarchy.DescentArgumentPageWordTariff

namespace OAI
/-! # Integer tariff for publishing one candidate selection per physical row -/
namespace Hierarchy.DescentDatedOperandSelectionRun

def readWork (C n u v : ℕ) := 1+C*(14+n*(u+11)+v+22)
def readFactor (K n C u v : ℕ) :=1024*(n+K+C+1)*(readWork C n u v+1)

/-- Charge the two immutable dictionaries once, and round each emitted group
column separately. The table charge is independent of the host population. -/
theorem read_budget (pages rows n K C T ks familyWords tables clock text : ℕ)
    (pre : familyWords≤(n+K)*(2*T)) (tab : tables≤(C+1)*(2*T))
    (time : clock≤(4+10*familyWords)+(4+10*tables+(4+pages*(4+rows*(2*ks+4)))))
    (code : text≤15*(familyWords+1)+(15*(tables+1)+(15+pages*(11+4*ks)))) :
    clock+7*text≤(1024*(n+K+C+1)*(ks+1))*((pages+1)*(1+rows)+(pages+1)*T) :=by
  refine (Nat.add_le_add time (Nat.mul_le_mul_left 7 code)).trans ?_
  calc
    _ ≤ (4+10*((n+K)*(2*T)))+(4+10*((C+1)*(2*T))+(4+pages*(4+rows*(2*ks+4))))+
        7*(15*((n+K)*(2*T)+1)+(15*((C+1)*(2*T)+1)+(15+pages*(11+4*ks)))) :=by gcongr
    _ ≤ _ :=by ring_nf;omega

end Hierarchy.DescentDatedOperandSelectionRun

end OAI
