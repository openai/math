import OAI.ThreeFlat.Diagonal.TraceUniformBudget
import OAI.ThreeFlat.Diagonal.TracePairCost

namespace OAI
/-! # Explicit polynomial bound on the uniform physical step verifier -/

namespace ThreeFlat.Diagonal.TraceProgram

open TracePair TraceIssue

def uniformBudget (w p r k : ℕ) : ℕ :=
  pinBudget w p r k * ((3*p + 4*w + 2*r*w + p*w + 11)*portBudget w +
    4*(p*(instructionBudget w r + 3)+32)) + 4*controlBudget w p r k

theorem uniformPair_size_le (w p r k : ℕ) :
    (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).1 ≤ uniformBudget w p r k :=
  uniformPair_size_of packet_size_le checkPacket_size_le (port_card w p r).le

theorem instructionBudget_poly (w r : ℕ) : instructionBudget w r =
    2*(8+(w*10+1)+(r*((w*10+1)+1)+1)+2) + 2*((w+1)*10+1)+10 := rfl

/-- A univariate bound for families in which all four public parameters are bounded by N. -/
theorem uniformPair_size_of_le {w p r k N : ℕ}
    (hw : w ≤ N) (hp : p ≤ N) (hr : r ≤ N) (hk : k ≤ N) :
    (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).1 ≤ 10^20 * (N+1)^12 := by
  apply (uniformPair_size_le w p r k).trans
  have hm : uniformBudget w p r k ≤ uniformBudget N N N N := by
    simp only [uniformBudget,pinBudget,shapeBudget,portBudget,controlBudget,slotBudget,instructionBudget_poly]
    gcongr
  apply hm.trans
  simp only [uniformBudget,pinBudget,shapeBudget,portBudget,controlBudget,slotBudget,instructionBudget_poly]
  ring_nf
  omega

end ThreeFlat.Diagonal.TraceProgram

end OAI
