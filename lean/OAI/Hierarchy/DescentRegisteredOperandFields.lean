import OAI.Hierarchy.DescentOperandStateBanks
import OAI.Hierarchy.DescentPackedNodeDigit

namespace OAI
/-! # The stored header indices and outgoing role word of an ordinary operand -/

namespace Hierarchy.DescentPriorOperandColumns
variable {slots : ℕ}

def headerIndex : Fin 4→Fin 10:=![0,2,3,4]
def sideIndex : Fin 6→Fin 10:=![1,5,6,7,8,9]

def pageOf (arg : Fin slots) (f : Fin 4) := DescentOperandStateBanks.page (Fin.castLE (by decide : 4≤7) f) arg

end Hierarchy.DescentPriorOperandColumns

namespace Hierarchy.DescentPackedRawTicket
open DescentSIMDLookup
variable {a H G : ℕ}

def payload (old role : Fin H→Fin G → Cell a) (fits : ∀h g,11*(old h g).val+(role h g).val<2^a) (h : Fin H) (g : Fin G) : Cell a :=
  ⟨11*(old h g).val+(role h g).val,fits h g⟩

end Hierarchy.DescentPackedRawTicket

end OAI
