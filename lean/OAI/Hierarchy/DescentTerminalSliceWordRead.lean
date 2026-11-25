import OAI.Hierarchy.DescentTerminalSliceRaw
import OAI.Hierarchy.DescentTerminalPointerPages
import OAI.Hierarchy.DescentPriorOperandTerminal
import OAI.Hierarchy.DescentTerminalWholeRows

namespace OAI
/-! Literal RAM readback of the two indices of a packed primitive word. -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentTerminalPointerDigits DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {L d H blocks w:ℕ} (chart : Fin L→Fin blocks→Gather.Address)
def seen (m:Memory w) (x:Fin blocks) (h:Fin H) (j:Fin L) : Cell d :=
  ((m ((chart j x).atHost h)).val:ℕ)
end
end Hierarchy.DescentTerminalSliceShelf

namespace Hierarchy.DescentTerminalSliceRuns
open DescentTerminalPointerDigits DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
/-- A tracked value may occupy only the low d bits of the physical word. Each
of the nested group and node digits agrees with the genuine previous RAM
publication, even if the high bits of other proposed inputs are arbitrary. -/
theorem stored_lane {H n groups bits d w:ℕ} (b:Bank) (values:Fin H→Fin groups→Cell (bits*n))
    (m:Memory w) (source:Reads b values groups m) (wide:bits*n*groups≤w) (small:bits*n*groups≤d)
    (h:Fin H) (g:Fin groups) (u:Fin n) :
    laneField bits g u ((m (b.base+h.val)).val:Cell d)=((encode bits n).symm (values h g) u).val := by
  let fmt:Widths:=⟨0,0,fun _=>bits,some n⟩
  have pos:=Nat.zero_lt_of_lt g.isLt
  have place:=Gather.at_whole groups pos h g
  have read:=fmt.nodeDigit_stored rfl b values m source wide pos h g u
  rw [place.1,place.2] at read
  change digit bits u.val (digit (bits*n) g.val _) = _ at read
  change digit bits u.val (digit (bits*n) g.val ((m (b.base+h.val)).val%2^d))=_
  have cut:(bits*n)*(g.val+1)≤d:=(Nat.mul_le_mul_left _ g.isLt).trans small
  unfold digit at read ⊢
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow _ cut)]
  exact read

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
