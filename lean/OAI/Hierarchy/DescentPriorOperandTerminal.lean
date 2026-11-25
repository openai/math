import OAI.Hierarchy.DescentOperandLaneRead
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentTerminalNodeDigit

namespace OAI
/-! # Literal two-level node-digit reads in the terminal pointer book -/
namespace Hierarchy.DescentTerminalPointerDigits.Widths
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem nodeDigit_stored {w H G M K a : ℕ} (s : Widths) (cap : s.nodeCapacity=some K)
    (B : Bank) (v : Fin H→Fin G→Cell (a*K)) (m : Memory w) (store : Reads B v M m)
    (wide : (a*K)*M≤w) (positive : 0<M) (host : Fin H) (group : Fin G) (j : Fin K) :
    s.nodeDigit a j.val (lane group positive).val
      (m (B.base+(row H G M (position host group positive)).val)).val=((encode a K).symm (v host group) j).val := by
  have h:=DescentOperandStateBanks.Reset.lane_read B.base v m store wide positive host group
  simp only [nodeDigit,cap,h]
  simpa only [Equiv.apply_symm_apply] using digit_encode ((encode a K).symm (v host group)) j

/-- A pointer header (including an exterior port/chunk) decoded at a genuinely
occupied node survives the terminal's read of that same physical address. -/
theorem nodeDigit_of_stored {w H G M K a : ℕ} (s : Widths) (cap : s.nodeCapacity=some K)
    (B : Bank) (v : Fin H→Fin G→Cell (a*K)) (m : Memory w) (store : Reads B v M m)
    (wide : (a*K)*M≤w) (positive : 0<M) (host : Fin H) (group : Fin G) (j : Fin K)
    (x : Cell a) (issued : (encode a K).symm (v host group) j=x) :
    s.nodeDigit a j.val (lane group positive).val
      (m (B.base+(row H G M (position host group positive)).val)).val=x.val :=
  (nodeDigit_stored s cap B v m store wide positive host group j).trans (congrArg Fin.val issued)

end
end Hierarchy.DescentTerminalPointerDigits.Widths

end OAI
