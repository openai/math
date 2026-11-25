import OAI.Hierarchy.DescentExteriorCalendar
import OAI.Hierarchy.DescentTerminalPacketSlotRAM

namespace OAI
/-! # End-to-end bit charges for the native exterior ancestry, gather and relative-slot directory -/
namespace Hierarchy.DescentExteriorReplay
open DescentTerminalExteriorPackets DescentTerminalPacketSlotRAM ProtocolRAM
open scoped Classical

/-- `population` counts original external stacks. An ancestor represents a
whole residual group and a sorted row contains a whole physical cohort. -/
theorem directory_charge (hops : ℕ→Hop) (e stages h p₀ frozen retained rowCount j hosts factor : ℕ)
    (source : e=frozen*retained) (cohorts : e=rowCount*2^j)
    (ancestorRoom : 96*stages*h≤p₀*retained) (payload : h≤factor*p₀*2^j)
    (bank : Bank) :
    (clocks frozen (schedule hops stages)+(4+28*rowCount)+
        ((4+rowCount*(2*(guard bank hosts).work+4))+ProtocolRAMEndpointSort.cost rowCount hosts+(4+rowCount*80)))*h ≤
      (4*stages+39+18*hosts)*h+(1+175*factor)*(e*p₀) := by
  have clocks':=total_price frozen (schedule hops stages)
  have scheduleLength : (schedule hops stages).length = stages := by
    simp only [schedule,List.length_map,List.length_range]
  rw [scheduleLength] at clocks'
  have nativeFee:=DescentTerminalPacketSlotRAM.fee (n:=rowCount) (H:=hosts) bank
  have rows : rowCount*h≤factor*(e*p₀):=by
    simpa only [cohorts,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using Nat.mul_le_mul_left rowCount payload
  have ancestry : (96*stages*frozen)*h≤e*p₀:=by
    simpa only [source,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using Nat.mul_le_mul_left frozen ancestorRoom
  calc
    _ ≤ ((4*stages+39+18*hosts)+96*stages*frozen+175*rowCount)*h := by
      apply Nat.mul_le_mul_right
      have f : stages*(4+96*frozen)+4=4*stages+96*stages*frozen+4:=by ring
      omega
    _ = (4*stages+39+18*hosts)*h+(96*stages*frozen)*h+175*(rowCount*h) := by ring
    _ ≤ (4*stages+39+18*hosts)*h+e*p₀+175*(factor*(e*p₀)) := by omega
    _ = _ := by ring

end Hierarchy.DescentExteriorReplay

end OAI
