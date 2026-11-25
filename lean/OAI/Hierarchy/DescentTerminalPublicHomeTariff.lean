import OAI.Hierarchy.DescentTerminalPacketHomeInstall

namespace OAI
/-! # Charging the expanded public hosts against the terminal public-row allocation -/
namespace Hierarchy.DescentTerminalPacketHomeRAM.Expansion
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

/-- For this bound the program is the genuinely fixed literal calendar
followed by two indirect reads. The argument establishing the frozen-height
range only identifies its word values and changes no instruction. -/
theorem fixed_tariff (w base E j rest kept : ℕ) (frozen:Bank) (lower:j≤kept) (upper:kept≤j+(j+rest)) :
    names (fixedProgram w base E j rest kept frozen)+(8+38*(E*2^(j+rest)))=
      53*(E*2^(j+rest))+82 := by
  rw [fixed_code w base frozen (calendarIndex E j rest kept lower upper) (calendarIndex_val E j rest kept lower upper)]
  exact tariff base frozen _

/-- A terminal invoice already paying every public row also covers this extra
scalar pass. The since-installed lookup columns are shared by all later uses. -/
theorem add_to_price (w base E j rest kept : ℕ) (frozen : Bank)
    (lower:j≤kept) (upper:kept≤j+(j+rest)) (body:Procedure w) (clock budget scale : ℕ)
    (billed : (names body+clock)*(w+1)≤ scale*budget)
    (publicPart : (E*2^(j+rest)+1)*(w+1)≤budget) :
    (names ((fixedProgram w base E j rest kept frozen).seq body)+
      (8+38*(E*2^(j+rest))+clock))*(w+1)≤(scale+82)*budget := by
  have component := fixed_tariff w base E j rest kept frozen lower upper
  have smaller : 53*(E*2^(j+rest))+82 ≤ 82*(E*2^(j+rest)+1) := by omega
  have paid := Nat.mul_le_mul_left 82 publicPart
  calc
    _ = (names (fixedProgram w base E j rest kept frozen)+(8+38*(E*2^(j+rest))))*(w+1)+
        (names body+clock)*(w+1) := by rw [names_seq];ring
    _ ≤ 82*(E*2^(j+rest)+1)*(w+1)+scale*budget := by
      rw [component];exact Nat.add_le_add (Nat.mul_le_mul_right _ smaller) billed
    _ = 82*((E*2^(j+rest)+1)*(w+1))+scale*budget :=
      congrArg (fun n => n+scale*budget) (Nat.mul_assoc 82 (E*2^(j+rest)+1) (w+1))
    _ ≤ 82*budget+scale*budget := Nat.add_le_add paid (Nat.le_refl _)
    _ = (scale+82)*budget := by ring

end
end Hierarchy.DescentTerminalPacketHomeRAM.Expansion

end OAI
