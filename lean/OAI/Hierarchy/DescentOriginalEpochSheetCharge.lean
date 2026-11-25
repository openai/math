import OAI.Hierarchy.DescentTerminalObservationPrefix
import OAI.Hierarchy.DescentWideSeedCalendarFee
import OAI.Hierarchy.DescentEpochAdviceLayoutNumbers
import OAI.Hierarchy.DescentPackedEpochShelfLayout

namespace OAI
/-! # Measured cardinalities of the original profile rows and their decision dictionary -/
namespace Hierarchy
open DescentSIMDLookup DescentPackedProfileTape DescentTerminalEpochChart DescentTerminalEpochDecoder
open scoped Classical BigOperators
noncomputable section
namespace DescentPackedProfileValidity
theorem tariff_le (C grain : ℕ) :
    tariff C grain ≤ 2^((DescentTerminalEpochBits.width C+1)*grain) := by
  have small : grain+1 ≤ 2^grain:=Nat.lt_two_pow_self (n:=grain)
  unfold tariff bankShift
  calc
    _ ≤ 2^grain*2^(DescentTerminalEpochBits.width C*grain) := Nat.mul_le_mul_right _ small
    _ = _ := by rw [←pow_add];congr 1; ring

end DescentPackedProfileValidity
namespace DescentPackedProfileInstall
open DescentPackedProfileValidity
theorem extent (lo C grain : ℕ) :
    end_ lo C grain ≤ lo+(2*(grain+1)+1)+(2*2^((DescentTerminalEpochBits.width C+1)*grain)+1) := by
  have shift:=DescentDyadicSpan.span_le (grain+1)
  have dict_:=DescentDyadicSpan.span_le (tariff C grain)
  have total:=tariff_le C grain
  change lo+DescentDyadicSpan.span (grain+1)+DescentDyadicSpan.span (tariff C grain) ≤ _
  omega

end DescentPackedProfileInstall
namespace DescentPackedEpochShelves
variable {A : Type}
theorem chunk_charge (w C n : ℕ) (wide : 2*unit C ≤ w) :
    slots n (grain w C)*w ≤ 2*w+4*n*unit C := by
  let R:=grain w C
  obtain ⟨_,bound⟩:=occupancy w (unit C) (Nat.zero_lt_succ _) wide
  have le : n/R*R ≤ n:=Nat.div_mul_le_self ..
  have mul:=Nat.mul_le_mul_left (n/R) bound
  have room:=Nat.mul_le_mul_right (unit C) (Nat.mul_le_mul_left 4 le)
  change (n/R+2)*w ≤ _
  change n/R*w ≤ n/R*(4*R*unit C) at mul
  rw [Nat.add_mul]
  nlinarith only [mul,room]

theorem chunks_charge (w C : ℕ) (ss : List (Source A)) (wide : 2*unit C ≤ w) :
    (ss.map fun s=>slots s.seats (grain w C)).sum*w ≤ 2*ss.length*w+4*seatBill ss*unit C := by
  induction ss with
  | nil=>simp [seatBill]
  | cons s ss ih=>
    have paid:=chunk_charge w C s.seats wide
    change (slots s.seats (grain w C)+(ss.map _).sum)*w ≤ 2*(ss.length+1)*w+4*(s.seats+seatBill ss)*unit C
    rw [Nat.add_mul]
    nlinarith only [paid,ih]

end DescentPackedEpochShelves
end
end Hierarchy

end OAI
