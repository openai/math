import OAI.Hierarchy.DescentDateBillVolume
import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # Paying a full half-word matching dictionary with the current physical host population -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentCompiler.TerminalScale

theorem volume_invoice {homes groups h unit weight radix : ℕ} (live : 0<homes)
    (page : 2^(h/2)≤homes) (radixPos : 0<radix) :
    weight*volumeBits (hostRows homes) groups h unit ≤
      homes*h*(4*weight)+homes*(groups*radix)*(8*weight*unit) := by
  have hosts := hostRows_double live
  have basic : h≤homes*h := Nat.le_mul_of_pos_left h live
  have pad := Nat.mul_le_mul_right h hosts
  have shared := Nat.mul_le_mul_right h page
  have records := Nat.mul_le_mul_right unit (Nat.mul_le_mul_right groups hosts)
  have scaleGroups : homes*groups*unit≤homes*(groups*radix)*unit := by
    gcongr
    exact Nat.le_mul_of_pos_right _ radixPos
  have summed : volumeBits (hostRows homes) groups h unit ≤
      4*(homes*h)+8*(homes*(groups*radix)*unit) := by
    unfold volumeBits
    nlinarith only [basic,pad,shared,records,scaleGroups]
  calc
    _ ≤ weight*(4*(homes*h)+8*(homes*(groups*radix)*unit)) := Nat.mul_le_mul_left _ summed
    _ = _ := by ring

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
