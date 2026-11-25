import Mathlib.Tactic

namespace OAI
/-! # The source and compact row counts of one venue quantity -/
namespace Hierarchy.DescentVenueQuantityPlanes
def rowCharge (B op oldRows newRows compact _raw directory pages table : ℕ) :=
  (115*B)*table+(2*B*op+4*B)*compact+284*B*newRows+115*directory+
    2048*pages+28*op+2048*newRows+2048*oldRows+3128

theorem charge_rows (B op oldRows newRows compact raw directory pages table : ℕ)
    (dir : directory≤4*B*compact+2*raw+3) :
    rowCharge B op oldRows newRows compact raw directory pages table≤
      (8192*(op+1)*(B+1))*(1+raw+oldRows+newRows+compact)+(115*B)*table+2048*pages := by
  let f:=8192*(op+1)*(B+1)
  have nonnegative : 0≤B*op := Nat.zero_le _
  have a : 3473+28*op≤f :=by unfold f;nlinarith
  have b : 230≤f :=by unfold f;nlinarith
  have c : 2048≤f :=by unfold f;nlinarith
  have d : 2048+284*B≤f :=by unfold f;nlinarith
  have e : 2*B*op+464*B≤f :=by unfold f;nlinarith
  have upper:=Nat.mul_le_mul_left 115 dir
  have rows:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add a (Nat.mul_le_mul_right raw b)) (Nat.mul_le_mul_right oldRows c))
    (Nat.mul_le_mul_right newRows d)) (Nat.mul_le_mul_right compact e)
  unfold rowCharge
  change _≤f*(1+raw+oldRows+newRows+compact)+(115*B)*table+2048*pages
  linear_combination rows + upper

end Hierarchy.DescentVenueQuantityPlanes

end OAI
