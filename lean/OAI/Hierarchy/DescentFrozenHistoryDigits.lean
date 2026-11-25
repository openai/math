import OAI.Hierarchy.DescentExteriorSpine
import OAI.Hierarchy.DescentExteriorCoordinates

namespace OAI
/-! # Fixed bit positions for replaying the chosen history over a frozen address -/

namespace Hierarchy.DescentExterior.Spine
open DescentGL DescentColonies
noncomputable section
variable {E A B C : Type} {a b c f g : ℕ} {initial : E→Bits a} {middle : E→Bits b} {last : E→Bits c}
  {one:E→A} {two:E→B} {three:E→C}
  (x : Spine initial middle one two f) (y : Spine middle last two three g)

theorem frozen_append (e : E) :
    (address (g+f) ((x.append y).cut (initial e)).2).val =
      (address g (y.cut (middle e)).2).val*2^f+(address f (x.cut (initial e)).2).val := by
  let v:=(splitRows g f).symm ((y.cut (x.cut (initial e)).1).2,(x.cut (initial e)).2)
  change (address (g+f) v).val=_
  have h:=split_value g f v
  simpa only [v,LinearEquiv.apply_symm_apply,x.active_eq] using h

theorem newest (e : E) :
    (address (g+f) ((x.append y).cut (initial e)).2).val/2^f=
      (address g (y.cut (middle e)).2).val := by
  rw [frozen_append,Nat.mul_comm (address g (y.cut (middle e)).2).val (2^f),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt (address f (x.cut (initial e)).2).isLt,Nat.add_zero]

theorem earlier (e : E) :
    (address (g+f) ((x.append y).cut (initial e)).2).val%2^f=
      (address f (x.cut (initial e)).2).val := by
  rw [frozen_append,Nat.mul_add_mod_of_lt (address f (x.cut (initial e)).2).isLt]

end
end Hierarchy.DescentExterior.Spine

end OAI
