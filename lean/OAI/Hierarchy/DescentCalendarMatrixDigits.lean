import OAI.Hierarchy.DescentPackedFlowWalsh
import OAI.Hierarchy.DescentResetDigits

namespace OAI
/-! # The previous physical header and the reset share the same low-digit order -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentCompiler DescentColonies
noncomputable section

private theorem block_cast_val {a b : ℕ} (eqn : a=b) (x : Block a) :
    ((Equiv.cast (congrArg Block eqn)) x).val=x.val:=by
  cases eqn
  rfl

theorem calendar_digits (S : AtomSchedule) {k tail left right age : ℕ}
    (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (width : left+right=S.groupWidth k tail age+k)
    (sizes : 2^(left+right)=S.groupCount age*2^k) :
    digits (h:=left) (l:=right) (Equiv.refl (Fin (S.groupCount age))) sizes =
      (Equiv.cast (congrArg Block width)).trans (S.resetInputDigits base radix age):=by
  apply Equiv.ext
  intro x
  apply finProdFinEquiv.injective
  apply Fin.ext
  have source : (finProdFinEquiv (digits (h:=left) (l:=right)
      (Equiv.refl (Fin (S.groupCount age))) sizes x)).val=x.val:=by simp [digits,finCongr,Nat.mod_add_div]
  have target (y : Block (S.groupWidth k tail age+k)) :
      (finProdFinEquiv (S.resetInputDigits base radix age y)).val=y.val:=by
    simp [DescentCompiler.AtomSchedule.resetInputDigits,finCongr,Nat.mod_add_div]
  exact source.trans ((target _).trans (block_cast_val width x)).symm

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
