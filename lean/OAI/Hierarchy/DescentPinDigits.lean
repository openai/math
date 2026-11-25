import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentExteriorCoordinates

namespace OAI
/-! # Exact binary places of the physical group and port row -/

namespace Hierarchy.DescentSixParty.PinCohorts
open DescentCompiler DescentGL DescentColonies DescentExterior
noncomputable section
variable {S : AtomSchedule} {i k tail : ℕ}

/-- The group and block fields use the same binary places as the linear split. -/
theorem separate (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (group : Fin (S.groupCount i)) (block : Block k) :
    let bitsAt := fun (g : Fin (S.groupCount i)) (b : Block k) =>
      (address _).symm ((S.resetInputDigits base radix i).symm (g,b))
    let x:=splitRows (S.groupWidth k tail i) k (bitsAt group block)
    (address _ x.1).val=group.val ∧ address _ x.2=block := by
  intro bitsAt x
  have digits:=split_value (S.groupWidth k tail i) k (bitsAt group block)
  have full : (address _ (bitsAt group block)).val=
      block.val+2^k*group.val := by
    simp only [bitsAt,Equiv.apply_symm_apply]
    rfl
  rw [full] at digits
  have lo : (address k x.2).val<2^k := (address k x.2).isLt
  have oldlo : block.val<2^k := block.isLt
  change block.val+2^k*group.val=
    (address _ x.1).val*2^k+(address k x.2).val at digits
  rw [Nat.add_comm block.val, Nat.mul_comm (address _ x.1).val] at digits
  have quotient := congrArg (fun n:ℕ=>n / 2^k) digits
  have remnant := congrArg (fun n:ℕ=>n % 2^k) digits
  have pos : 0<2^k := by positivity
  simp only [Nat.mul_add_div pos,Nat.div_eq_of_lt oldlo,Nat.div_eq_of_lt lo,Nat.add_zero] at quotient
  simp only [Nat.mul_add_mod,Nat.mod_eq_of_lt oldlo,Nat.mod_eq_of_lt lo] at remnant
  exact ⟨quotient.symm,Fin.ext remnant.symm⟩

theorem cast_address {a b : ℕ} (h : a=b) (x : Bits a) :
    (address _ (castBits h x)).val=(address a x).val := by subst b; rfl

/-- Recombining the next-stage block and group gives the preceding group ordinal. -/
theorem group_address (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (age : i<S.length) (j : Fin (S.groupCount i)) :
    ((S.resetInputDigits base radix (i+1)).symm (S.groupDigits age radix j)).val=j.val := by
  simp only [AtomSchedule.resetInputDigits,AtomSchedule.groupDigits,Equiv.symm_trans_apply,
    Equiv.trans_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  rfl

end
end Hierarchy.DescentSixParty.PinCohorts

end OAI
