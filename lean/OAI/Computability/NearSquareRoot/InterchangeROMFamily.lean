import OAI.Computability.NearSquareRoot.InterchangeROMFrontNode
import OAI.Computability.NearSquareRoot.InterchangeTemplateSelect

/-! # The selected native interchange codes at every requested exponent -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFamily

open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Interchange
  InterchangeAddress InterchangeAddress.Request InterchangeROMFrame InterchangeROMRecursion
  CommonRegisters GeneratorSyntax

/-- Exponent index and lower bound on the radix. -/
abbrev Index := ℕ × ℕ

def selected (u : Index) := Template.Data.select u.1 u.2

theorem computable_selected : Computable selected := Template.Data.computable_select

abbrev valid (x : Template.Data) := Packed (b:=x.b) (@InterchangeROMFront.digit x.p)
abbrev Cases (x : Template.Data) (degree : ℕ) := ThickRequest (valid x) degree

/-- The physical run of a specified program and a specified numerical
template. The ground-field modulus is the actual selected prime. -/
def Executes (j : ℕ) (x : Template.Data) (degree : ℕ) (program : Cmd) : Prop :=
  Certified program
    (fun i : Cases x degree =>
      ⌈(i.val.recordVolume : ℝ)*(i.val.width : ℝ)^Generator.targetExponent j⌉₊)
    (fun i => i.val.recordVolume)
    (fun i => (job x.b).issue i.val) (fun i => (job x.b).reply i.val)

/-- Data consumed by the binary rectangular adapter. Both the register
cutoff and the record-padding degree are fixed across all selections. -/
structure NativeFamily where
  command : Index → Cmd
  registers : ℕ
  degree : ℕ
  effective : Effective ltr command
  within (u : Index) : Within registers (command u)
  run (u : Index) : Executes u.1 (selected u) degree (command u)

namespace NativeFamily

theorem geometry (u : Index) :
    (selected u).p.Prime ∧ 2 < (selected u).p ∧
    (selected u).b.Prime ∧ u.2 < (selected u).b := by
  have h := (Template.Data.selected_valid u.1 u.2).1
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

/-- Bind the proven joint selector to a concrete backend assembled over
numerical templates. Its center may refer back to the common caller. -/
def fromCenter (F : InterchangeROMFront.Core) (center : Template.Data → Cmd)
    (R degree : ℕ) (hc : Effective ltr center) (hw : ∀ x, Within R (center x))
    (runs : ∀ (j t : ℕ) (x : Template.Data), Template.Data.Valid j t x →
      Executes j x degree (controller F.cmd (center x) x.b (positions x.a x.m))) : NativeFamily where
  command u := let x := selected u; controller F.cmd (center x) x.b (positions x.a x.m)
  registers := max F.registers R
  degree := degree
  effective := by
    have num (i : ℕ) : Computable (fun u => (selected u).header i) :=
      (Template.Data.primrec_header i).to_comp.comp computable_selected
    exact effective_controller F.cmd (hc.comp computable_selected) (num 1)
      (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (num 3) (num 2)) (num 3))
  within u := node_within (F.pos.trans_le (le_max_left ..))
    (RegisterSelect.within_mono (le_max_left ..) _ F.cutoff)
    (RegisterSelect.within_mono (le_max_right ..) _ (hw (selected u)))
  run u := runs _ _ _ (Template.Data.selected_valid u.1 u.2)

end NativeFamily
end InterchangeROMFamily

end NearSquareRoot
end Computability
end OAI
