import OAI.Hierarchy.DescentOrdinaryBornDigits
import OAI.Hierarchy.DescentCompactedOperandHeaders

namespace OAI
/-! # The temporary four header columns of each newly emitted ordinary operand -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentSIMDLookup DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section

/-- A padded row is the zero pointer. A present row stores its original aligned
chunk at the width of the dated registers. -/
theorem component_header (size : ℕ) (mouth_ : Option Mouth) :
    TypedHeader (fun f=>component (size+2) mouth_ (f.castLE (by decide : 4≤7))) :=by
  cases mouth_ with
  | none =>
    apply typed_zero
  | some item =>
    refine ⟨.cable 0 0 ((item.chunk:Cell (size+2))).val,?_⟩
    intro f
    have one : 1<2^(size+2):=by
      exact (by decide : 1<2^2).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left 2 size))
    fin_cases f <;> simp [component,Pointer.fields,Pointer.header,Fin.val_natCast,Nat.mod_eq_of_lt one]

end
end Hierarchy.DescentOrdinaryBorn

end OAI
