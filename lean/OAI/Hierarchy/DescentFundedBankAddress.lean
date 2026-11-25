import OAI.Hierarchy.DescentDatedOperandHeader

namespace OAI
/-! # Native funded bank from the previous stage's operand descriptor -/
namespace Hierarchy.DescentFundedCensus
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM

/-- Every published stage operand has a literal base. Extract the address from
the public expression so it can be passed to the retiling controller. -/
def priorBank (io : Dated.Operands) (x : ℕ) : Bank :=
  match io.atoms x with
  | .lookup page .row => page
  | _ => ⟨0,0⟩

/-- The address extraction is safe for every input expression accepted by the
previous stage. Its fixed default uses one word within the old hub page bound. -/
theorem priorBank_fits (io : Dated.Operands) (x : ℕ) {w floor : ℕ}
    (hubs : io.hubs.Fits w floor) (paid : (io.atoms x).Fits w floor) :
    (priorBank io x).Fits w floor:=by
  have spare : (⟨0,0⟩ : Bank).Fits w floor:=by
    obtain ⟨pos,word,space⟩:=hubs
    change 0<2^0 ∧ 2^0<2^w ∧ 0+2^0≤floor
    rw [pow_zero]
    omega
  unfold priorBank
  generalize name : io.atoms x = term at paid ⊢
  cases term with
  | row | lit | op | branch => exact spare
  | lookup B idx =>
    cases idx <;> first | exact paid.1 | exact spare


end Hierarchy.DescentFundedCensus

end OAI
