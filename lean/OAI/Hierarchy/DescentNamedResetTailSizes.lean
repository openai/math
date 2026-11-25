import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentPhysicalResetTailTariff

namespace OAI
/-! All lane and block counts of the named reset tail are strictly positive. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base : ℕ)
local notation "head_" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base


theorem tail_sizes (prior : 0<old.venue.lanes) (roles : 0<old.primitiveLanes)
    (current : 0<M) (following : 0<nextM) : PhysicalReset.FinalInputs.TailSizes head_:=by
  let r := (head_).roleTransfer.transfer
  have high : r.high ≤ r.cut := Nat.sub_le ..
  have matrix : 0<r.matrixLanes := Nat.div_pos
    (Nat.pow_le_pow_right (by decide) (show r.high+r.low-r.cut≤r.low by omega)) (Nat.two_pow_pos _)
  constructor <;> first | exact current | exact following | exact prior | exact roles | exact matrix | exact Nat.two_pow_pos _

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
