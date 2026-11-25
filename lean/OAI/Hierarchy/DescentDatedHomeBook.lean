import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentRetainedPhysicalTarget

namespace OAI
/-! # The numerical prior-home key used by the physical reset role mover -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentResetActorClass DescentDatedAddressBook.ActorSetup DescentDenseHostOrder
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 6000
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "r" => a.successor.middle.rootDepth
local notation "move" => a.successor.roleTransfer

theorem which_book (j : Fin (move).shapes) :
    z.which j=targetBook u.atlas.board r u.roots.Ht ((j.cast z.primaryRanks).cast u.menu.nodes):=by
  unfold which OperandMenu.target targetBook
  cases shapeAt u.atlas.board r u.roots.Ht ((j.cast z.primaryRanks).cast u.menu.nodes) with
  | trunk s key=>cases s <;>cases key <;>rfl
  | good =>rfl
  | fall =>rfl

/-- The two static setup functions agree on all numerical actor rows, including empty ones. -/
theorem which_calendar {n' d' : ℕ} (board : NonlinearExpanders.Graph n' d') (k height : ℕ)
    (bits : a.successor.middle.rotorBits=n') (ports : u.atlas.boardDegree=d')
    (same : HEq u.atlas.board board) (residual : r=k) (depth : u.roots.Ht=height)
    (size : (move).shapes=(roster board k height).card) :
    z.which=fun j=>targetBook board k height (j.cast size):=by
  subst height
  funext j
  rw [z.which_book]
  let eqSize:= (z.primaryRanks.trans u.menu.nodes).symm.trans size
  exact (targetBook_cast u.atlas.board board bits ports same u.roots.Ht r k residual
    eqSize ((j.cast z.primaryRanks).cast u.menu.nodes)).symm

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
