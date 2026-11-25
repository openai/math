import OAI.Hierarchy.DescentPhysicalResetSceneInputs
import OAI.Hierarchy.DescentPhysicalStemOperand
import OAI.Hierarchy.DescentResetTrunkOperand

namespace OAI
/-! # Transport of the published signed stem rows to the named reset date -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook ProtocolRAM CandidateFront

/-- Two names for the same front and the same original input banks denote the
same published columns and both actual phases, including their clocks and images. -/
theorem original_stem_coordinates {a b : CandidateFront} {start w : ℕ}
    (same : a=b) (x : a.Originals start) (y : b.Originals start) (inputs : HEq x y)
    (flags count inverse : Bank) (left : a.SceneRoom start (a.fromOriginals start x flags count inverse) w)
    (right : b.SceneRoom start (b.fromOriginals start y flags count inverse) w) :
    a.stemOutput start=b.stemOutput start ∧ a.trunkEnd start=b.trunkEnd start ∧
    (∀i j,a.stemOperand start i j=b.stemOperand start i j) ∧
    a.received start (a.fromOriginals start x flags count inverse) left =
      b.received start (b.fromOriginals start y flags count inverse) right ∧
    a.trunkScene start (a.fromOriginals start x flags count inverse) left =
      b.trunkScene start (b.fromOriginals start y flags count inverse) right ∧
    (∀i,a.trunkOperand start i=b.trunkOperand start i) := by
  subst b
  cases eq_of_heq inputs
  exact ⟨rfl,rfl,fun _ _=>rfl,rfl,rfl,fun _=>rfl⟩

end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
