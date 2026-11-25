import OAI.Hierarchy.DescentCalendarStemCoordinates
import OAI.Hierarchy.DescentPhysicalPeerProbe
import OAI.Hierarchy.DescentPhysicalResetSceneRead

namespace OAI
/-! # Literal addresses and memories of the measured peer prefixes -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook ProtocolRAM CandidateFront Computability.VPVNP.BurstRAM

theorem original_probe_room {a b : CandidateFront} {left right w : ℕ}
    (front : a=b) (offset : left=right) (x : a.Originals left) (y : b.Originals right)
    (sources : HEq x y) {f f' c c' i i' : Bank} (flags : f=f') (count : c=c') (inverse : i=i')
    (leftRoom : a.SceneRoom left (a.fromOriginals left x f c i) w) :
    b.SceneRoom right (b.fromOriginals right y f' c' i') w:=by
  subst b right f' c' i'
  cases eq_of_heq sources
  exact leftRoom

theorem original_probe_coordinates {a b : CandidateFront} {left right w : ℕ}
    (front : a=b) (offset : left=right) (x : a.Originals left) (y : b.Originals right)
    (sources : HEq x y) {flags flags' count count' inverse inverse' : Bank}
    (f : flags=flags') (c : count=count') (i : inverse=inverse')
    (leftRoom : a.SceneRoom left (a.fromOriginals left x flags count inverse) w)
    (rightRoom : b.SceneRoom right (b.fromOriginals right y flags' count' inverse') w) :
    a.peer.rawPeers (a.peers left)=b.peer.rawPeers (b.peers right) ∧
    a.peers left=b.peers right ∧ a.trunkEnd left=b.trunkEnd right ∧
    (∀m : Memory w,a.probeStart left (a.fromOriginals left x flags count inverse) m=
      b.probeStart right (b.fromOriginals right y flags' count' inverse') m) ∧
    (∀m : Memory w,a.preScalar left (a.fromOriginals left x flags count inverse) leftRoom m=
      b.preScalar right (b.fromOriginals right y flags' count' inverse') rightRoom m) ∧
    (∀x₀ j,a.stemOperand left x₀ j=b.stemOperand right x₀ j) ∧
    (∀x₀,a.trunkOperand left x₀=b.trunkOperand right x₀) ∧
    a.trunkScene left (a.fromOriginals left x flags count inverse) leftRoom =
      b.trunkScene right (b.fromOriginals right y flags' count' inverse') rightRoom:=by
  subst b right flags' count' inverse'
  cases eq_of_heq sources
  exact ⟨rfl,rfl,rfl,fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,rfl⟩

end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
