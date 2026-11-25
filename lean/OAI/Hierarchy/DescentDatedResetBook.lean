import OAI.Hierarchy.DescentPackedCanvasRoom
import OAI.Hierarchy.DescentEstimatorArenaExtent
import OAI.Hierarchy.DescentEstimatorImmutableExtent
import OAI.Hierarchy.DescentDatedResetArea
import OAI.Hierarchy.DescentSubwordReturn
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The actual measured canvas, estimator, signed remix and reblocking in one address book -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement
open DescentPackedWalsh DescentGLPacked DescentSIMDLookup ProtocolRAM DescentDatedAddressBook Filter
noncomputable section
variable (p : Placement)

def estimator (payload gain : ℕ) (positive : 0<p.geo.bits) : EstimatorArena :=
  ⟨p.geo.hosts*(p.geo.high+p.geo.low+1+p.geo.ports),p.geo.high,p.geo.low,payload,p.geo.bits,gain,positive,
    p.endAddress,0,p.depthRows,p.gainRows⟩

def routedHosts := ((1+p.geo.ports)+(p.geo.high+p.geo.low))*p.geo.hosts
def remixAt (payload gain : ℕ) (positive : 0<p.geo.bits) := (p.estimator payload gain positive).endAddress
def remixEnd (payload gain : ℕ) (positive : 0<p.geo.bits) :=
  BankImage.Dated.endAddress (p.remixAt payload gain positive) p.routedHosts p.geo.high p.geo.low p.geo.bits
/-- The true selected rotation matrix is kept live in the word immediately before this boundary. -/
def rotationEnd (payload gain : ℕ) (positive : 0<p.geo.bits) :=
  let d:=p.geo.high+p.geo.low
  p.remixEnd payload gain positive+(2^d)^d+(2^d)^d+1
def repackedEnd (payload gain : ℕ) (positive : 0<p.geo.bits) (field groups ratio lanes : ℕ) :=
  Subwords.finish (p.rotationEnd payload gain positive) field p.routedHosts groups ratio lanes

theorem estimator_columns (payload gain : ℕ) (positive : 0<p.geo.bits) :
    let E:=p.estimator payload gain positive
    E.origin=p.endAddress ∧ E.dataGap=0 ∧ E.depthRows=p.depthRows ∧ E.gainRows=p.gainRows ∧
      E.hosts=p.routedHosts := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  dsimp [estimator,routedHosts]
  ring

theorem estimator_prefix (payload gain : ℕ) (positive : 0<p.geo.bits) :
    p.endAddress≤(p.estimator payload gain positive).staticEnd := by
  let E:=p.estimator payload gain positive
  have left : E.origin≤E.reduceAt:=Nat.le_add_right ..
  have more : E.reduceAt≤E.orderAt := by
    rw [EstimatorArena.orderAt,E.plan.header_offset]
    exact Nat.le_add_right ..
  exact (((left.trans more).trans (show E.orderAt≤E.transformAt from Nat.le_add_right ..)).trans
    (show E.transformAt≤E.squareAt from Nat.le_add_right ..)).trans (Nat.le_add_right ..)

theorem estimator_range (payload gain : ℕ) (positive : 0<p.geo.bits) :
    let E:=p.estimator payload gain positive
    E.origin≤E.staticEnd ∧ E.staticEnd≤E.endAddress ∧ E.endAddress≤p.remixEnd payload gain positive := by
  intro E
  refine ⟨p.estimator_prefix _ _ _,?_,?_⟩
  · rw [E.endAddress_eq]
    have start : E.staticEnd≤E.start:=Nat.le_add_right ..
    omega
  · exact BankImage.Dated.origin_le_endAddress E.endAddress p.routedHosts p.geo.high p.geo.low p.geo.bits

/-- Use the genuine per-buffer GL capacity theorem on the exact allocator originating
after the primed depth/gain tables. -/
theorem estimator_room (payload gain : ℕ) (positive : 0<p.geo.bits) (w e A K : ℕ)
    (wire : e+2≤w) (prefixRoom : (p.estimator payload gain positive).staticEnd≤2^e)
    (hosts : p.routedHosts≤2^A) (axis : p.geo.high+p.geo.low≤K) (panel : 5+A+2*K≤e) :
    let E:=p.estimator payload gain positive
    E.endAddress<2^w ∧ DescentGL.PhysicalTrajectory.Room w E.dim E.solveAt E.bank := by
  intro E
  have count : E.hosts=p.routedHosts := (p.estimator_columns payload gain positive).2.2.2.2
  have fit:=E.end_room_bits w e A K wire prefixRoom (Nat.zero_le _) (count.trans_le hosts) axis panel
  exact ⟨fit,E.room_of_end fit⟩

/-- Every stored input remains strictly before the fresh estimator and routing banks. -/
theorem old_before (payload gain : ℕ) (positive : 0<p.geo.bits) {floor x : ℕ}
    (prior : x<floor) (installed : floor≤p.middle) :
    x<(p.estimator payload gain positive).origin ∧ x<p.remixAt payload gain positive ∧
      x<p.remixEnd payload gain positive := by
  have pre : p.middle≤p.endAddress := by rw [p.end_eq];exact Nat.le_add_right ..
  have old:=prior.trans_le (installed.trans pre)
  obtain ⟨one,two,three⟩:=p.estimator_range payload gain positive
  exact ⟨old,old.trans_le (one.trans two),old.trans_le ((one.trans two).trans three)⟩

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement

end OAI
