import OAI.Hierarchy.DescentPhysicalResetSceneRead
import OAI.Hierarchy.DescentResetTrunkProjectedHeaders
import OAI.Hierarchy.DescentResetTrunkScalarBanks

namespace OAI
/-! # Broadcast headers and descriptors on the completed physical reset treatment -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentDyadicSpan DescentPackedZip DescentSIMDLookup DescentSixParty.Chronology ProtocolRAM
open DescentResetStemPackedIssue DescentResetStemHeaders
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (floor : ℕ) (s : v.Scene) {w : ℕ} (room : v.SceneRoom floor s w)
local notation "peer₀" => v.peer
local notation "date₀" => v.peers floor
local notation "scalar₀" => (peer₀).endAddress date₀
local notation "split₀" => Mixed.Projected.splitAt (v.parentEnd floor) v.signedQueries (peer₀).oldDegree
  (peer₀).oldHosts (peer₀).groups v.blocks v.stemField v.oldLanes (peer₀).lanes
local notation "A₀" => Mixed.plan split₀ (v.parent floor).base v.oldTicketCount v.newHosts

def trunkHeader := (A₀).hdr (peer₀).oldDegree v.stemField (peer₀).lanes (peer₀).oldHosts v.newHosts
  (peer₀).groups (v.blocks*v.signedQueries)
def stemOutput := (A₀).out (peer₀).oldDegree v.stemField (v.metaBits*7) v.oldTicketCount (peer₀).lanes
  (peer₀).oldHosts v.newHosts (peer₀).groups (v.blocks*v.signedQueries)

theorem trunk_regions_of_format
    (queries : v.projectionCount=v.signedQueries*((peer₀).oldDegree+2))
    (digits : v.projectionBits=v.stemField) :
    scalar₀+v.newHosts+span v.newHosts≤v.trunkHeader floor ∧
    outputBase v.newHosts (peer₀).groups (peer₀).lanes (v.metaBits*7) (v.trunkHeader floor)+
      v.newHosts*chunks (peer₀).groups (peer₀).lanes≤v.mixed floor ∧
    v.stemOutput floor+(v.blocks*v.signedQueries)*(v.newHosts*chunks (peer₀).groups (peer₀).lanes)=v.mixed floor:=by
  have hx:=Mixed.Projected.header_borders (D:=(peer₀).oldDegree) (f:=v.stemField) (Q:=v.signedQueries)
    (K:=v.oldTicketCount) (v.parentEnd floor) (v.parent floor).base v.metaBits (peer₀).oldHosts v.newHosts
    (peer₀).groups v.blocks v.oldLanes (peer₀).lanes
  have scalar : scalar₀+v.newHosts+span v.newHosts≤v.parentEnd floor:=by
    change v.parentStart floor+span v.newHosts≤DescentResetParentAperture.endAddress (v.parentStart floor) (peer₀).hosts v.newHosts
    rw [DescentResetParentAperture.extent]
    have cap:=Nat.le_max_right (v.newHosts+1) (span v.newHosts)
    omega
  have finish : Mixed.Projected.extent (v.parentEnd floor) (v.parent floor).base (peer₀).oldDegree
      v.stemField v.metaBits v.oldTicketCount (peer₀).oldHosts v.newHosts (peer₀).groups v.blocks
      v.oldLanes (peer₀).lanes v.signedQueries=v.mixed floor:=by
    unfold Mixed.Projected.extent Mixed.Projected.splitAt mixed projected
    rw [queries,digits]
  exact ⟨scalar.trans hx.1,hx.2.1.trans finish.le,hx.2.2.trans finish⟩

include s in
theorem trunk_regions :
    scalar₀+v.newHosts+span v.newHosts≤v.trunkHeader floor ∧
    outputBase v.newHosts (peer₀).groups (peer₀).lanes (v.metaBits*7) (v.trunkHeader floor)+
      v.newHosts*chunks (peer₀).groups (peer₀).lanes≤v.mixed floor ∧
    v.stemOutput floor+(v.blocks*v.signedQueries)*(v.newHosts*chunks (peer₀).groups (peer₀).lanes)=v.mixed floor:=
  v.trunk_regions_of_format floor s.stems.queries s.stems.digits

/-- Only the three measured raw peers, two trunk endpoints and the root
flag enter the scalar header. Every operand ends below the actual date scan. -/
theorem physical_trunk_fits (high : scalar₀<2^w) :
    (DescentSixParty.ClosedReset.Window.rawTrunkExpr v.metaBits (peer₀).hosts
      ((peer₀).rawPeers date₀) ((peer₀).threshold date₀)).Fits w scalar₀:=by
  let p:=v.peer
  let t:=v.peers floor
  have old : p.rawPeers t+3*p.hosts=p.three t:=rfl
  have bnd:=p.ordered t
  have early : p.rawPeers t≤p.threshold t:=(Nat.le_add_right _ _).trans (old.le.trans (bnd.2.1.trans bnd.2.2.1))
  refine DescentSixParty.ClosedReset.Window.raw_trunk_fits ?_ le_rfl high
  exact Nat.add_le_add_right (Nat.add_le_add_right early _) _

theorem received_trunk_header (initial : Memory w) :
    TablesOK v.newHosts (peer₀).groups (peer₀).lanes (v.metaBits*7) (v.trunkHeader floor)
      ((v.received floor s room).image initial):=
  Mixed.Projected.header_image (v.parentEnd floor) (v.parent floor).base v.metaBits (peer₀).oldHosts v.newHosts
    (peer₀).groups v.blocks v.oldLanes (peer₀).lanes s.stems.parse s.stems.side s.stems.operands s.stems.ports _
    ((v.stem_boundary s.stems floor).le.trans_lt room.stems.final)

theorem received_trunk_scalar (initial : Memory w) (i : Fin v.newHosts) :
    (v.received floor s room).image initial (scalar₀+i.val)=
      v.preParent floor s room initial (scalar₀+i.val):=
  (v.retained_cuts floor s room initial).1 _ (Nat.add_lt_add_left i.isLt _)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
