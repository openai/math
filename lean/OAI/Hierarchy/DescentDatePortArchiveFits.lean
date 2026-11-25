import OAI.Hierarchy.DescentPriorArchiveLimits
import OAI.Hierarchy.DescentDatedRegisterState

namespace OAI
/-! # The original argument, arity and role pages below each chronological cut -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentCompiler DescentSIMDLookup DescentInitialHost DescentDatedSeedStartup
noncomputable section
def storage (p : DatePorts) (k : ℕ) (next : DescentResetRetainedSetup.Layout) : DescentResetRetainedSetup.Layout :=
  {next with
    bits:=p.operandBits
    hosts:=p.operandHosts
    groups:=p.venue.groups
    blocks:=2^k
    previousNodes:=p.nodes
    previousArgs:=p.argumentsPerNode
    previousLanes:=p.operandLanes}

structure ArchiveFits (p : DatePorts) (k floor : ℕ) : Prop where
  data : ∀L, p.archive.Fits (p.storage k L) floor
  blocks : 2^k≤p.archive.roles.blocks
  roles : p.archive.roles.endAddress≤floor

theorem ArchiveFits.before {p : DatePorts} {k a b : ℕ} (h : p.ArchiveFits k a) (le : a≤b) : p.ArchiveFits k b :=
  ⟨fun L=>(h.data L).before le,h.blocks,h.roles.trans le⟩

variable {F : Type} [Field F] {P : Type} {c p : ℕ}
theorem initial_archive_fits (G : PoweredGadget F) (op : RotorSpec) (X : Catalyst.Approximation F c p) (R : ℕ)
    (l : DescentDatedSeedStartup.Layout) (k H groups payload Z : ℕ) :
    let v:=initial G op X R l k H groups payload Z
    let table:=DescentDatedSeedStartup.Input.nodeChart l k H groups
    let base:=table.seedEnd (DescentDatedSeedStartup.endAddress X l H groups k)
    let M:=Primitive.paletteLanes G op l.seedWidth Z payload k
    v.ArchiveFits k (Primitive.initialEnd X R l.seedWidth payload k H groups M base):=by
  dsimp only
  exact ⟨fun L=>PriorResetArchive.initial_limits G op X R l k H groups payload Z _ rfl rfl,
    le_rfl,le_rfl⟩

theorem ordinary_archive_fits (v : PhysicalOrdinary F P) (floor k : ℕ)
    (blocks : v.resolver.blocks=2^k) (keys : v.reference.k=k) (groups : v.venue.groups=v.resolver.groups)
    (bits : v.metadata.chart.bits=v.resolver.size+2) (nodes : v.metadata.chart=v.nodeChart)
    (span : v.metadata.spanBits=v.resolver.size+2) (book : v.operandBook=v.finalChart) :
    (ordinary v floor).ArchiveFits k (v.returnedEnd floor):=by
  constructor
  · intro L
    refine PriorResetArchive.ordinary_limits ((ordinary v floor).storage k L) v floor ?_ nodes span book rfl
    change DescentDatedNodeMetadata.Chart.mk (2^k) v.resolver.nodes v.resolver.hosts v.venue.groups
      (v.resolver.size+2) v.resolver.lanes=v.nodeChart
    rw [←blocks,groups,←bits]
    rfl
  · change 2^k≤2^v.reference.k
    rw [keys]
  · change v.primitiveEnd floor≤v.returnedEnd floor
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

theorem reset_archive_fits {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w) (k : ℕ)
    (blocks : a.successor.receiver.blocks=2^k) (groups : a.successor.venue.next.groups=a.successor.receiver.groups)
    (hosts : a.successor.sheets.hosts=a.successor.receiver.hosts)
    («meta» : a.successor.metadata.chart=⟨a.successor.receiver.blocks,a.successor.nodes,
      a.successor.receiver.hosts,a.successor.receiver.groups,a.successor.nodeBits,a.successor.receiver.lanes⟩)
    (roles : a.successor.primitive.chart.blocks=a.successor.receiver.blocks) :
    (reset a floor u).ArchiveFits k (a.successor.metadataEnd (a.rebased floor)):=by
  let v:=a.successor
  let base:=a.rebased floor
  let port_:=reset a floor u
  constructor
  · intro L
    refine PriorResetArchive.reset_limits (port_.storage k L) v base ?_ blocks.symm ?_ rfl
    · change DescentDatedNodeMetadata.Chart.mk (2^k) v.nodes v.sheets.hosts v.venue.next.groups
        v.nodeBits v.receiver.lanes=v.metadata.chart
      rw [←blocks,hosts,groups,«meta»]
    · change v.sheets.hosts*chunks v.venue.next.groups v.receiver.lanes=_
      rw [hosts,groups]
  · change 2^k≤v.primitive.chart.blocks
    rw [roles,blocks]
  · change v.primitiveEnd base≤v.metadataEnd base
    dsimp [ResetOutput.metadataEnd,MetadataReturn.endAddress,
      MetadataReturn.headerEnd,DescentDatedNodeMetadata.Chart.endAddress,
      DescentDatedNodeMetadata.Chart.output,DescentDatedNodeMetadata.Chart.scalarEnd]
    omega

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
