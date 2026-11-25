import OAI.Hierarchy.DescentPhysicalResetAtlas
import OAI.Hierarchy.DescentPreparedPrivateRoots
import OAI.Hierarchy.DescentFallbackRecordFit

namespace OAI
/-! # Address bounds for the actual shared book read by the reset actor -/

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod
open DescentGLPacked ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {a : PhysicalReset} (z : a.Atlas) (sh : a.StencilShape) (start : ℕ)
  (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs) (w : ℕ)

local notation "v" => a.successor
local notation "P" => a.stencilPhase sh start count hub g Y
local notation "rc" => a.rootPhase sh start count hub g Y roots w
local notation "book" => atlasBook z sh start count hub g Y roots w
local notation "actorStart" => (v).middle.stop (a.rebased start)
local notation "source" shape => atlasActors z sh start count hub g Y roots w shape

/-- The literal controls and all four shape-table pages come from the prepared
book. Its hub and neighbor lookups come from the earlier stencil. -/
theorem atlas_actor_refs (shape : ActorFit z roots) (prepared : (rc).PreparedFits book)
    (rootEnd : (rc).preparedEnd book=actorStart) (hosts : (v).actor.hosts=(v).middle.signedHosts)
    (roster : (P).X.roster.Fits w (P).endAddress) (flags : (P).X.hubs.Fits w (P).endAddress) :
    (DescentSharedBookScan.expr (source shape).shared (v).actor.hosts
      (source shape).degree (source shape).treeCap).Fits w actorStart := by
  change (DescentSharedBookScan.expr ((book).common (rc).projectionEnd (v).actor.hosts)
    (v).actor.hosts a.ports (2^roots.Ht)).Fits w actorStart
  rw [hosts]
  have lim := (book).limits (rc).projectionEnd (v).middle.signedHosts
    (2^(v).middle.stencil.c) (v).middle.signedLanes
  have header : (rc).headerEnd book ≤ actorStart := by
    rw [←rootEnd]
    exact Nat.le_add_right ..
  have before : (P).endAddress ≤ (rc).headerEnd book :=
    (rc).origin_le_projection.trans (lim.1.trans (lim.2.1.trans lim.2.2))
  have previous := atlas_previous z sh start count hub g Y roots w
  have near : (book).previousNeighbors.Fits w ((rc).headerEnd book) := by
    rw [previous.1]
    exact ⟨roster.1,roster.2.1,roster.2.2.trans before⟩
  have hubFit : (book).previousHubs.Fits w ((rc).headerEnd book) := by
    rw [previous.2.1]
    exact ⟨flags.1,flags.2.1,flags.2.2.trans before⟩
  have printed : (DescentSharedBookScan.record ((book).common (rc).projectionEnd (v).middle.signedHosts)
      (v).middle.signedHosts a.ports (2^roots.Ht) (roots.Ht+2)).Fits w ((rc).headerEnd book) :=
    DescentSharedBookScan.Public.record_fits (book).previousNeighbors (book).previousHubs roots.Ht
      (lim.2.1.trans lim.2.2) prepared.literals near hubFit
  exact ProtocolRAMGeneratedWrite.fits_mono _ header printed.1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
