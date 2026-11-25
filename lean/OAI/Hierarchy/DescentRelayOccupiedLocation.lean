import OAI.Hierarchy.DescentOriginalOperandLocation
import OAI.Hierarchy.DescentResetOriginalOperandSite

namespace OAI
/-! # The occupied compact archive row at a genuine reset relay -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentResetTrunks Chronology
open DescentCompiler DescentColonies DescentStageEdgeReceipt Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (whole : p∣B.reset.unit) (a : Archive W)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "where_" x => resetOrigin B hp whole a x
local notation "loc_" => fun e : (raw_).graph.Edge=>B.terminals.home ((raw_).graph.dst e)


open DescentDatedAddressBook DescentSharedCableNames
/-- The original archived ordinal and the physical receiver of a reached relay
are read at the same occupied output coordinates. -/
theorem relay_occupied_location (ports : DatePorts) (number : Local next_)
    (room : DatePorts.RangeRoom ports B.next next_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes)
    (h₀ : Fin ports.operandHosts) (group_ : Fin ports.venue.groups)
    (y : NodeOrder.All next_) (seen : DatePorts.slotAt ports B.next next_ number room block node h₀ group_=some y)
    (rack : Fin (S.hostSize (i+1))) (hostAt : rack.val=h₀.val)
    (e₀ : (raw_).graph.Edge) (origin : (where_ y)=Sum.inr (.inl e₀)) :
    operandLocation B (block.cast (congrArg (2^·) room.radix.symm)) rack (group_.cast room.groups.symm)=
      some ((blocks B).dst (trunkParent B (loc_ e₀))) ∧ node.val=(number y.1 y.2).val :=by
  obtain ⟨site,ordinal⟩:=location_at_archive B ports next_ number room block node h₀ group_ y seen rack hostAt
  have placed := (hop).symm_apply_eq.mp (relay_original_site B hp whole a y e₀ origin)
  exact ⟨site.trans (congrArg (fun v => some (Stage.home B.next.placement v)) placed), ordinal⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
