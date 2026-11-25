import OAI.Hierarchy.DescentResetTrunkSource
import OAI.Hierarchy.DescentRelaySavedPacket

namespace OAI
/-! # Occupancy and the shape register at a genuine incoming relay -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentFallbackOperandQuery DescentNextSignedWindow DescentResetWireTags DescentTreePrefixIntervals
open DescentRouterSlots DescentContactTree
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)

local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit

variable {field query lanes batches split nodes args grain : ℕ}
open DescentPackedRotorMatrix DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape

open DescentOperandStateBanks DescentResetOperandComponents DescentOperandCandidateLookup
open DescentDatedAddressBook.ResetOutput

local notation "End₀" => (old).graph.Edge
local notation "land" e => (T).home ((old).graph.dst e)
local notation "trunk" e => trunkParent B (land e)
local notation "receiver" t => (blocks B).dst (trunkParent B t)
local notation "site" e => receiver (land e)

open DescentMeasuredOperandKey DescentRelativeContacts DescentSharedBookScan DescentFallbackItemSelect
open DescentDenseHostOrder DescentPacking

open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentStageEdgeReceipt
open DescentOrdinaryAtomFieldRAM

theorem relay_terminal_presence {H : ℕ} (next:Fintype.card B.next.V≤H) (t:(Z).Fallback) :
    let host:=((denseOrder B) (receiver t).1.2).castLE next
    actualBit B next host (receiver t).1.1 (receiver t).2≠0 ∧
      ((Z).localShape T (receiver t).1.2).val=.trunk true ((),(shortName (T).commonDepth ((T).code t)).2) :=by
  intro host
  constructor
  · have witness : ∃s:B.reblock.result.graph.Site,
        (B.next.vertex.trans (Fin.castLEEmb next)) (B.next.placement.pos s).2=host ∧
        (B.next.placement.pos s).1=(receiver t).1.1 ∧ B.next.placement.block s=(receiver t).2 :=
      ⟨hop ((coarse).graph.dst (trunkParent B t)),rfl,rfl,rfl⟩
    simpa [actualBit] using witness
  · have trueHost : (receiver t).1.2.val=.trunk true (shortName (T).commonDepth ((T).code t)) :=
      (trunk_side B t true).1
    change DescentDenseHostOrder.shape (Z).graph (receiver t).1.2.val=_
    rw [trueHost]
    rfl

theorem relay_row_presence {H : ℕ} (next:Fintype.card B.next.V≤H) (edge:End₀) :
    let host:=((denseOrder B) (site edge).1.2).castLE next
    actualBit B next host (site edge).1.1 (site edge).2≠0 ∧
      ((Z).localShape T (site edge).1.2).val=.trunk true ((),(shortName (T).commonDepth ((T).code (land edge))).2) :=
  relay_terminal_presence B next (land edge)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
