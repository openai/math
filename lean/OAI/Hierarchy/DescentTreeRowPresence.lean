import OAI.Hierarchy.DescentFallbackRootSocket
import OAI.Hierarchy.DescentResetActorPlanes

namespace OAI
/-! # The occupied native receiver of an installed fallback tree site -/
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
local notation "oldRank" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "dense" => ((Z).rawHostRank T oldRank).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation:max "treeSite" s:arg t:arg v:arg => (⟨(s,.inr t),v⟩ : (Z).bank.Site)

theorem tree_row_presence {H : ℕ} (next : Fintype.card B.next.V≤H) (s : Bool) (t : (Z).Fallback)
    (v : Physical.Site ((Z).placement.fallbackBook s t).height) :
    let u:=treeReceiver B (treeSite s t v)
    actualBit B next (((denseOrder B) u.1.2).castLE next) u.1.1 u.2≠0 ∧
      u.1.2=(Z).placed T ((Z).privateSiteAt T s (.inr t) v) :=by
  intro u
  let source:=(Z).privateSiteAt T s (.inr t) v
  let landed:=DescentPhysicalOrder.rename rawSite source
  constructor
  · have witness : ∃ site:B.reblock.result.graph.Site,
        (B.next.vertex.trans (Fin.castLEEmb next)) (B.next.placement.pos site).2=
            ((denseOrder B) u.1.2).castLE next ∧
        (B.next.placement.pos site).1=u.1.1 ∧ B.next.placement.block site=u.2 :=
      ⟨landed,rfl,rfl,rfl⟩
    simpa [actualBit] using witness
  · exact congrArg (fun site=>site.1.2) (named_home B source)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
