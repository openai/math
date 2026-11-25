import OAI.Hierarchy.DescentNativeResetEdgeTape
import OAI.Hierarchy.DescentSiteNameRead
import OAI.Hierarchy.DescentCollectedPhase
import OAI.Hierarchy.DescentResetLocalOrder

namespace OAI
/-! # Installing the actual site and cable ordinals on both sides of a reset -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCompiler DescentPacking DescentRosterOrder DescentStageEdgeReceipt GroupStage
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {H M : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin M)
local notation "norm" => orderedReblock Z T key
local notation "tape" => nativeResetEdges Z T vertex key
local notation "hostOrd" => Function.Embedding.trans (rawHostRank Z T vertex) Fin.valEmbedding
variable {G : PoweredGadget F} {q fee : ℝ} {groups k i : ℕ} {S : AtomSchedule}
    (N : GroupStage (orderedOrdinary Z T key) G q fee (Fin groups) ↥(commonNames Z T) k) (paid : N.StateBounds S i)
local notation "rows" => DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) hostOrd
local notation "ps" => DescentPhysicalOrder.rename (N.siteFrom rows paid.coordinates)
local notation "rawId" => Function.Embedding.trans (Tape.order tape) Fin.valEmbedding
local notation "siteId" => N.siteFrom rows paid.coordinates
local notation "shortId" => DescentResetLocalOrder.allCode N rawId S paid siteId
local notation "pe" => DescentPhysicalOrder.rename shortId

def namedReset : Normalize (orderedReentry Z T key) :=
  (norm).appendNames ps pe

local notation "result" => namedReset Z T vertex key N paid

def namedPlacement : GroupStage (result).result G q fee (Fin groups) ↥(commonNames Z T) k :=
  GroupStage.afterNames norm N ps pe

def namedTape : Tape (result).result.graph.Edge :=
  Tape.afterNames norm tape ps pe

private def selectorAfter {X Y : MarkedWorld F d P bits}
    (rank : X.graph.Edge↪ℕ) (sites : Equiv.Perm X.graph.Site)
    (eqn : Y=PhysicalRename.world X sites (DescentPhysicalOrder.rename rank)) :
    Y.graph.Edge↪Fin (Fintype.card Y.graph.Edge) := by
  subst Y
  exact (DescentPhysicalOrder.rename rank).symm.toEmbedding.trans (DescentPhysicalOrder.physical rank).toEmbedding

omit [Field F] in
private theorem selectorAfter_read {X Y : MarkedWorld F d P bits}
    (rank : X.graph.Edge↪ℕ) (sites : Equiv.Perm X.graph.Site)
    (eqn : Y=PhysicalRename.world X sites (DescentPhysicalOrder.rename rank)) (u : Y.graph.Edge) :
    originalId Y.graph.Edge u=(selectorAfter rank sites eqn u).val := by
  subst Y
  obtain ⟨t,rfl⟩:=(DescentPhysicalOrder.rename rank).surjective u
  change (Fintype.equivFin X.graph.Edge (DescentPhysicalOrder.rename rank t)).val=
    (DescentPhysicalOrder.physical rank ((DescentPhysicalOrder.rename rank).symm (DescentPhysicalOrder.rename rank t))).val
  simp

/-- Orders for two consecutive operations on the same real normalized graph.
The raw tape above reads the previous chronological parent. The next matcher
uses this ordinal, whose within-source comparisons read bounded source slots. -/
def namedOrder : (result).result.graph.Edge↪Fin (Fintype.card (result).result.graph.Edge) :=
  selectorAfter shortId ps ((norm).appendNames_result ps pe)

theorem sourceOrder (e f : {e : (norm).result.graph.Edge // e∈(norm).result.core})
    (same : (norm).result.graph.src e.val=(norm).result.graph.src f.val) :
    DescentPhysicalOrder.physical shortId e.val<DescentPhysicalOrder.physical shortId f.val ↔
      DescentResetLocalOrder.ticket N rawId S paid e<DescentResetLocalOrder.ticket N rawId S paid f :=
  DescentResetLocalOrder.on_source N rawId S paid siteId e f same

local notation "N'" => namedPlacement Z T vertex key N paid
local notation "outTape" => namedTape Z T vertex key N paid

theorem namedBounds : (N').StateBounds S i := by
  obtain ⟨z,cap,wire,hist,degree,coord,whole,count⟩ := N.renamed_fields ps pe ((norm).appendNames_result ps pe)
  change (N').z=N.z at z
  change (N').cap=N.cap at cap
  change (N').wire=N.wire at wire
  change (N').hist=N.hist at hist
  refine ⟨coord paid.coordinates,paid.host,(by simpa only [cap] using paid.capacity),(by simpa only [cap] using paid.bundleCapacity),?_,(by simpa only [hist] using paid.atom),?_,?_,?_⟩
  · exact count.symm ▸ paid.history
  · simpa only [hist] using paid.valuation
  · simpa only [z,wire] using paid.paidUnit
  · rw [z]
    exact whole _ paid.divides

theorem namedScalars : (N').z=N.z ∧ (N').wire=N.wire ∧ (N').hist=N.hist ∧ (N').degree=N.degree := by
  obtain ⟨z,_,wire,hist,degree,_⟩:=N.renamed_fields ps pe ((norm).appendNames_result ps pe)
  exact ⟨z,wire,hist,degree⟩

theorem namedHub : (N').hub=N.hub :=
  (GroupStage.renamed_particle_fields N ps pe ((norm).appendNames_result ps pe)).2.2

theorem namedCapacity : (N').cap=N.cap :=
  (N.renamed_fields ps pe ((norm).appendNames_result ps pe)).2.1

theorem namedEdges (e : (result).result.graph.Edge) :
    originalId (result).result.graph.Edge e=(namedOrder Z T vertex key N paid e).val :=
  selectorAfter_read shortId ps ((norm).appendNames_result ps pe) e

theorem namedSites (v : (result).result.graph.Site) :
    originalId (result).result.graph.Site v=
      ((N').site (denseHostRank Z T vertex) (namedBounds Z T vertex key N paid).coordinates v).val :=
  (N').siteNamed_read hostOrd (namedBounds Z T vertex key N paid).coordinates
    (N.cast_siteNamed rows paid.coordinates pe ((norm).appendNames_result ps pe)) v

theorem namedCuts (q₀ : ℕ) : Normalize.CutsEqual q₀ result ↔ Normalize.CutsEqual q₀ norm :=
  Normalize.cutsEqual_appendNames q₀ norm ps pe

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
