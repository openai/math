import OAI.Hierarchy.DescentResetOriginalOperandSite
import OAI.Hierarchy.DescentFallbackRootSocket

namespace OAI
/-! # The physical site of each newly installed reset operand -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentResetTrunks Chronology
open DescentSharedCableNames DescentCompiler DescentColonies DescentStageEdgeReceipt Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (whole : p∣B.reset.unit) (a : Archive W)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation:max "where_" x:arg => resetOrigin B hp whole a x

/-- The compact host of the original edge relay or mounted bank, before its chosen operand is read. -/
def freshHost : (raw_).graph.Edge ⊕ B.reset.bank.Site → Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
  | .inl edge => (blocks B).dst (trunkParent B (B.terminals.home ((raw_).graph.dst edge)))
  | .inr v => treeReceiver B v

theorem fresh_host_of_slot (x:NodeOrder.All next_)
    (child:(raw_).graph.Edge ⊕ Σ v:B.reset.bank.Site,(B.reset.laneRecipe birth unit p hp splitEq v).Node)
    (origin:where_ x=.inr child) :
    freshHost B (Sum.map id Sigma.fst child)=Stage.home B.next.placement x.1:=by
  cases child with
  | inl e =>
    have loc:=relay_original_site B hp whole a x e origin
    change Stage.home B.next.placement (hop ((coarse).graph.dst (trunkParent B (B.terminals.home ((raw_).graph.dst e)))))=_
    exact congrArg (Stage.home B.next.placement) ((congrArg ⇑(hop) loc.symm).trans ((hop).apply_symm_apply x.1))
  | inr k₀ =>
    obtain ⟨v,u⟩:=k₀
    have loc:=device_original_site B hp whole a x v u origin
    change Stage.home B.next.placement (hop ((B.reset.resetNames B.terminals).symm (.inr v)))=_
    exact congrArg (Stage.home B.next.placement) ((congrArg ⇑(hop) loc.symm).trans ((hop).apply_symm_apply x.1))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
