import OAI.Hierarchy.DescentObservedTreeSocketKey
import OAI.Hierarchy.DescentGoodTapIssuedWord
import OAI.Hierarchy.DescentCapturedRelayRows

namespace OAI
/-! # Earlier registered observations at the actual fresh relay or device site -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentPhysicalOrder DescentStageEdgeReceipt ThreeFlat.Routing
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentStageEdgeReceipt
open DescentFallbackItemSelect DescentNamedContact
open DescentPrimitivePalette DescentLaneGates DescentBundleHistory DescentResetGates DescentResetFreshWires
open DescentResetLocalNodes DescentLocalArchiveOrder DescentKernelHistory DescentTreeLaneProgram DescentContactTree
open Chronology Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement

open DescentRotor DescentDenseHostOrder DescentCommonHost DescentRelativeContacts
variable {p field query lanes nodes args : ℕ}
local notation "unit" => B.reset.unit/p
local notation "pub" => publicOperandConfig B field query lanes unit unit nodes args p
local notation "raw" => W.granular B.count (z*G.b) B.fit
local notation "r" => (Z).k-(T).commonDepth
local notation "hgt" => GroupStage.depthBound D n f g
local notation "shapeBook" => DescentDenseHostOrder.roster (Z).graph r hgt
local notation "header" x:arg => (pub).oldConfig.header ((pub).basic x)
local notation "rank_" a:arg => (DescentDenseHostOrder.localRank (Z).graph r hgt a).val
local notation "short_" edge:arg => (shortName (T).commonDepth ((T).code ((T).home ((raw).graph.dst edge)))).2
local notation "tr_" s:arg t:arg q:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T s (.inr t) q))

/-- Only the earlier registers at the actual origin are required.
All three alternatives refer to the same observed packed input row. -/
def FreshObservation (x : (pub).Data (Z).n) (origin : (raw).graph.Edge ⊕ (Z).bank.Site) : Prop :=
  ((header x) 0).val≠0 ∧ ((header x) 1).val=(A).cap ∧
  match origin with
  | .inl e =>
      OriginalRelayRows (field:=field) (query:=query) (lanes:=lanes) (batches:=unit) (split:=unit)
        (nodes:=nodes) (args:=args) (grain:=p) (M:=lanes) B e x ∧
      ∃ tag:↥shapeBook, ((header x) 2).val=rank_ tag ∧ tag.val=.trunk true ((),short_ e)
  | .inr ⟨⟨side₀,.inl rGate⟩,rCell⟩ =>
      GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args)
        (grain:=p) B side₀ rGate x ∧
      (((pub).reg x) 1).val=((Z).goodLabel T rGate).val.1+1 ∧ (((pub).reg x) 2).val%2=0 ∧
      ((Z).circuit side₀ rGate).layers*unit≤nodes ∧
      ∃ tag:↥shapeBook, (((pub).reg x) 3).val=rank_ tag ∧
        tag.val=.good side₀ ((),((Z).goodLabel T rGate).val.2)
          ((DescentCommonPalette.rotorSiteEquiv (Z).graph d
            (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit side₀ rGate)
            C (Z).width (Z).unit).symm rCell)
  | .inr ⟨⟨side₀,.inr t⟩,q₀⟩ =>
      FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args)
        (grain:=p) B side₀ t x ∧ ((header x) 2).val=rank_ (tr_ side₀ t q₀)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
