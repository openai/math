import OAI.Hierarchy.DescentMeasuredTreeRangeCast
import OAI.Hierarchy.DescentObservedTreeSocketKey

namespace OAI
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
local notation "c" => (T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-c
variable {field query lanes nodes args grain p : ℕ} (hp : 0<p) (whole : p∣B.reset.unit)
local notation "batches" => (Z).unit/p
local notation "unitFit" => ((Nat.div_mul_cancel whole).symm : (Z).unit=batches*p)
local notation "cfg" => flatConfig B field query lanes batches batches nodes args
local notation "pub" => publicOperandConfig B field query lanes batches batches nodes args grain
local notation "birth" => DescentOrderedReset.grains W B.count B.order
variable (s : Bool) (t : B.reset.Fallback)
local notation "bk" => (R).fallbackBook s t
local notation:max "venue" q:arg => (⟨(s,.inr t),q⟩ : (Z).bank.Site)
local notation:max "gateAt" q:arg => (Z).laneRecipe birth batches p hp unitFit (venue q)
local notation:max "header" x:arg => (cfg).header ((pub).basic x)
local notation:max "here" q:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T s (.inr t) q))


open DescentRetainedRangeDigits
/-- At a fallback gate, its original packet and its original two coordinate
columns determine the three span digits for every flattened argument. -/
theorem observed_tree_span (q₀ : DescentContactTree.Physical.Site (bk).height) (node : (gateAt q₀).Node)
    (x : (pub).Data (Z).n)
    (rows : FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes)
      (args:=args) (grain:=grain) B s t x)
    (live : (header x 0).val≠0)
    (badge : (header x 2).val=(DescentDenseHostOrder.localRank (Z).graph r Ht (here q₀)).val)
    (slot : Fin nodes) (numbered : slot.val=((Z).laneNodeOrder birth batches p hp unitFit (venue q₀) node).val)
    (arg : Fin args) (width : ℕ) (printed : 2<2^width) (axis : Fin 3) :
    ((pub).column (Z).graph width (some (page axis)) (finProdFinEquiv (arg,slot)) x).val=
      atSlot ((Z).laneShape birth batches p hp unitFit (venue q₀)) node arg.val axis :=by
  rcases rows with ⟨height,groupId,pad₀,snapshot,known⟩
  let sample:=pub
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age₀,date,extent,tickets,unit₀,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain₀,wire₀,atoms,branch,capacity₀⟩
  subst order
  exact GroupStage.measured_tree_range_cast phase S ready _ oldOrder groupId compact pad₀ Z₀ T₀ frame snapshot
    Z₀.k extent sample s t x known.packet known.hostRead known.groupWord known.fineWord known.indexed known.sorted p hp (Nat.div_mul_cancel whole).symm
    q₀ node live badge slot numbered arg width printed axis

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
