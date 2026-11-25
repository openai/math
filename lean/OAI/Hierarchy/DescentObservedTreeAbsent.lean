import OAI.Hierarchy.DescentObservedTreeSocketKey
import OAI.Hierarchy.DescentMeasuredTreeAbsent
import OAI.Hierarchy.DescentReachedRootRows
import OAI.Hierarchy.DescentObservedTreeRange

namespace OAI
/-! The observed fallback tuple with the reached grain count at unoccupied exceptional-tree node slots. -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentRelativeContacts
open DescentPackedFallbackTree DescentFallbackItemSelect DescentStageEdgeReceipt
open DescentOrderedReset DescentOrderedWords DescentFallbackRankRAM DescentSharedBookScan DescentRosterOrder DescentPackedLeafSelector
open DescentSharedLeafLookup DescentGroupPeerOrder DescentPlainTerminal DescentPlainTerminal.Suffix
open DescentRetainedRangeDigits DescentBundleHistory DescentTreeLaneProgram
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000

variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (grp : Fin groups↪ℕ) (vertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
local notation "native" => order.trans Fin.valEmbedding
local notation "pad" => vertex.trans (Fin.castLEEmb padded)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
variable (Z : ResetInput (F:=F) (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht)
  (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (filled W.graph A.pos A.block digits) A.hub g)
variable (zEq : zz=A.z) (wireEq : ww=A.wire) (countEq : ct=A.grainCount)
variable (snap : RootObservation A S ready digits (order.trans Fin.valEmbedding) grp (vertex.trans (Fin.castLEEmb padded)) Z T frm field)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
variable (effective : ℕ) (extent : effective=m)
local notation "L" => 2^(effective-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "cfg" sample:arg => ({sample with
  oldDegree := A.degree
  oldCap := A.cap
  donors := L
  fineBits := k
  fieldBits := field
  residual := r
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)
local notation:max "whereHost" t:arg => frm.host.symm (T.code t).1
local notation:max "hiAt" t:arg => selectedRoot A S ready Z T t
local notation "ranks" => DescentSharedBookScan.ranks (a:=r) («Y»:=2^Z.n) (D:=A.degree) snap.chart (2^Ht) (Ht+2) snap.memory
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item Z.placement.contact Z.placement.owner s (.inr t)
local notation:max "book" s:arg t:arg => Z.placement.fallbackBook s t
local notation:max "loc" s:arg e:arg => localAddress A native S ready digits frm.basis («c»:=c) s e
local notation:max "row" s:arg e:arg => finProdFinEquiv (((loc s e).1.cast (congrArg (fun l=>2^(l-c)) extent).symm),(loc s e).2)
local notation "chron" => DescentOrderedReset.grains W ct order

local notation:max "heightAt" s:arg t:arg => (book s t).height
local notation:max "surface" sample:arg => ({sample with oldConfig:=cfg (sample).oldConfig}:DescentResetPublicOperandBook.Config)
local notation:max "treeVenue" side:arg t:arg vertex₁:arg => (⟨(side,.inr t),vertex₁⟩ : Z.bank.Site)
local notation:max "treeBadge" side:arg t:arg vertex₁:arg => Z.localShape T (Z.placed T (Z.privateSiteAt T side (.inr t) vertex₁))

include zEq wireEq countEq in
theorem measured_tree_absent_cast (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
    (x : (surface sample).Data Z.n)
    (packet : (cfg sample.oldConfig).packet ((surface sample).basic x)=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast (congrArg (fun len=>2^(len-c)) extent))) snap.peers (fun u hi lo=>snap.marks u hi (lo.cast (congrArg (fun len=>2^(len-c)) extent))) (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (p : ℕ) (hp : 0<p) (positive : 0<sample.batches) (unitFit : Z.unit=sample.batches*p)
    (site : Physical.Site (heightAt side t)) (slot : Fin sample.nodes)
    (absent : Fintype.card (Z.laneRecipe chron sample.batches p hp unitFit (treeVenue side t site)).Node≤ slot.val)
    (active : ((cfg sample.oldConfig).header ((surface sample).basic x) 0).val≠0)
    (shapeRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 2).val=
      (DescentDenseHostOrder.localRank Z.graph r Ht (treeBadge side t site)).val)
    (arg : Fin sample.args) (bitsOut : ℕ) (axis : Fin 3) :
    (surface sample).column Z.graph bitsOut (some (page axis)) (finProdFinEquiv (arg,slot)) x=0 :=by
  subst zz
  subst ww
  subst ct
  subst effective
  exact measured_tree_absent A S ready digits order grp vertex padded Z T frm snap sample side t x packet
    p hp positive unitFit site slot absent active shapeRead arg bitsOut axis

end
end Hierarchy.DescentSixParty.GroupStage

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
variable {field query lanes nodes args grain p : ℕ} (hp : 0<p) (positive : 0<B.reset.unit) (whole : p∣B.reset.unit)
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
include positive whole s t in
theorem observed_tree_absent (cell : Physical.Site (bk).height) (node : Fin nodes)
    (absent : Fintype.card (gateAt cell).Node≤node.val)
    (x : (pub).Data (Z).n) (rows : FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes)
      (nodes:=nodes) (args:=args) (grain:=grain) B s t x)
    (active : (header x 0).val≠0)
    (shapeRead : (header x 2).val=(DescentDenseHostOrder.localRank (Z).graph r Ht (here cell)).val)
    (arg : Fin args) (bitsOut : ℕ) (axis : Fin 3) :
    (pub).column (Z).graph bitsOut (some (page axis)) (finProdFinEquiv (arg,node)) x=0:=by
  obtain ⟨height,groupId,space,seen,known⟩:=rows
  have nonempty : 0<batches:=Nat.div_pos (Nat.le_of_dvd positive whole) hp
  exact GroupStage.measured_tree_absent_cast (A) S input.valid (S.resetInputDigits ctl.base ctl.radix i) input.order groupId input.vertex space
    (Z) (T) B.frame input.grain.symm input.edges.symm B.count_eq seen (Z).k B.keyWidth (pub) s t x known.packet
    p hp nonempty unitFit cell node (by change Fintype.card ((Z).laneRecipe (DescentOrderedReset.grains W B.count input.order) batches p hp unitFit (venue cell)).Node ≤ node.val; simpa only [B.order_eq] using absent) active shapeRead arg bitsOut axis

include positive whole s t in
theorem observed_tree_absent_at (calendar : ℕ) (scheduled : batches=calendar)
    (cell : Physical.Site (bk).height) (node : Fin nodes) (absent : Fintype.card (gateAt cell).Node≤node.val)
    (x : (publicOperandConfig B field query lanes calendar batches nodes args grain).Data (Z).n)
    (rows : FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes)
      (args:=args) (grain:=grain) B s t x)
    (active : (header x 0).val≠0)
    (shapeRead : (header x 2).val=(DescentDenseHostOrder.localRank (Z).graph r Ht (here cell)).val)
    (arg : Fin args) (bitsOut : ℕ) (axis : Fin 3) :
    (publicOperandConfig B field query lanes calendar batches nodes args grain).column (Z).graph bitsOut
      (some (page axis)) (finProdFinEquiv (arg,node)) x=0:=by
  subst calendar
  exact observed_tree_absent B hp positive whole s t cell node absent x rows active shapeRead arg bitsOut axis

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
