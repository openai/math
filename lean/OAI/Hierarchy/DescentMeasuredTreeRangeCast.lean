import OAI.Hierarchy.DescentMeasuredTreeRange

namespace OAI
/-! # Fallback range with the recorded original input width -/
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
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (filled W.graph A.pos A.block digits) A.hub g)
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
local notation "chron" => DescentOrderedReset.grains W A.grainCount order

local notation:max "heightAt" s:arg t:arg => (book s t).height
local notation:max "surface" sample:arg => ({sample with oldConfig:=cfg (sample).oldConfig}:DescentResetPublicOperandBook.Config)
local notation:max "atTree" side:arg t:arg vertex₁:arg => (⟨(side,.inr t),vertex₁⟩ : Z.bank.Site)
local notation:max "actorOf" side:arg t:arg vertex₁:arg => Z.localShape T (Z.placed T (Z.privateSiteAt T side (.inr t) vertex₁))

theorem measured_tree_range_cast (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
    (x : (surface sample).Data Z.n)
    (packet : (cfg sample.oldConfig).packet ((surface sample).basic x)=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      (fun v hi lo=>snap.stencil v hi (lo.cast (congrArg (fun l=>2^(l-c)) extent))) snap.peers
      (fun v hi lo=>snap.marks v hi (lo.cast (congrArg (fun l=>2^(l-c)) extent))) (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (hostRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A vertex (whereHost t)) (vertex (whereHost t)).val)
      (decide (whereHost t∉A.near (whereHost t))))
    (groupWord : ∀e : item side t,((cfg sample.oldConfig).digit ((surface sample).basic x) (row side e.val) 0).val=
      compress (groupDomain digits frm.basis fit (whereHost t) (hiAt t)) (A.pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item side t,((cfg sample.oldConfig).digit ((surface sample).basic x) (row side e.val) 1).val=(A.block (W.graph.src e.val.1)).val)
    (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (sorted : SourceSorted W order) (p : ℕ) (hp : 0<p) (unitFit : Z.unit=sample.batches*p)
    (q₀ : Physical.Site (heightAt side t))
    (node : (Z.laneRecipe chron sample.batches p hp unitFit (atTree side t q₀)).Node)
    (active : ((cfg sample.oldConfig).header ((surface sample).basic x) 0).val≠0)
    (shapeRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 2).val=
      (DescentDenseHostOrder.localRank Z.graph r Ht (actorOf side t q₀)).val)
    (slot : Fin sample.nodes)
    (numbered : slot.val=Z.nodeIndex chron sample.batches p hp unitFit (atTree side t q₀) node)
    (arg : Fin sample.args) (bitsOut : ℕ) (printRoom : 2<2^bitsOut) (f₀ : Fin 3) :
    ((surface sample).column Z.graph bitsOut (some (page f₀)) (finProdFinEquiv (arg,slot)) x).val=
      atSlot (Z.laneShape chron sample.batches p hp unitFit (atTree side t q₀)) node arg.val f₀ :=by
  subst effective
  exact measured_tree_range A S ready digits order grp vertex padded Z T frm snap sample side t x
    packet hostRead groupWord fineWord indexed sorted p hp unitFit q₀ node active shapeRead slot numbered arg bitsOut printRoom f₀

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
