import OAI.Hierarchy.DescentInstalledTreeRead

namespace OAI
/-! # All fields of every installed node in an exceptional reset tree -/
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentContactTree DescentRouterSlots DescentOrderedWords DescentBatchedBank DescentBundleHistory
open DescentRetainedRangeDigits DescentPhysicalSplit
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
  (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
  (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "selection" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align selection D
local notation "programAt" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D selection
local notation "ord" => DescentBatchedNodeOrder.sizedOrder G hw m p hp P.contact P.input P.site P.owner P.align key D u fit selection
variable (s : Bool) (t : H)
local notation "book" => P.fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (P.fallbackBook s t).codes (link P.contact P.owner s (.inr t))
local notation "ids" => DescentOrderedReset.itemKey key P.contact P.owner s (.inr t)
variable (q : Physical.Site (P.fallbackBook s t).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : (bank).Site)
local notation "raw" => DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (.inr t) (P.fallbackBook s t).codes
local notation "rawOp" => DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align m p hp s (.inr t) (P.fallbackBook s t).codes key (2^n) q


/-- Every node of this actual placed bank consists of one item in its prefix and
one physical batch. At a vertex with no such item the node type is empty. -/
theorem installedTreeGate_cases (node : (programAt venue).Node) :
    ∃(e : Cell code q.1.val q.2) (b : Fin m),
      installedTreeGate P G hw pay hardware key D m p hp fit s t q e b=node :=by
  subst u
  exact ⟨node.1,node.2,rfl⟩

end
end Hierarchy.DescentChosenRouter

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
set_option maxHeartbeats 1400000

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
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "cfg" sample:arg => ({sample with
  oldDegree := A.degree
  oldCap := A.cap
  donors := L
  fineBits := k
  fieldBits := field
  residual := r
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)
local notation "tkt" t:arg => (Z.fallLabel T t,(T.code t).2.2)
local notation "addr" t:arg => chartShape A S ready Z T t
local notation "num" t:arg => (T.leaves.window (shortName c (T.code t))).card
local notation "whereHost" t:arg => frm.host.symm (T.code t).1
local notation "hiAt" t:arg => selectedRoot A S ready Z T t
local notation "ranks" => DescentSharedBookScan.ranks (a:=r) (Y:=2^Z.n) (D:=A.degree) snap.chart (2^Ht) (Ht+2) snap.memory
local notation "item" s:arg t:arg => DescentRouterSlots.Item Z.placement.contact Z.placement.owner s (.inr t)
local notation "book" s:arg t:arg => Z.placement.fallbackBook s t
local notation "spatial" s:arg t:arg => DescentFixedNamedContact.code (book s t).codes
  (DescentRouterSlots.link Z.placement.contact Z.placement.owner s (.inr t))
local notation "row" s:arg e:arg => finProdFinEquiv (localAddress A native S ready digits frm.basis («c»:=c) s e)
local notation "chron" => DescentOrderedReset.grains W A.grainCount order


local notation "heightAt" s:arg t:arg => (book s t).height
local notation "linkAt" s:arg t:arg e:arg => DescentRouterSlots.link Z.placement.contact Z.placement.owner s (.inr t) e
local notation "cellPrefix" s:arg t:arg l:arg e:arg => prefixAt (spatial s t) (l).val e
local notation "ids" s:arg t:arg => itemKey chron Z.placement.contact Z.placement.owner s (.inr t)


local notation "surface" sample:arg => ({sample with oldConfig:=cfg (sample).oldConfig}:DescentResetPublicOperandBook.Config)
local notation "chosenNode" side:arg t:arg l:arg e:arg => (⟨l,cellPrefix side t l e⟩ : Physical.Site (heightAt side t))
local notation "measuredProgram" sample:arg p:arg hp:arg side:arg t:arg q:arg => DescentTreeLaneProgram.program d Z.placement.contact
  Z.placement.input Z.placement.site Z.placement.owner Z.placement.align (sample).batches p hp side (.inr t)
  (book side t).codes chron (2^Z.n) q
local notation "act" s:arg t:arg l:arg e:arg => Z.localShape T (Z.placed T (Z.privateSiteAt T s (.inr t) (chosenNode s t l e)))


local notation "receiverAt" s:arg t:arg l:arg e:arg => (⟨(s,.inr t),chosenNode s t l e⟩ : Z.bank.Site)
local notation "gateAt" m:arg p:arg hp:arg eqn:arg s:arg t:arg l:arg e:arg b:arg => DescentChosenRouter.installedTreeGate (K:=F) (C₀:=C) (k:=Z.k) (n:=Z.n) (h:=h) (bits:=Z.width) (u:=Z.unit) (N:=∑ x,A.grainCount x) Z.placement Z.graph
  Z.positive Z.pay Z.circuit chron d m p hp eqn s t (chosenNode s t l e) (⟨e,rfl⟩) b


local notation "atTree" side:arg t:arg vertex₁:arg => (⟨(side,.inr t),vertex₁⟩ : Z.bank.Site)
local notation "actorOf" side:arg t:arg vertex₁:arg => Z.localShape T (Z.placed T (Z.privateSiteAt T side (.inr t) vertex₁))

theorem measured_tree_range (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
    (x : (surface sample).Data Z.n)
    (packet : (cfg sample.oldConfig).packet ((surface sample).basic x)=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      snap.stencil snap.peers snap.marks (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
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
  classical
  rcases q₀ with ⟨l,loc₀⟩
  obtain ⟨⟨e,prefixAtSite⟩,b,rfl⟩:=installedTreeGate_cases (K:=F) (C₀:=C) (k:=Z.k) (n:=Z.n) (h:=h) (bits:=Z.width) (u:=Z.unit) (N:=∑ x,A.grainCount x) Z.placement Z.graph Z.positive Z.pay Z.circuit
    chron d sample.batches p hp unitFit side t ⟨l,loc₀⟩ node
  change cellPrefix side t l e = loc₀ at prefixAtSite
  subst loc₀
  have gateNumber:=installedTreeIndex (K:=F) (C₀:=C) (k:=Z.k) (n:=Z.n) (h:=h) (bits:=Z.width) (u:=Z.unit) (N:=∑ x,A.grainCount x) Z.placement Z.graph Z.positive Z.pay Z.circuit chron d sample.batches
    p hp unitFit side t (chosenNode side t l e) ⟨e,rfl⟩ b
  have raw:=issued_tree_digits A S ready digits order grp vertex padded Z T frm snap sample side t x packet
    hostRead groupWord fineWord indexed sorted e b p hp l active shapeRead arg slot (numbered.trans gateNumber)
    bitsOut printRoom f₀
  have measured:=word_multiple d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
    (surface sample) p side (.inr t) (book side t).codes (chosenNode side t l e)
  exact raw.trans (Z.reached_tree_range chron sample.batches p hp unitFit side t (chosenNode side t l e)
    ⟨e,rfl⟩ b measured arg.val f₀).symm

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
