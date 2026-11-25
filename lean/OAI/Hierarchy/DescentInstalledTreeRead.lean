import OAI.Hierarchy.DescentObservedTreeRange
import OAI.Hierarchy.DescentNumberedFallbackNode

namespace OAI
/-! # Directly reading an installed physical fallback gate at its funded node number -/
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

theorem installed_tree_digits (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
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
    (sorted : SourceSorted W order) (e : item side t) (b : Fin sample.batches) (p : ℕ) (hp : 0<p)
    (l : Fin ((heightAt side t)+1))
    (active : ((cfg sample.oldConfig).header ((surface sample).basic x) 0).val≠0)
    (shapeRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 2).val=
      (DescentDenseHostOrder.localRank Z.graph r Ht (act side t l e)).val)
    (unitFit : Z.unit=sample.batches*p)
    (budget : (2*DescentNetworkSubstitution.portLoad Z.bank (receiverAt side t l e))/p≤ sample.nodes)
    (arg : Fin sample.args) (bitsOut : ℕ) (printRoom : 2<2^bitsOut) (f₀ : Fin 3) :
    let slot:=Z.numberedTreeGate chron sample.batches p hp unitFit side t (chosenNode side t l e) ⟨e,rfl⟩ b budget
    let sh:=Z.laneShape chron sample.batches p hp unitFit (receiverAt side t l e)
    let gate:=gateAt sample.batches p hp unitFit side t l e b
    ((surface sample).column Z.graph bitsOut (some (page f₀)) (finProdFinEquiv (arg,slot)) x).val=
      atSlot sh gate arg.val f₀ :=by
  let slot:=Z.numberedTreeGate chron sample.batches p hp unitFit side t (chosenNode side t l e) ⟨e,rfl⟩ b budget
  have numbered:=Z.numbered_tree_gate chron sample.batches p hp unitFit side t (chosenNode side t l e) ⟨e,rfl⟩ b budget
  have raw:=issued_tree_digits A S ready digits order grp vertex padded Z T frm snap sample side t x packet hostRead
    groupWord fineWord indexed sorted e b p hp l active shapeRead arg slot numbered bitsOut printRoom f₀
  have measured:=word_multiple d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
    (surface sample) p side (.inr t) (book side t).codes (chosenNode side t l e)
  exact raw.trans (Z.reached_tree_range chron sample.batches p hp unitFit side t (chosenNode side t l e)
    ⟨e,rfl⟩ b measured arg.val f₀).symm

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
