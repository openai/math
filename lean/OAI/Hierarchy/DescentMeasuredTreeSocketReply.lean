import OAI.Hierarchy.DescentReachedRootRows
import OAI.Hierarchy.DescentObservedTreeRange

namespace OAI
/-! The observed fallback tuple with the reached old grain count and actual signed input width. -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentRelativeContacts
open DescentPackedFallbackTree DescentFallbackItemSelect DescentStageEdgeReceipt
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (grp : Fin groups↪ℕ) (vertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
local notation "native" => order.trans Fin.valEmbedding
local notation "pad" => vertex.trans (Fin.castLEEmb padded)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
variable (Z : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht) (T : Z.Terminals)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (snap : RootObservation A S ready digits (order.trans Fin.valEmbedding) grp (vertex.trans (Fin.castLEEmb padded)) Z T frm field)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
variable (effective : ℕ) (extent : effective=m)
local notation "L" => 2^(effective-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation:max "cfg" sample:arg => ({sample with
  oldDegree := A.degree
  oldCap := A.cap
  donors := L
  fineBits := k
  fieldBits := field
  residual := r
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)
local notation:max "tkt" t:arg => (Z.fallLabel T t,(T.code t).2.2)
local notation:max "addr" t:arg => Z.observedRootAddress T t
local notation:max "num" t:arg => (T.leaves.window (shortName c (T.code t))).card
local notation:max "whereHost" t:arg => frm.host.symm (T.code t).1
local notation:max "hiAt" t:arg => Z.rootBlock T (.inr t)
local notation "ranks" => DescentSharedBookScan.ranks (a:=r) (Y:=2^Z.n) (D:=A.degree) snap.chart (2^Ht) (Ht+2) snap.memory
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item Z.placement.contact Z.placement.owner s (.inr t)
variable (zEq : zz=A.z) (wireEq : ww=A.wire) (countEq : ct=A.grainCount)
local notation "asOld" => Equiv.sigmaCongrRight (fun a=>finCongr (congrFun countEq a))
local notation:max "oldPos" s:arg e:arg => localAddress A native S ready digits frm.basis («c»:=c) s (asOld e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((oldPos s e).1.cast (congrArg (fun l=>2^(l-c)) extent.symm)),(oldPos s e).2)
local notation "chron" => DescentOrderedReset.grains W ct order
open DescentNamedContact DescentOrderedReset

local notation:max "book" s:arg t:arg => Z.placement.fallbackBook s t
local notation:max "spatial" s:arg t:arg => DescentFixedNamedContact.code (book s t).codes
  (DescentRouterSlots.link Z.placement.contact Z.placement.owner s (.inr t))
open DescentKernelHistory DescentTreeLaneProgram DescentRotor DescentOrderedWords
local notation:max "heightAt" s:arg t:arg => (book s t).height
local notation:max "linkAt" s:arg t:arg e:arg => DescentRouterSlots.link Z.placement.contact Z.placement.owner s (.inr t) e
local notation:max "cellPrefix" s:arg t:arg l:arg e:arg => prefixAt (spatial s t) (l).val e
local notation:max "ids" s:arg t:arg => itemKey chron Z.placement.contact Z.placement.owner s (.inr t)


local notation:max "surface" sample:arg => ({sample with oldConfig:=cfg (sample).oldConfig}:DescentResetPublicOperandBook.Config)
local notation:max "chosenNode" side:arg t:arg l:arg e:arg => (⟨l,cellPrefix side t l e⟩ : Physical.Site (heightAt side t))
local notation:max "measuredProgram" sample:arg p:arg hp:arg side:arg t:arg q:arg => DescentTreeLaneProgram.program d Z.placement.contact
  Z.placement.input Z.placement.site Z.placement.owner Z.placement.align (sample).batches p hp side (.inr t)
  (book side t).codes chron (2^Z.n) q
local notation:max "act" s:arg t:arg l:arg e:arg => Z.localShape T (Z.placed T (Z.privateSiteAt T s (.inr t) (chosenNode s t l e)))

include zEq wireEq in
theorem observed_tree_reply_cast (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
    (x : (surface sample).Data Z.n)
    (packet : (cfg sample.oldConfig).packet ((surface sample).basic x)=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast (congrArg (fun len=>2^(len-c)) extent))) snap.peers (fun u hi lo=>snap.marks u hi (lo.cast (congrArg (fun len=>2^(len-c)) extent))) (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (hostRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A vertex (whereHost t)) (vertex (whereHost t)).val)
      (decide (whereHost t∉A.near (whereHost t))))
    (groupWord : ∀e : item side t,((cfg sample.oldConfig).digit ((surface sample).basic x) (row side e.val) 0).val=
      compress (groupDomain digits frm.basis fit (whereHost t) (hiAt t)) (A.pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item side t,((cfg sample.oldConfig).digit ((surface sample).basic x) (row side e.val) 1).val=(A.block (W.graph.src e.val.1)).val)
    (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (sorted : SourceSorted W order) (capRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 1).val=A.cap) (e : item side t) (b : Fin sample.batches) (p : ℕ) (hp : 0<p)
    (l : Fin ((heightAt side t)+1))
    (active : ((cfg sample.oldConfig).header ((surface sample).basic x) 0).val≠0)
    (shapeRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 2).val=
      (DescentDenseHostOrder.localRank Z.graph r Ht (act side t l e)).val)
    (arg : Fin sample.args) (slot : Fin sample.nodes)
    (numbered : slot.val=(DescentOrderedWords.before
      (Contact.cellKey (ids side t) (spatial side t) l.val (cellPrefix side t l e)) ⟨e,rfl⟩).card*sample.batches+b.val)
    :
    let q:=chosenNode side t l e
    let P:=measuredProgram sample p hp side t q
    let old:=(surface sample).basic x
    let xs:=(cfg sample.oldConfig).rowsAt old side (tkt t) (addr t) (num t)
    let leaf:=(book side t).codes (linkAt side t e)
    let gate:=P.op (⟨e,rfl⟩,b)
    (surface sample).mixed Z.graph slot.val arg.val x=
      (cfg sample.oldConfig).physicalReply side A.cap
        (heightAt side t) (List.ofFn (cellPrefix side t l e)) (tkt t) xs (start Ht leaf)
        (gate.arg (0 : Fin 2)) (gate.arg (1 : Fin 2)) arg.val :=by
  subst zz
  subst ww
  subst ct
  subst effective
  dsimp only
  have issued:=issued_tree_operands A S ready digits order grp vertex padded Z T frm snap sample side t x packet
    hostRead groupWord fineWord indexed sorted e b p hp l active shapeRead arg slot numbered
  apply Eq.trans issued.1
  congr 1

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
