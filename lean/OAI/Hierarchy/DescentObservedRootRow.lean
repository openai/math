import OAI.Hierarchy.DescentMeasuredFallbackLane

namespace OAI
/-! # The measured signed row at every original input of an exceptional root -/
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

open DescentNamedContact DescentOrderedReset
open private DescentTreeLaneProgram.rootCell DescentTreeLaneProgram.before_equiv
  from OAI.Hierarchy.DescentMeasuredFallbackLane

/-- The rank is the position in the full physical input fibre anchored at this
tree. A later covered word can select a different original grain from the gate's anchor. -/
theorem observed_root_row (sample : DescentFallbackOperandBranch.Config) (side : Bool) (t : Z.Fallback)
    (x : (cfg sample).Data Z.n)
    (packet : (cfg sample).packet x=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      snap.stencil snap.peers snap.marks (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (hostRead : ((cfg sample).header x 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A vertex (whereHost t)) (vertex (whereHost t)).val)
      (decide (whereHost t∉A.near (whereHost t))))
    (groupWord : ∀e : item side t,((cfg sample).digit x (row side e.val) 0).val=
      compress (groupDomain digits frm.basis fit (whereHost t) (hiAt t)) (A.pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item side t,((cfg sample).digit x (row side e.val) 1).val=(A.block (W.graph.src e.val.1)).val)
    (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (sorted : SourceSorted W order)
    (anchor : item side t) (e : Fibre (Z.placement.input side) (Z.placement.input side anchor.val)) :
    let xs:=(cfg sample).rowsAt x side (tkt t) (addr t) (num t)
    ∃ j : ↥(rows Ht [] xs),
      rank xs (rows Ht [] xs) j.val=
        (DescentOrderedWords.before (fibreKey chron (Z.placement.input side) (Z.placement.input side anchor.val)) e).card ∧
      (xs j.val).residual=(localAddress A native S ready digits frm.basis («c»:=c) side e.val).1.val ∧
      (xs j.val).signed=(localAddress A native S ready digits frm.basis («c»:=c) side e.val).2.val :=by
  classical
  intro xs
  let path:=prefixAt (spatial side t) 0 anchor
  let sole:=fallback_root (Y:=2^Z.n) Z.placement.b Z.placement.keys Z.placement.hub side t
  let perm:=DescentTreeLaneProgram.rootCell Z.placement.contact Z.placement.input Z.placement.site
    Z.placement.owner Z.placement.align side (.inr t) (book side t).codes sole anchor
  let donor:=perm.symm e
  have observed:=rowsAt_leaf A S ready digits native grp pad Z T frm snap sample side t x packet
  let atlas:=fallbackCellEquiv A S ready digits native Z T frm side t 0 (Nat.zero_le _) path xs observed
  let j : ↥(rows Ht [] xs):=atlas donor
  have same : j.val=row side e.val:=rfl
  have issued:=issued_measured_rank_card A S ready digits order grp vertex padded Z T frm snap sample
    side t x packet hostRead groupWord fineWord indexed sorted 0 (Nat.zero_le _) path donor
  let ids:=itemKey chron Z.placement.contact Z.placement.owner side (.inr t)
  let cellOrd:=DescentOrderedWords.Contact.cellKey ids (spatial side t) 0 path
  let fibreOrd:=fibreKey chron (Z.placement.input side) (Z.placement.input side anchor.val)
  have earlier:=DescentTreeLaneProgram.before_equiv perm cellOrd fibreOrd (fun _=>rfl) donor
  have compatible {I : Type} {N : ℕ} (one two : Fintype I) (orderAt : I ↪ Fin N) (x y : I) (sameAt : x=y) :
      (@DescentOrderedWords.before I one N orderAt x).card=(@DescentOrderedWords.before I two N orderAt y).card := by
    cases sameAt
    cases Subsingleton.elim one two
    rfl
  refine ⟨j,issued.2.trans (earlier.trans (compatible _ _ fibreOrd _ e (perm.apply_symm_apply e))),?_,?_⟩
  · rw [same]
    change (finProdFinEquiv.symm (row side e.val)).1.val=_
    rw [Equiv.symm_apply_apply]
  · rw [same]
    change (finProdFinEquiv.symm (row side e.val)).2.val=_
    rw [Equiv.symm_apply_apply]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
