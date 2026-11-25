import OAI.Hierarchy.DescentMeasuredOperandLeaf
import OAI.Hierarchy.DescentMeasuredOperandDigits
import OAI.Hierarchy.DescentFallbackItemChronology

namespace OAI
/-! # Actual old-word selection inside a reached fallback tree cell -/
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

private theorem measured_keys (sample : DescentFallbackOperandBranch.Config) (side : Bool) (t : Z.Fallback)
    (x : (cfg sample).Data Z.n)
    (packet : (cfg sample).packet x=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      snap.stencil snap.peers snap.marks (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (hostRead : ((cfg sample).header x 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A vertex (whereHost t)) (vertex (whereHost t)).val)
      (decide (whereHost t∉A.near (whereHost t))))
    (groupWord : ∀e : item side t,((cfg sample).digit x (row side e.val) 0).val=
      compress (groupDomain digits frm.basis fit (whereHost t) (hiAt t)) (A.pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item side t,((cfg sample).digit x (row side e.val) 1).val=(A.block (W.graph.src e.val.1)).val)
    : ∀a : item side t,((cfg sample).rowsAt x side (tkt t) (addr t) (num t) (row side a.val)).key=
      ⟨sourceDigit A digits frm.basis fit vertex (whereHost t) (hiAt t) a.val,
        (outgoingSlot A S ready order a.val).val,a.val.2.val⟩ := by
  intro a
  rw [show ((cfg sample).rowsAt x side (tkt t) (addr t) (num t) (row side a.val)).key=_ from
      (cfg sample).rowsAt_key x side (tkt t) (addr t) (num t) (row side a.val)]
  rw [packet,Equiv.symm_apply_apply]
  exact DescentMeasuredOperandKey.key_in_packet A S ready digits frm.basis fit native grp vertex pad
      snap.stencil snap.peers snap.marks (fun u j=>(ranks u j).val) snap.markRead snap.signedFits
      side a.val (whereHost t) (hiAt t) (falls_parameters A S ready digits Z T frm a.property)
      _ _ _ hostRead (groupWord a) (fineWord a)

/-- Number the genuine selected signed row by its original source and occupied
slot, then read the item at the original grain's chronological batch. -/
theorem issued_measured_item (sample : DescentFallbackOperandBranch.Config) (side : Bool) (t : Z.Fallback)
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
    (sorted : SourceSorted W order) (depth : ℕ) (ok : depth≤(book side t).height)
    (path : DescentTreePrefixIntervals.Bits depth) (e : Cell (spatial side t) depth path) (M : ℕ) (batch : Fin M) :
    let rowsAt:=(cfg sample).rowsAt x side (tkt t) (addr t) (num t)
    let printed:=(Finset.univ.filter (fun j : Cell (spatial side t) depth path=>chron j.val.val<chron e.val.val)).card*M+batch.val
    select rowsAt (rows Ht (List.ofFn path) rowsAt) (printed/M)=some (row side e.val.val) := by
  intro rowsAt printed
  apply issued_fallback_item A S ready digits native Z T frm vertex indexed order sorted
    side t depth ok path rowsAt _ _ e M batch
  · exact measured_keys A S ready digits order grp vertex padded Z T frm snap sample side t x packet hostRead groupWord fineWord
  · exact rowsAt_leaf A S ready digits native grp pad Z T frm snap sample side t x packet

/-- Exact live row count and count of earlier grains in any measured tree cell. -/
theorem issued_measured_rank_card (sample : DescentFallbackOperandBranch.Config) (side : Bool) (t : Z.Fallback)
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
    (sorted : SourceSorted W order) (depth : ℕ) (ok : depth≤(book side t).height)
    (path : DescentTreePrefixIntervals.Bits depth) (e : Cell (spatial side t) depth path) :
    let xs:=(cfg sample).rowsAt x side (tkt t) (addr t) (num t)
    let live:=rows Ht (List.ofFn path) xs
    live.card=Fintype.card (Cell (spatial side t) depth path) ∧
      rank xs live (row side e.val.val)=
        (Finset.univ.filter (fun j : Cell (spatial side t) depth path=>chron j.val.val<chron e.val.val)).card := by
  intro xs live
  have read:=rowsAt_leaf A S ready digits native grp pad Z T frm snap sample side t x packet
  let eqv:=fallbackCellEquiv A S ready digits native Z T frm side t depth ok path xs read
  let old : Cell (spatial side t) depth path ↪ Fin _ :=
    (Function.Embedding.subtype _).trans ((Function.Embedding.subtype _).trans chron)
  have ordered:=fallback_cell_order A S ready digits native Z T frm vertex indexed order sorted side t depth path xs
    (measured_keys A S ready digits order grp vertex padded Z T frm snap sample side t x packet hostRead groupWord fineWord)
  exact ⟨(Fintype.card_coe live).symm.trans (Fintype.card_congr eqv.symm),
    rank_of_equiv xs live eqv old ordered e⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
