import OAI.Hierarchy.DescentMeasuredFallbackSelection
import OAI.Hierarchy.DescentFallbackFlatChild
import OAI.Hierarchy.DescentPairedTreeLanes

namespace OAI
/-! # Every level of the fallback packet read from the issued root -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentRelativeContacts
open DescentPackedFallbackTree DescentFallbackItemSelect DescentStageEdgeReceipt
open DescentOrderedReset DescentOrderedWords DescentFallbackRankRAM DescentSharedBookScan DescentRosterOrder DescentPackedLeafSelector
open DescentSharedLeafLookup DescentGroupPeerOrder DescentPlainTerminal DescentPlainTerminal.Suffix
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000

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

theorem issued_fallback_cells (sample : DescentFallbackOperandBranch.Config) (side : Bool) (t : Z.Fallback)
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
    (sorted : SourceSorted W order) (e : item side t) (M : ℕ) (b : Fin M) :
    let xs:=(cfg sample).rowsAt x side (tkt t) (addr t) (num t)
    let leaf:=(book side t).codes (linkAt side t e)
    let cells:=fun l : Fin ((heightAt side t)+1)=>rows Ht (List.ofFn (cellPrefix side t l e)) xs
    let j:=row side e.val
    DescentFallbackPeriod.score ((cfg sample).packet x) (addr t,0,addr t)=num t ∧
    (xs j).leaf=some (start Ht leaf) ∧
    ∀l : Fin ((heightAt side t)+1),
      let old:=DescentOrderedWords.before (Contact.cellKey (ids side t) (spatial side t) l.val (cellPrefix side t l e)) ⟨e,rfl⟩
      (cells l).card=Fintype.card (Cell (spatial side t) l.val (cellPrefix side t l e)) ∧
      rank xs (cells l) j=old.card ∧
      select xs (cells l) ((old.card*M+b.val)/M)=some j ∧
      (if (List.ofFn (cellPrefix side t l e)).length=Nat.clog 2 (num t) then cells l else
       rows Ht (DescentFallbackOperandBranch.Config.childPath Ht (List.ofFn (cellPrefix side t l e)) (start Ht leaf)) xs)=
        cells (DescentTreeLaneProgram.nextLevel l) :=by
  classical
  intro xs leaf cells j
  constructor
  · have truthful:=window_input (field:=field) A S ready digits native Z T frm grp pad snap.word ranks
      snap.stencilRead snap.rosterRead snap.markRead (whereHost t) (Z.rootBlock T (.inr t))
    have amountRead:=measured_amount A S ready digits Z T frm pad
      snap.n snap.f snap.B snap.wire snap.K snap.wt snap.flow snap.roster snap.chart snap.memory snap.cutoff
      snap.header snap.room snap.layouts snap.old snap.hubs snap.pos snap.heightFits snap.available side t
    change (choose _ (DescentSharedBookScan.ticket (addr t,0,addr t)) _).val=_ at amountRead
    rw [choose_ticket] at amountRead
    rw [packet,truthful]
    exact (window_rank A S ready digits native Z T frm grp pad snap.word ranks snap.countFits _ _ _).trans amountRead
  constructor
  · have atRow:=rowsAt_leaf A S ready digits native grp pad Z T frm snap sample side t x packet j
    have orig:=fallbackPanel_at A S ready digits native Z T frm side t e.val e.property
    rw [atRow]
    have member : A.falls S ready Z side t e.val := e.property
    simp only [leafPanel,j,Equiv.symm_apply_apply,orig]
    change (A.arrivedLeaf S ready Z T side t e.val).map Fin.val = _
    unfold arrivedLeaf
    rw [dite_eq_left member]
    rfl
  intro l old
  have bound (l : Fin ((heightAt side t)+1)) : l.val≤heightAt side t:=Nat.le_of_lt_succ l.isLt
  have pathRead (l : Fin ((heightAt side t)+1)) : cellPrefix side t l e=cut (bound l) leaf:=by
    funext n
    have small:=lt_of_lt_of_le n.isLt (bound l)
    simp [cut,prefixAt,DescentFixedNamedContact.code,small,leaf]
    rfl
  have full:=issued_measured_rank_card A S ready digits order grp vertex padded Z T frm snap sample side t x
    packet hostRead groupWord fineWord indexed sorted l.val (bound l) (cellPrefix side t l e) ⟨e,rfl⟩
  refine ⟨full.1,full.2,?_,?_⟩
  · exact issued_measured_item A S ready digits order grp vertex padded Z T frm snap sample side t x
      packet hostRead groupWord fineWord indexed sorted l.val (bound l) (cellPrefix side t l e) ⟨e,rfl⟩ M b
  · induction l using Fin.lastCases with
    | last=>simp [DescentTreeLaneProgram.nextLevel,T.leaves.depth side t]
    | cast z=>
      have child:=child_path z.isLt (T.bookHeight side t) leaf
      simp only [List.length_ofFn,←T.leaves.depth side t,Fin.val_castSucc,ite_eq_right (Nat.ne_of_lt z.isLt),
        DescentTreeLaneProgram.nextLevel,Fin.lastCases_castSucc]
      change rows Ht (DescentFallbackOperandBranch.Config.childPath Ht
        (List.ofFn (cellPrefix side t z.castSucc e)) (start Ht leaf)) xs=
        rows Ht (List.ofFn (cellPrefix side t z.succ e)) xs
      rw [pathRead z.castSucc,pathRead z.succ,child]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
