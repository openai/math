import OAI.Hierarchy.DescentMeasuredTreeRange
import OAI.Hierarchy.DescentCalendarProducedOperand

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


theorem installedTreeGate_card :
    Fintype.card (programAt venue).Node=Fintype.card (Cell code q.1.val q.2)*m :=by
  subst u
  let α := Cell (DescentFixedNamedContact.code (P.fallbackBook s t).codes
    (link P.contact P.owner s (.inr t))) q.1.val q.2
  let gate := sizedProgram G hw (m*p) m p hp rfl P.contact P.input P.site P.owner P.align key D
    (selected P G hw pay hardware) ⟨(s,.inr t),q⟩
  calc
    @Fintype.card gate.Node gate.finite = Fintype.card (α × Fin m) :=
      @Fintype.card_congr gate.Node (α × Fin m) gate.finite inferInstance (Equiv.refl _)
    _ = _ := by rw [Fintype.card_prod, Fintype.card_fin]

end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentFallbackItemSelect DescentFallbackOperandQuery
open DescentDenseHostOrder DescentHostDirectory DescentResetLocalRoster DescentTreePrefixIntervals
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
theorem make_absent {n : ℕ} (C : DescentFallbackOperandBranch.Config) (s : Bool) (cap ht : ℕ)
    (ds : List Bool) (root : code C.residual×Option (Fin (2^n))) (items : Fin C.count→Item) (node arg : ℕ)
    (positive : 0<C.batches) (absent : (rows C.maxDepth ds items).card*C.batches≤node) :
    C.make s cap ht ds root items node arg=none :=by
  let live:=rows C.maxDepth ds items
  have dropped : select items live (node/C.batches)=none:=by
    apply dite_eq_right
    rintro ⟨j,member_,number⟩
    have rankSmall : rank items live j<live.card:=by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
      exact ⟨j,member_,fun h=>(by simpa [before,Key.irrefl] using (Finset.mem_filter.mp h).2 : False)⟩
    exact (Nat.not_lt_of_ge ((Nat.le_div_iff_mul_le positive).2 absent)) (number ▸ rankSmall)
  simp [make,show select items (rows C.maxDepth ds items) (node/C.batches)=none from dropped]
end
end Hierarchy.DescentFallbackOperandBranch.Config

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

theorem measured_tree_absent (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
    (x : (surface sample).Data Z.n)
    (packet : (cfg sample.oldConfig).packet ((surface sample).basic x)=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      snap.stencil snap.peers snap.marks (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (p : ℕ) (hp : 0<p) (positive : 0<sample.batches) (unitFit : Z.unit=sample.batches*p)
    (site : Physical.Site (heightAt side t)) (slot : Fin sample.nodes)
    (absent : Fintype.card (Z.laneRecipe chron sample.batches p hp unitFit (atTree side t site)).Node≤ slot.val)
    (active : ((cfg sample.oldConfig).header ((surface sample).basic x) 0).val≠0)
    (shapeRead : ((cfg sample.oldConfig).header ((surface sample).basic x) 2).val=
      (DescentDenseHostOrder.localRank Z.graph r Ht (actorOf side t site)).val)
    (arg : Fin sample.args) (bitsOut : ℕ) (axis : Fin 3) :
    (surface sample).column Z.graph bitsOut (some (page axis)) (finProdFinEquiv (arg,slot)) x=0 :=by
  classical
  let old:=(surface sample).basic x
  let xs:=(cfg sample.oldConfig).rowsAt old side (tkt t) (addr t) (num t)
  let live:=rows Ht (List.ofFn site.2) xs
  have leafRead:=rowsAt_leaf A S ready digits native grp pad Z T frm snap sample.oldConfig side t old packet
  let eqv:=fallbackCellEquiv A S ready digits native Z T frm side t site.1.val (Nat.le_of_lt_succ site.1.isLt)
    site.2 xs leafRead
  have cells : live.card=Fintype.card (Cell (spatial side t) site.1.val site.2):=
    (Fintype.card_coe live).symm.trans (Fintype.card_congr eqv.symm)
  have card:=installedTreeGate_card Z.placement Z.graph Z.positive Z.pay Z.circuit chron d sample.batches p hp
    unitFit side t site
  have dead : live.card*sample.batches≤ slot.val:=by rw [cells,←card];exact absent
  have amount : DescentFallbackPeriod.score ((cfg sample.oldConfig).packet old) (addr t,0,addr t)=num t:=by
    have truthful:=window_input (field:=field) A S ready digits native Z T frm grp pad snap.word ranks
      snap.stencilRead snap.rosterRead snap.markRead (whereHost t) (Z.rootBlock T (.inr t))
    have amountRead:=measured_amount A S ready digits Z T frm pad
      snap.n snap.f snap.B snap.wire snap.K snap.wt snap.flow snap.roster snap.chart snap.memory snap.cutoff
      snap.header snap.room snap.layouts snap.old snap.hubs snap.pos snap.heightFits snap.available side t
    change (choose _ (DescentSharedBookScan.ticket (addr t,0,addr t)) _).val=_ at amountRead
    rw [choose_ticket] at amountRead
    rw [packet,truthful]
    exact (window_rank A S ready digits native Z T frm grp pad snap.word ranks snap.countFits _ _ _).trans amountRead

  have room : DescentFallbackPeriod.rootCell r Z.n (tkt t)<DescentFallbackShapeTable.rows r (2^Z.n):=(addr t).isLt
  have finId : (⟨_,room⟩ : Fin (DescentFallbackShapeTable.rows r (2^Z.n)))=addr t:=rfl
  have counts : (surface sample).mixed Z.graph slot.val arg.val x=none:=by
    rw [(surface sample).tree_dispatch Z.graph slot.val arg.val x side (tkt t) (List.ofFn site.2)
      (actorOf side t site) active shapeRead (Z.installed_tree_shape T side t site) room,finId,amount]
    exact DescentFallbackOperandBranch.Config.make_absent (cfg sample.oldConfig) side _ _ _ _ xs slot.val arg.val positive dead
  simp [DescentResetPublicOperandBook.Config.column,counts]
end
end Hierarchy.DescentSixParty.GroupStage

end OAI
