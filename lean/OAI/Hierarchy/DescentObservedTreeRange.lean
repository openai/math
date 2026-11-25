import OAI.Hierarchy.DescentTreeOperandReply
import OAI.Hierarchy.DescentFreshTreeRange
import OAI.Hierarchy.DescentObservedFallbackCells

namespace OAI
/-! # Fresh range digits from the actually attained packet at every fallback level -/
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
set_option maxHeartbeats 1600000

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

theorem issued_tree_operands (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
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
    (arg : Fin sample.args) (slot : Fin sample.nodes)
    (numbered : slot.val=(DescentOrderedWords.before
      (Contact.cellKey (ids side t) (spatial side t) l.val (cellPrefix side t l e)) ⟨e,rfl⟩).card*sample.batches+b.val)
    :
    let q:=chosenNode side t l e
    let P:=measuredProgram sample p hp side t q
    let device:=DescentFixedExceptionalRouter.device d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
      (fun _=>sample.batches*p) side (.inr t) (book side t).codes
    let mul:=word_multiple d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
      (surface sample) p side (.inr t) (book side t).codes q
    let old:=(surface sample).basic x
    let xs:=(cfg sample.oldConfig).rowsAt old side (tkt t) (addr t) (num t)
    let leaf:=(book side t).codes (linkAt side t e)
    let gate:=P.op (⟨e,rfl⟩,b)
    (surface sample).mixed Z.graph slot.val arg.val x=
      (cfg sample.oldConfig).physicalReply side (((cfg sample.oldConfig).header old 1).val)
        (heightAt side t) (List.ofFn (cellPrefix side t l e)) (tkt t) xs (start Ht leaf)
        (gate.arg (0 : Fin 2)) (gate.arg (1 : Fin 2)) arg.val ∧
    ∀(bitsOut : ℕ) (f₀ : Fin 3),(surface sample).column Z.graph bitsOut (some (page f₀)) (finProdFinEquiv (arg,slot)) x=
        ((DescentRetainedRangeDigits.atSlot (ofProgram (fun a=>DescentKernelHistory.boundaryWidth device q a/p) mul hp P)
          (⟨e,rfl⟩,b) arg.val f₀ : ℕ) : DescentSIMDLookup.Cell bitsOut) :=by
  intro rawNode rawProgram rawDevice widthMultiple inputData inputRows hashedLeaf rowGate
  let mul:=word_multiple d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
    (surface sample) p side (.inr t) (book side t).codes (chosenNode side t l e)
  let old:=(surface sample).basic x
  let xs:=(cfg sample.oldConfig).rowsAt old side (tkt t) (addr t) (num t)
  let cells:=fun l : Fin ((heightAt side t)+1)=>rows Ht (List.ofFn (cellPrefix side t l e)) xs
  let leaf:=(book side t).codes (linkAt side t e)
  let j:=row side e.val
  obtain ⟨amount,landed,all⟩:=issued_fallback_cells A S ready digits order grp vertex padded Z T frm snap
    sample.oldConfig side t old packet hostRead groupWord fineWord indexed sorted e sample.batches b
  have positive : 0<sample.batches:=Nat.zero_lt_of_lt b.isLt
  have phase : slot.val%sample.batches=b.val:=by rw [numbered];simp [Nat.add_mod,Nat.mod_eq_of_lt b.isLt]
  have sole : Subsingleton (InputId Z.placement.site side (.inr t)) :=
    DescentChosenRouter.fallback_root (H:=Z.Fallback) (Y:=2^Z.n) Z.placement.b Z.placement.keys Z.placement.hub side t
  have complete (u : Fin ((heightAt side t)+1)) :
      (cells u).card = Fintype.card (Cell (spatial side t) u.val (cellPrefix side t u e)) ∧
      rank xs (cells u) j = (DescentOrderedWords.before
        (Contact.cellKey (ids side t) (spatial side t) u.val (cellPrefix side t u e)) ⟨e,rfl⟩).card :=
    ⟨(all u).1,(all u).2.1⟩
  have lanes:=paired_words (depth:=(book side t).height) (n:=∑ i,A.grainCount i)
    (I:=(W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)).graph.Edge)
    (C:=Z.placement.Contact) (R:=Z.placement.Public) (W:=Z.placement.Site) d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
    Z.placement.align (cfg sample.oldConfig) p hp side (.inr t) (book side t).codes chron (2^Z.n) e b xs cells j
    slot.val phase sole (fun u => by
    let X := Cell (spatial side t) u.val (cellPrefix side t u e)
    let ordinal := Contact.cellKey (ids side t) (spatial side t) u.val (cellPrefix side t u e)
    let selected : X := ⟨e,rfl⟩
    refine ⟨((complete u).1).trans ?_,((complete u).2).trans ?_⟩
    · exact congrArg (@Fintype.card X) (Subsingleton.elim _ _)
    · exact congrArg (fun inst : Fintype X =>
        (@DescentOrderedWords.before X inst _ ordinal selected).card) (Subsingleton.elim _ _)) l
  have room : DescentFallbackPeriod.rootCell r Z.n (tkt t)<DescentFallbackShapeTable.rows r (2^Z.n):=(addr t).isLt
  have finId : (⟨_,room⟩ : Fin (DescentFallbackShapeTable.rows r (2^Z.n)))=addr t:=rfl
  have amountAt : DescentFallbackPeriod.score ((surface sample).oldConfig.packet ((surface sample).basic x))
      (addr t,0,addr t) = num t := amount
  have actualDepth : min Ht (heightAt side t)=heightAt side t:=Nat.min_eq_right (T.bookHeight side t)
  have actualCount : min Ht (Nat.clog 2 (num t))=Nat.clog 2 (num t):=by
    simpa only [←T.leaves.depth side t] using actualDepth
  constructor
  · rw [(surface sample).tree_dispatch Z.graph slot.val arg.val x side (tkt t) (List.ofFn (cellPrefix side t l e))
        (act side t l e) active shapeRead (Z.installed_tree_shape T side t _) room,finId,amount,←T.leaves.depth side t,actualDepth]
    apply DescentFallbackOperandBranch.Config.make_reply (cfg sample.oldConfig) side _ _ _ (tkt t) xs (start Ht leaf)
      _ _ j slot.val arg.val positive
    · rw [numbered]
      exact (all l).2.2.1
    · exact landed
    · exact lanes.1
    · have nextRows :=(all l).2.2.2
      rw [←T.leaves.depth side t] at nextRows
      rw [nextRows]
      exact lanes.2
  · intro bitsOut f₀
    apply fresh_range d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner Z.placement.align
      Z.graph (surface sample) p hp side (.inr t) (book side t).codes chron (2^Z.n) (chosenNode side t l e)
      (⟨e,rfl⟩,b) mul x arg slot (tkt t) (List.ofFn (cellPrefix side t l e)) (act side t l e)
      active shapeRead (Z.installed_tree_shape T side t _) room positive j (start Ht leaf) f₀ bitsOut
    · rw [finId,amountAt,numbered]
      exact (all l).2.2.1
    · rw [finId,amountAt]
      exact landed
    · rw [finId,amountAt]
      exact lanes.1
    · rw [finId,amountAt,actualCount,(all l).2.2.2]
      exact lanes.2

theorem issued_tree_range (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
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
    (arg : Fin sample.args) (slot : Fin sample.nodes)
    (numbered : slot.val=(DescentOrderedWords.before
      (Contact.cellKey (ids side t) (spatial side t) l.val (cellPrefix side t l e)) ⟨e,rfl⟩).card*sample.batches+b.val)
    (bitsOut : ℕ) (f₀ : Fin 3) :
    let q:=chosenNode side t l e
    let P:=measuredProgram sample p hp side t q
    let device:=DescentFixedExceptionalRouter.device d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
      (fun _=>sample.batches*p) side (.inr t) (book side t).codes
    let mul:=word_multiple d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
      (surface sample) p side (.inr t) (book side t).codes q
    (surface sample).column Z.graph bitsOut (some (page f₀)) (finProdFinEquiv (arg,slot)) x=
        ((DescentRetainedRangeDigits.atSlot (ofProgram (fun a=>DescentKernelHistory.boundaryWidth device q a/p) mul hp P)
          (⟨e,rfl⟩,b) arg.val f₀ : ℕ) : DescentSIMDLookup.Cell bitsOut) :=
  (issued_tree_operands A S ready digits order grp vertex padded Z T frm snap sample side t x packet hostRead
    groupWord fineWord indexed sorted e b p hp l active shapeRead arg slot numbered).2 bitsOut f₀

theorem issued_tree_digits (sample : DescentResetPublicOperandBook.Config) (side : Bool) (t : Z.Fallback)
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
    (arg : Fin sample.args) (slot : Fin sample.nodes)
    (numbered : slot.val=(DescentOrderedWords.before
      (Contact.cellKey (ids side t) (spatial side t) l.val (cellPrefix side t l e)) ⟨e,rfl⟩).card*sample.batches+b.val)
    (bitsOut : ℕ) (printRoom : 2<2^bitsOut) (f₀ : Fin 3) :
    let q:=chosenNode side t l e
    let P:=measuredProgram sample p hp side t q
    let device:=DescentFixedExceptionalRouter.device d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
      (fun _=>sample.batches*p) side (.inr t) (book side t).codes
    let mul:=word_multiple d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner
      (surface sample) p side (.inr t) (book side t).codes q
    ((surface sample).column Z.graph bitsOut (some (page f₀)) (finProdFinEquiv (arg,slot)) x).val=
      DescentRetainedRangeDigits.atSlot (ofProgram (fun a=>DescentKernelHistory.boundaryWidth device q a/p) mul hp P)
          (⟨e,rfl⟩,b) arg.val f₀ :=by
  have issued:=issued_tree_operands A S ready digits order grp vertex padded Z T frm snap sample side t x packet hostRead
    groupWord fineWord indexed sorted e b p hp l active shapeRead arg slot numbered
  apply (surface sample).column_nat Z.graph x arg slot f₀ _ bitsOut _ printRoom (fun b=>issued.2 b f₀)
  rw [issued.1]
  apply DescentFallbackOperandBranch.Config.physical_range_le
  · exact stride_one d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner Z.placement.align
      sample.batches p hp side (.inr t) (book side t).codes chron (2^Z.n) (chosenNode side t l e) (⟨e,rfl⟩,b) (0 : Fin 2)
  · exact stride_one d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner Z.placement.align
      sample.batches p hp side (.inr t) (book side t).codes chron (2^Z.n) (chosenNode side t l e) (⟨e,rfl⟩,b) (1 : Fin 2)


end
end Hierarchy.DescentSixParty.GroupStage

end OAI
