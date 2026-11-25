import OAI.ThreeFlat.RAM.FoldRefreshCache
import OAI.ThreeFlat.RAM.HistoryMotifTariff

namespace OAI
/-! # Publishing the selected shrink into its chronological cache row -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Diagonal Diagonal.PhysicalStage
open Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage
open Diagonal.HistoryContraction Diagonal.NavigationPass Diagonal.ShrinkStageNav
open Diagonal.NavigationDirectory HistoryStageBody.Physical HistoryMotifJoin
open HistoryStageBody HistoryPartyBatchExec HistoryStageSetup HistoryWordStepRun NavigationNodeRows
open scoped Classical BigOperators Fin.CommRing
open private descriptorAllocation from OAI.ThreeFlat.RAM.HistoryShrinkArchive
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F Pins E : Type} [Field F] [Fintype F] (B : Block F) (level : Fin B.levels)
  {u rom K rem : ℕ}
local notation "W" => (16*u^10)
local notation "V" => volume u
local notation "s" => B.exponent level.val
local notation "D" => (2^B.exponent (level.val+1):ℕ)
local notation "d" => (2^s:ℕ)
local notation "S" => shrinkStage s D
local notation "family" => shrinkFamily B rom W level
local notation "arc" => archive B rom W K
local notation "J" => layout u arc family
local notation "tag₀" => (HistoryRefreshEmitter.tag (K:=F))
variable (hD : 0 < 2^(B.exponent (level.val+1)))
  (small : let degree : ℕ := 2^(B.exponent level.val)
    ((2^(2*degree+1)*degree*degree : ℕ) : ℝ) / ((2^(B.exponent (level.val+1)) : ℕ) : ℝ) ≤ 1/1024)
  (A : State (2^(B.exponent level.val)) (shrinkCharge (B.exponent level.val)+rem))
local notation "M" => shrinkBinary B.shrink s D rem hD small A
local notation "X" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
variable (branch : Fin (shrinkBinary B.shrink (B.exponent level.val)
    (2^(B.exponent (level.val+1))) rem hD small A).rules.count)
  {c : Cursor} (L : A.Words Pins)
  (z : ((shrinkBinary B.shrink (B.exponent level.val)
    (2^(B.exponent (level.val+1))) rem hD small A).next branch).Site)
local notation "step" => shrinkBinary_assembler B.shrink s D rem hD small A L branch
local notation "charge" => shrinkBinaryCharge B.shrink s D rem hD small A branch
local notation "dims₀" => Diagonal.CompressorPacking.Native.ShrinkStage.Resident.dims S
  (Fintype.card (X).Base) (Diagonal.CompressorPacking.tagBits d) rem
local notation "en" => allocate K c (.shrink dims₀)
local notation "lay" => ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
local notation "sites" => shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
local notation "rank₀" => (sites).ord z
local notation "idx" => (sites).id z
variable (v : Computability.VPVNP.Compression.Site (shrinkRecordState (B.exponent level.val) rem A).Base
    (BitWord (Diagonal.CompressorPacking.tagBits (2^(B.exponent level.val)))) (BitWord rem))
local notation "siteNo" => Incidents.siteNumber (X).order v

/-- The S44 half-directory supplies the new part of the literal positive-arm
arity after summing the genuine earlier children in their allocated order. -/
theorem recorded_new_bits {w n cap₀ d₀ l₀ : ℕ} {Y : State d₀ l₀} {sites₀ : Y.ArchiveSites}
    {safe : ℕ→Prop} {input : Memory w} (rows : State.HalfRows sites₀ safe (numeric input))
    (z₀ : Y.Site) (C : HistoryNodePorts.Layout) (T : HistoryStageRoot.Input)
    (oldBits : Fin n→ℕ) (future : ℕ)
    (current : numeric input C.cursor-1=T.id) (nodes : C.nodes=T.nodeBase) (cache : C.cache=T.resultBase)
    (count : HistoryStageRoot.childCount T (numeric input)=n) (enough : n≤cap₀)
    (cached : ∀i,HistoryStageRoot.oldHalf (HistoryStageRoot.atResult (numeric input)
      (HistoryStageRoot.childPtr T (numeric input) i.val))=oldBits i)
    (head : numeric input (HistoryStageRoot.node T+6)=sites₀.layer.incident+(sites₀.ord z₀).val*2)
    (root : childWidth C cap₀ (numeric input) (C.starts+cap₀)+Y.incidentWidth z₀=
      (∑i,oldBits i)+future) : HistoryStageRoot.halfWidth T (numeric input)=future := by
  have old := recorded_child_prefix C T input oldBits current nodes cache count cached n cap₀ le_rfl
  have nativeCount : numeric input (C.nodes+8*(numeric input C.cursor-1)+4)=n:=by rw [nodes,current];exact count
  have all : childWidth C cap₀ (numeric input) (C.starts+cap₀)=
      childWidth C cap₀ (numeric input) (C.starts+n):=by
    simp only [childWidth,Nat.add_sub_cancel_left,nativeCount,min_eq_right enough,min_self]
  have prior : childWidth C cap₀ (numeric input) (C.starts+cap₀)=∑i,oldBits i:=all.trans (by simpa using old)
  rw [prior] at root
  exact (HistoryStageSetup.stage_half sites₀ rows T z₀ head).trans (Nat.add_left_cancel root)

include B level hD small A branch z v in
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1600000 in
/-- Both guards use the pointer and the degree issued by this very shrink. -/
theorem recorded_dispatch {cur ctr : Word W} {before issued final input : Memory W} {heads : ℕ}
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (caps : ShrinkNativeCaps B.shrink s D rem W A) (bounds : RecordedArrayBounds W heads c A)
    (saved : SavedFrame cur ctr heads (en).next.header (en).next.heap issued final)
    (age : 16≤u) (controls : cur.val<ctr.val)
    (keep : ∀a,(c.header≤a ∧ a<c.header+64 ∨ heads≤a) → a<(en).next.heap → input a=final a)
    (b : Banks) (nodes : b.nodes=Diagonal.TickWorkspace.base u 44)
    (current : numeric input (Diagonal.TickWorkspace.base u 18)=idx+1)
    (kind : input (b.nodes+8*idx)=((sites).layer.kind:Word W))
    (dir : DirectoryRow b (sites).layer rank₀ input)
    (placed : (rank₀).val=siteNo) :
    (families B rom W).find? (matchesFamily u input)=some family ∧
      stageAddress u input+48<2^W := by
  let kernel : ℕ := (sites).layer.kernels+(rank₀).val*5
  have cursorAt : numeric input (Diagonal.TickWorkspace.base u 18)-1=idx := by
    simp only [current, Nat.add_sub_cancel]
  have addr : HistoryStageBody.Physical.nodeAddress u input=b.nodes+8*idx := by
    rw [nodes]
    exact congrArg (fun n : ℕ => Diagonal.TickWorkspace.base u 44+8*n) cursorAt
  have f34 : DescriptorSpan.fields K c dims₀ lay 34=(sites).layer.kernels :=
    (PhysicalStage.shrink_allocated_fields B.shrink s D rem hD small A (K:=K) c branch).1
  have wide : 8≤W := by
    have linear := Nat.le_self_pow (by decide : 10≠0) u
    omega
  have field := PhysicalStage.ShrinkOutput.selected_kernel B.shrink s D rem hD small A
    cur before c branch H caps.old caps.ordinals.1 wide caps.ordinals.2 bounds.widthPos v (0 : Fin 5)
  have address : DescriptorSpan.fields K c dims₀ lay 34+(5*siteNo+0)=kernel :=
    congrArg₂ Nat.add f34 ((Nat.add_zero (5*siteNo)).trans
      ((congrArg (fun n : ℕ => 5*n) placed.symm).trans (Nat.mul_comm 5 (rank₀).val)))
  have limit : kernel<(en).next.heap := by
    rw [←address]
    exact field.1
  have native : issued kernel=(c.header : Word W) := by
    rw [←address]
    exact field.2.1
  have heapLow : heads≤c.heap :=
    bounds.graphLow.trans ((Nat.le_add_right _ _).trans bounds.graphBound)
  have kernelLow : c.heap≤(sites).layer.kernels := (descriptorAllocation K c (.shrink dims₀)).1
  have lower : heads≤kernel := (heapLow.trans kernelLow).trans (Nat.le_add_right _ _)
  have controlAt : (en).next.heap≤cur.val := H.cursor.controls
  have high : (en).next.heap<2^W := controlAt.trans_lt cur.isLt
  have headerSpace : c.header+64≤c.heap := H.cursor.earlier
  have nextHeap : c.heap≤(en).next.heap := by
    rw [NavigationDirectory.heap_step]
    exact Nat.le_add_right _ _
  have headerEnd : c.header+64≤(en).next.heap := headerSpace.trans nextHeap
  have headerFit : c.header<2^W := by omega
  have addr48 : c.header+48<(en).next.heap :=
    (Nat.add_lt_add_left (by decide : 48<64) c.header).trans_le headerEnd
  have directoryWord : input (b.nodes+8*idx+5)=(kernel : Word W) := dir.kernel
  have pointer : (input (HistoryStageBody.Physical.nodeAddress u input+5)).val=kernel := by
    rw [addr, directoryWord, Fin.val_cast_of_lt (limit.trans high)]
  have survives : final kernel=issued kernel :=
    saved kernel (limit.trans_le controlAt).ne ((limit.trans_le controlAt).trans controls).ne
      (.inr lower) limit
  have entryWord : input kernel=(c.header : Word W) :=
    (keep kernel (.inr lower) limit).trans (survives.trans native)
  have header : (input kernel).val=c.header := (congrArg Fin.val entryWord).trans (Fin.val_cast_of_lt headerFit)
  have actual : stageAddress u input=c.header := by
    unfold stageAddress
    rw [pointer]
    exact header
  have ports : (input (c.header+48)).val=d := by
    rw [keep _ (.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (by decide : 48<64) c.header⟩) addr48]
    exact SavedFrame.familyDegree (K:=K) c (.shrink dims₀) saved headerSpace controlAt
      (controlAt.trans controls.le) (PhysicalStage.ShrinkOutput.degreeWord B.shrink s D rem hD small A cur before c H)
  have tagWord : input (b.nodes+8*idx)=(1 : Word W) := kind
  have marked : (input (HistoryStageBody.Physical.nodeAddress u input)).val=1 := by
    rw [addr, tagWord]
    exact Fin.val_cast_of_lt (show (1 : ℕ)<2^W from (by
      have enough := Nat.pow_le_pow_right (by decide : 0<2) wide
      omega))
  exact ⟨select_shrink B rom W u input level marked (by rw [actual]; exact ports),
    by rw [actual]; exact addr48.trans high⟩


variable {heads heapEnd : ℕ} {cur ctr : Word (16*u^10)} {before issued final entry : Memory (16*u^10)}
    (O : let exponent := B.exponent level.val
         let nextDegree := 2^(B.exponent (level.val+1))
         let issuedLayout := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink exponent nextDegree rem hD small A branch)
         ∀ v, Incidents.SiteOrder («S» := shrinkStage exponent nextDegree) (shrinkRecordPacking exponent rem A)
           (shrinkRecordState exponent rem A).order issuedLayout v (16*u^10))
    (old : A.ArchiveSites)
    (numbered : old.Numbered) (first : old.layer.first=c.node)
local notation "row₀" => shrinkArchiveStep (K:=K) («W»:=W) B.shrink s D rem hD small A c branch O old numbered first
local notation "target" => Move.WordStep.targetSite (R:=M) (i:=branch) z
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
variable (b : Banks) (seedCount : ℕ) (trees : Forest F L.ports.form)
    (orig : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ)
local notation "childN" i:arg => NodeValue.ofSite (Run.nodeOfSite L trees orig ((row₀).row.children z i).val)
  pointer (streamAt u seedCount ((row₀).data.child rank₀ i)) (endsAt u seedCount ((row₀).data.child rank₀ i))

local notation "lanesEq" => rootLaneEq s rem
local notation "priorW" => A.laneWords lanesEq L
local notation "priorS" => PhysicalStage.priorSites lanesEq A old
local notation "iso₀" => StageAddress.shrinkInputIso (X).graph (X).chart
  (shrinkRecordLane s rem) P rfl (X).width
local notation "past₀" => (iso₀).pushWord (G:=StageAddress.portGraph (X).graph (X).chart) (w:=(X).width)
  (H:=Diagonal.CompressorPacking.oldGraph P) (b:=shrinkRecordWidth s rem A) (Pins:=Pins) (show (X).Words Pins from priorW)
local notation "ordered₀" => Owner.childOrder P lay v
local notation "list₀" => (sites).layer.children+(rank₀).val*(sites).layer.childCount
local notation "T₀" => numInput J (family).childBound (numeric entry)

open private shrinkPackedSuccessor from OAI.ThreeFlat.Diagonal.ShrinkArchiveStep
open private prior_id from OAI.ThreeFlat.RAM.FoldRefreshCache

omit [Fintype F] in
set_option maxHeartbeats 1900000 in
set_option maxRecDepth 14000 in
/-- The same old site viewed in the numbered child array and in the root's packed port chart. -/
theorem occupied_child_site
    (placed : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (k : Fin (d*2^(2*d+1))) :
    laneSite lanesEq A (shrinkChildFiber B.shrink s D rem hD small A branch z k).val =
      (iso₀).site.symm ((ordered₀ k).val) := by
  let packed:=shrinkPackedSuccessor B.shrink s D rem hD small A branch
  have here : packed z=v := by
    change (shrinkPackOrder s D rem A).symm
      (shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))=v
    rw [←placed,Equiv.symm_apply_apply]
  change laneSite lanesEq A ((shrinkOldPosition s rem A).symm
    ((Owner.childOrder P lay (packed z) k).val))=_
  rw [here]
  change laneSite lanesEq A ((laneSite lanesEq A).symm _) = _
  exact (laneSite lanesEq A).apply_symm_apply _

private theorem childHalfBitsAfterLaneChange {degree oldLanes newLanes : ℕ}
    (lanes : oldLanes = newLanes) (state : State degree oldLanes) (words : state.Words Pins)
    {sites₁ edges₁ : Type} [Fintype sites₁] [Fintype edges₁]
    (graph₁ : LinearAlgebra.SpectralBooks.PortGraph sites₁ edges₁) (width₁ : edges₁ → ℕ)
    (chart : HistoryRelabel.Iso (lanes ▸ state : State degree newLanes).shape (WordLayout.shape graph₁ width₁))
    (child : state.Site) (destination : sites₁)
    (placed : laneSite lanes state child = chart.site.symm destination)
    (sameWidth : ∀ edge, (lanes ▸ state : State degree newLanes).width edge = width₁ (chart.edge edge)) :
    (chart.pushWord (G:=(lanes ▸ state : State degree newLanes).shape.graph)
      (w:=(lanes ▸ state : State degree newLanes).width) (H:=graph₁) (b:=width₁)
      (Pins:=Pins) (state.laneWords lanes words)).ports.halfBits destination = words.ports.halfBits child := by
  cases lanes
  exact (HistoryRelabel.Iso.pushWord_halfBits_at (G:=state.shape.graph) (w:=state.width)
    (H:=graph₁) (b:=width₁) chart words sameWidth destination).trans
    (congrArg words.ports.halfBits placed.symm)

private theorem childIdAfterLaneChange {degree oldLanes newLanes : ℕ}
    (lanes : oldLanes = newLanes) (state : State degree oldLanes) (archiveSites : state.ArchiveSites)
    (child : state.Site) (source : (lanes ▸ state : State degree newLanes).Site)
    (placed : laneSite lanes state child = source) :
    archiveSites.id child = (PhysicalStage.priorSites lanes state archiveSites).id source := by
  subst source
  exact (priorSites_id lanes state archiveSites child).symm

set_option maxHeartbeats 1900000 in
set_option maxRecDepth 17000 in
/-- Recover the old half-bit count in every S13 result and the address of that
same child in S44, in the numeric order used by the elected arm. -/
theorem occupied_children
    (placed : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (st : (T₀).id=idx) (nodes : b.nodes=Diagonal.TickWorkspace.base u 44)
    (entryRows : StageRows L step row₀ z u b entry)
    (port : HistoryStageRoot.Ports L.ports (((M).target_eq branch).symm ▸ (step).words.ports)
      (step).stage.count (step).stage.child target T₀ (numeric entry))
    (nav : ∀a,NavigationCell u a→Diagonal.TickWorkspace.base u 19≤a ∧ a<2^W) (listRoom : list₀<2^W) :
    HistoryStageRoot.childCount T₀ (numeric entry)=d*2^(2*d+1) ∧
    (∀ k : Fin (d*2^(2*d+1)), HistoryStageRoot.oldHalf
      (HistoryStageRoot.atResult (numeric entry) (HistoryStageRoot.childPtr T₀ (numeric entry) k.val))=
        (past₀).ports.halfBits ((ordered₀ k).val)) ∧
    numeric entry (HistoryStageRoot.node T₀+3)=list₀ ∧
    (Diagonal.TickWorkspace.base u 19≤list₀ ∧ list₀+d*2^(2*d+1)≤2^W) ∧
    ∀ k : Fin (d*2^(2*d+1)),numeric entry (list₀+k.val)=
      (priorS).id ((iso₀).site.symm ((ordered₀ k).val)) := by
  let n:=d*2^(2*d+1)
  have positive : 0<n := by dsimp only [n];positivity
  have countEq : n=(step).stage.count target:=(step).count_eq (row₀) z
  have physical (k : Fin n):=occupied_child_site B level hD small A branch z v placed k
  have loc : HistoryStageRoot.node T₀=b.nodes+8*idx:=by
    unfold HistoryStageRoot.node
    rw [st,nodes]; rfl
  have widthEq (k : Fin n) :
      (past₀).ports.halfBits ((ordered₀ k).val)=L.ports.halfBits (shrinkChildFiber B.shrink s D rem hD small A branch z k).val := by
    exact childHalfBitsAfterLaneChange lanesEq A L (Diagonal.CompressorPacking.oldGraph P)
      (shrinkRecordWidth s rem A) (iso₀) (shrinkChildFiber B.shrink s D rem hD small A branch z k).val
      ((ordered₀ k).val) (physical k)
      (fun edge => (congrArg (X).width ((StageAddress.splitEdge (shrinkRecordLane s rem)).symm_apply_apply edge)).symm)
  refine ⟨port.degree.trans countEq.symm,?_,?_,?_,?_⟩
  · intro k
    let j:=k.cast countEq
    have ar:=port.childArity j
    have ex:=port.childExt j
    change (HistoryStageRoot.atResult (numeric entry) (HistoryStageRoot.childPtr T₀ (numeric entry) k.val)).pins=
      L.ports.form.width (((step).children z) j).val at ar
    change (HistoryStageRoot.atResult (numeric entry) (HistoryStageRoot.childPtr T₀ (numeric entry) k.val)).extCount=
      L.ports.ext (((step).children z) j).val at ex
    calc
      _ = L.ports.halfBits (((step).children z) j).val := by
        rw [HistoryStageRoot.oldHalf,ar,ex]
        simp [PortLayout.form]
      _ = L.ports.halfBits (shrinkChildFiber B.shrink s D rem hD small A branch z k).val :=
        congrArg L.ports.halfBits (shrink_childrenAt B.shrink s D rem hD small A L branch z j k rfl)
      _ = _ := (widthEq k).symm
  · rw [loc]
    exact (congrArg Fin.val entryRows.directory.childPtr).trans (Fin.val_cast_of_lt listRoom)
  · let a : Fin n:=⟨0,positive⟩
    let last : Fin n:=⟨n-1,by omega⟩
    have lo:= (nav _ (entryRows.footprint.child rank₀ a)).1
    have hi:= (nav _ (entryRows.footprint.child rank₀ last)).2
    change Diagonal.TickWorkspace.base u 19≤list₀+0 at lo
    change list₀+(n-1)<2^W at hi
    change Diagonal.TickWorkspace.base u 19≤list₀ ∧ list₀+n≤2^W
    omega
  · intro k
    have recorded := shrink_child_id (K:=K) («W»:=W) B.shrink s D rem hD small A c branch O old numbered first z k
    exact (entryRows.reads.child rank₀ k).trans (recorded.trans (childIdAfterLaneChange lanesEq A old
      (shrinkChildFiber B.shrink s D rem hD small A branch z k).val
      ((iso₀).site.symm ((ordered₀ k).val)) (physical k)))

private def selectedStepSite {K₀ Pins₀ E₀ : Type} [Field K₀] {oldD oldL newD newL : ℕ}
    {Y : State oldD oldL} (move : Move K₀ Y newD newL) (term : Fin move.rules.count)
    (words : Y.Words Pins₀) (assembly : move.WordStep Pins₀ words term)
    (forest : Forest K₀ words.ports.form) (origin : ∀ y, Fin (words.ext y) → E₀)
    (site : (move.next term).Site) : Run.SelectedNode K₀ Pins₀ E₀ :=
  Run.nodeOfSite (A := move.next term) assembly.words (assembly.nextForest forest)
    (Run.pushedOrigin (R := move) (i := term) assembly origin) site

local notation "outSite" => selectedStepSite (K₀ := F) (Pins₀ := Pins) (E₀ := E)
  (oldD := d) (oldL := shrinkCharge s+rem) (newD := D) (newL := rem) (Y := A)
  M branch L step trees orig z

set_option maxRecDepth 22000 in
set_option maxHeartbeats 1500000 in
/-- Every incident in the chosen shrink is charged to the same physical S43 entry.
Its decoded unit count pays the selected port and compactor page. -/
theorem occupied_page_margin {fee levels degree : ℕ} {paidMem : ℕ→ℕ}
    (placed : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (paid : (M).ResourceReceipt fee levels peak b paidMem L step old charge row₀)
    (priced : Run.PricedAt (F := F) (Pins := Pins) (E := E) b paidMem fee levels peak idx
      (selectedStepSite (K₀ := F) (Pins₀ := Pins) (E₀ := E) (Y := A)
        M branch L step trees orig z))
    (unit : 0<b.unitWork) (tariff : B.archiveUnit u B.localCoefficient degree≤b.unitWork) (age : 2≤u) :
    let amount:=archiveColumn b paidMem idx 0/b.unitWork
    (∀ i,shrinkRecordCopies B.shrink s rem A (((O v).equiv i).val)≤amount) ∧
      gridPageRate (arity B) (shrinkGrid B level)*((amount+1)*(W+1)^3)≤V := by
  intro amount
  let many:=shrinkRecordCopies B.shrink s rem A
  let total:=∑ i,many (((O v).equiv i).val)
  have copies : total=(shrinkBinary_siteCopies B.shrink s D rem hD small A).copies branch z := by
    let listed (y : Computability.VPVNP.Compression.Site (X).Base (BitWord (Diagonal.CompressorPacking.tagBits d)) (BitWord rem)) :=
      (List.ofFn (fun i => many (((O y).equiv i).val))).sum
    have recorded := shrinkLayerData_motif_sum (K:=K) B.shrink s D rem hD small A c branch O z
    change listed ((shrinkPackOrder s D rem A).symm
      (shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))) = _ at recorded
    rw [←placed, Equiv.symm_apply_apply] at recorded
    simpa only [total, listed, List.sum_ofFn] using recorded
  have assigned : total≤charge z := by rw [copies];unfold shrinkBinaryCharge;omega
  have available : charge z≤amount := by
    change charge z≤archiveColumn b paidMem ((row₀).sites.id z) 0/b.unitWork
    rw [(paid.after z).1,Nat.mul_div_cancel_left _ unit]
    exact Nat.le_add_right ..
  have gridAt : shrinkGrid B level∈grids B := by
    rw [grids,List.mem_append]
    exact .inl (List.mem_ofFn.mpr ⟨level,rfl⟩)
  have pages:=priced.grid_pages B gridAt degree unit tariff
  have exp : 2≤u^10 := age.trans (Nat.le_self_pow (by decide) _)
  exact ⟨fun i=>(Finset.single_le_sum (fun j _=>Nat.zero_le (many (((O v).equiv j).val)))
    (Finset.mem_univ i)).trans (assigned.trans available),
    pages.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega))⟩

private def priorDirectoryRead {w deg n n' : ℕ} (e : n = n') (Y : State deg n)
    (S₀ : Y.ArchiveSites) (nodeBase : ℕ) (mem : Memory w) : Prop :=
  let sites₀ := PhysicalStage.priorSites e Y S₀
  ∀ x : (e ▸ Y : State deg n').Site, nodeBase+(8*sites₀.id x+6) < 2^w ∧
    numeric mem (nodeBase+(8*sites₀.id x+6)) = sites₀.layer.incident+(sites₀.ord x).val*2

private theorem priorDirectoryRead_of_rows {age₀ deg n n' : ℕ} (e : n = n') (Y : State deg n)
    (S₀ : Y.ArchiveSites) (bank : Banks) (mem : Memory (16*age₀^10))
    (age : 16 ≤ age₀) (nodes : bank.nodes = Diagonal.TickWorkspace.base age₀ 44)
    (ends : S₀.layer.first+S₀.layer.count ≤ (volume age₀)^2)
    (halves : State.HalfRows S₀ (fun a => Diagonal.TickWorkspace.base age₀ 19 ≤ a ∧
      a < 2^(16*age₀^10)) (numeric mem))
    (directory : ∀ j : Fin S₀.layer.count, DirectoryRow bank S₀.layer j mem) :
    priorDirectoryRead e Y S₀ (Diagonal.TickWorkspace.base age₀ 44) mem := by
  intro x
  obtain ⟨a,rfl⟩ := (laneSite e Y).surjective x
  rw [priorSites_id,priorSites_ord]
  have before : S₀.id a < (volume age₀)^2 :=
    lt_of_lt_of_le (Nat.add_lt_add_left (S₀.ord a).isLt S₀.layer.first) ends
  have big : 128 ≤ volume age₀ := Nat.pow_le_pow_right (by decide : 0 < 2)
    ((by omega : 7 ≤ age₀).trans (Nat.le_self_pow (by decide : 10 ≠ 0) age₀))
  have bound := directory_address_space (u:=age₀) age big before
  have address := congrArg Fin.val (directory (S₀.ord a)).incident
  have fits : S₀.layer.incident+(S₀.ord a).val*2 < 2^(16*age₀^10) := by
    simpa only [Fin.val_zero, Nat.add_zero] using (halves.headerSafe a 0).2
  refine ⟨by omega, ?_⟩
  rw [nodes] at address
  simpa only [PhysicalStage.priorSites, State.ArchiveSites.id, numeric, Nat.add_assoc,
    Fin.val_cast_of_lt fits] using address

set_option maxRecDepth 16000 in
set_option maxHeartbeats 800000 in
include O numbered first in
omit [Fintype F] in
/-- Read the exact previous S44 incident-header pointer after the old lane chart is
recast. Every previous site precedes the current node, including children of other roots. -/
theorem occupied_old_directory (age : 16≤u) (smallNode : idx<V^2) (nodes : b.nodes=Diagonal.TickWorkspace.base u 44)
    (oldHalf : State.HalfRows old (fun a=>Diagonal.TickWorkspace.base u 19≤a ∧ a<2^W) (numeric entry))
    (oldDir : ∀ k : Fin old.layer.count,DirectoryRow b old.layer k entry) :
    priorDirectoryRead lanesEq A old (Diagonal.TickWorkspace.base u 44) entry := by
  have contiguous : (sites).layer.first = old.layer.first+old.layer.count := (row₀).row.contiguous
  have startBound : (sites).layer.first ≤ V^2 := by
    change (sites).layer.first+(rank₀).val < V^2 at smallNode
    omega
  exact priorDirectoryRead_of_rows lanesEq A old b entry age nodes
    (contiguous ▸ startBound) oldHalf oldDir

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
/-- Publish all cells of the actual chosen shrink. The physical occurrence fixes the
family and root syntax, and its archived charge pays for the achieved kernel and join. -/
theorem write_occurrence_with_selection {fee levels : ℕ} {paidMem : ℕ→ℕ}
    (native : ShrinkWordVisit K cur ctr heads heapEnd final B.publicTemplate
      (M) branch L step old charge row₀)
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (caps : ShrinkNativeCaps B.shrink s D rem W A) (bounds : RecordedArrayBounds W heads c A)
    (saved : SavedFrame cur ctr heads (en).next.header (en).next.heap issued final)
    (keep : ∀a,(c.header≤a ∧ a<c.header+64 ∨ heads≤a)→a<(en).next.heap→entry a=final a)
    (area : Diagonal.TickWorkspace.base u 19≤heads) (control : cur.val<ctr.val)
    (stridePos : 0<K) (strideRoom : K<2^W)
    (strt : Diagonal.TickWorkspace.base u 19≤rom) (static : rom+libraryWords B W<2^W)
    (age : 40≤u) (threshold : B.archiveConstant B.localCoefficient≤u)
    (current : numeric entry (Diagonal.TickWorkspace.base u 18)=idx+1) (smallNode : idx<V^2)
    (placed : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (nodes : b.nodes=Diagonal.TickWorkspace.base u 44) (charges : b.charges=Diagonal.TickWorkspace.base u 43)
    (entryRows : StageRows L step row₀ z u b entry)
    (children : ∀ i : Fin (sites).layer.childCount,(childN i).Cached tag₀ u ((row₀).data.child rank₀ i) entry)
    (wordFee : (W+1)^3≤fee) (positive : 0<b.unitWork)
    (paid : (M).ResourceReceipt fee levels peak b paidMem L step old charge row₀)
    (margin : 10*(levels+2)^2*fee≤b.unitWork)
    (resource : Run.PricedAt (F := F) (Pins := Pins) (E := E) b paidMem fee levels peak idx outSite)
    (ordered : A.OrderedHalves L)
    (oldHalf : State.HalfRows old (fun a=>Diagonal.TickWorkspace.base u 19≤a ∧ a<2^W) (numeric entry))
    (oldDirectory : ∀k : Fin old.layer.count,DirectoryRow b old.layer k entry)
    (mounted : Mounted B W W rom entry)
    {horizon : ℕ} (allowance : B.archiveUnit u B.localCoefficient horizon≤b.unitWork)
    (later : seedCount≤ idx) (shape : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W)
    {n : ℕ} (vals : Fin n→NodeValue F) (j : Fin n) (number : j.val=idx)
    (same : vals j=NodeValue.ofSite (F := F) (Pins := Pins) (E := E) outSite pointer (streamAt u seedCount idx) (endsAt u seedCount idx)) :
    let arm:=fun i : Fin n=>B.nativeArmTime levels fee b paidMem i.val
    (∃ f, (families B rom W).find? (matchesFamily u entry)=some f) ∧
    CacheWrite arc shape pub (families B rom W) vals tag₀ (B.nativeVisitCost levels fee b paidMem)
      arm (fun i _=>arm i) j entry := by
  let T:=numInput J (family).childBound (numeric entry)
  have ord : (rank₀).val=siteNo:=by
    exact (congrArg Fin.val placed).symm.trans (shrinkPackOrder_val s D rem A v)
  have selection:=recorded_dispatch (rom:=rom) B level hD small A branch z v H caps bounds saved
    (by omega) control keep b nodes current entryRows.kind entryRows.directory ord
  have room:=B.blockPageRate_at_age threshold
  have reg:=grid_page_rate_le_block B (g:=shrinkGrid B level) (List.mem_append_left _ (List.mem_ofFn.mpr ⟨level,rfl⟩))
  have hreg : gridPageRate (HistoryStageBody.Physical.arity B) (shrinkGrid B level)≤u:=reg.trans room
  have vol : u<V:=(Nat.le_self_pow (by decide : 10≠0) u).trans_lt Nat.lt_two_pow_self
  have space : Diagonal.TickWorkspace.base u 60+Diagonal.TickWorkspace.stride u<2^W:=Diagonal.TickWorkspace.word_space (by omega) (by
    change 60<(2^(u^10))^4
    have ww : 7≤u^10:=(by omega : 7≤u).trans (Nat.le_self_pow (by decide) _)
    have ww' := Nat.pow_le_pow_right (by decide : 0<2) ww
    have := Nat.le_self_pow (by decide : 4≠0) (2^(u^10))
    omega)
  have Vword : 2+V<2^W:=by
    have sV:V ≤ Diagonal.TickWorkspace.stride u:=Nat.le_self_pow (by decide : 4≠0) V
    change (60+1)*Diagonal.TickWorkspace.stride u+Diagonal.TickWorkspace.stride u<2^W at space;omega
  have capSize : (family).childBound≤V:=by
    have bounds' : Incidents.capacity S≤u:=by
      unfold gridPageRate at hreg
      change _+(Incidents.capacity S+2)*(6+2)*8*32+_+_≤u at hreg
      omega
    change d*2^(2*d+1)≤V
    change 8*d^2*2^(2*d+1)≤u at bounds'
    have hd : d≤8*d^2:=by have :=Nat.le_self_pow (by decide : 2≠0) d;omega
    have :=Nat.mul_le_mul_right (2^(2*d+1)) hd
    omega
  have capacity : ((family).motifs+2)*((family).parties+2)*8*32≤V:=by
    change ((shrinkGrid B level).motifs+2)*((shrinkGrid B level).parties+2)*8*32≤V
    unfold gridPageRate at hreg;omega
  have sector : (2*((family).parties+2)*8+5)*32+8≤V:=by
    change ((family).motifs+2)*(6+2)*8*32≤V at capacity
    have nonzero : 0<(family).motifs:=by change 0<8*d^2*2^(2*d+1);positivity
    change (2*(6+2)*8+5)*32+8≤V
    omega
  have deq : (sites).layer.childCount=(family).childBound:=rfl
  have feeLarge : 2≤fee:=by
    have : 2≤W+1:=by have:=Nat.le_self_pow (by decide : 10≠0) u;omega
    exact this.trans ((Nat.le_self_pow (by decide : 3≠0) _).trans wordFee)
  have ex : (step).words.ext z≤V := (resource.native_words (u:=u) (by omega) feeLarge margin).2.1
  have size:8*((step).nextForest trees z).resources≤V:=(resource.slab (u:=u) (by omega) feeLarge margin).2.2.2
  have resource_eq:=HistoryWordStepResult.resource_eq (step) trees z
  have rootRoom : 4*((step).rootPacket z).2.resources≤V ∧ ((step).rootPacket z).1<2^W:=by
    change 4*((step).stage.root target).resources≤V ∧ (step).stage.rootWidth target<2^W
    rw [←resource_eq,Stage.resources_assemble] at size
    unfold Stage.freshResources at size;omega
  have wordAtRoot:=shrink_word_root_at B.shrink s D rem hD small A L branch z v placed (O v)
    (ShrinkOutput.rootKeys B.shrink s D rem hD small A H)
  have sizes : 4*(issuedRootAt B.shrink s D rem hD small A L branch v (O v)).2.resources≤V ∧
      (issuedRootAt B.shrink s D rem hD small A L branch v (O v)).1<2^W:=by rw [←wordAtRoot];exact rootRoom
  have nav (a : ℕ) (ha:NavigationCell u a) : Diagonal.TickWorkspace.base u 19≤a ∧ a<2^W:=by
    obtain ⟨lo,hi⟩:=ha
    exact ⟨((Nat.le_add_right _ _).trans (Diagonal.TickWorkspace.apart (u:=u) (by decide : 19<20))).trans lo,
      hi.trans (by omega)⟩
  have archiveSites_eq : (row₀).sites = sites := by unfold shrinkArchiveStep; rfl
  have countPos : 0<(sites).layer.childCount:=by change 0<d*2^(2*d+1);positivity
  have listRoom : (sites).layer.children+(rank₀).val*(sites).layer.childCount<2^W:=by
    let k : Fin (sites).layer.childCount:=⟨0,countPos⟩
    simpa only [k,Nat.add_zero,archiveSites_eq] using (nav _ (entryRows.footprint.child rank₀ k)).2
  have sourceHalf:=entryRows.halves.transfer (fun _ _=>rfl) nav
  have halfRoom:= (sourceHalf.headerSafe z 0).2
  have halfFit : (sites).layer.incident+(rank₀).val*2<2^W:=by
    have raw : (row₀).sites.layer.incident+((row₀).sites.ord z).val*2<2^W := by
      simpa only [Fin.val_zero,Nat.add_zero] using halfRoom
    have address := congrArg (fun a : ((M).next branch).ArchiveSites =>
      a.layer.incident+(a.ord z).val*2) archiveSites_eq
    exact address.symm.trans_lt raw
  have st : T.id=idx:=by change numeric entry (Diagonal.TickWorkspace.base u 18)-1=idx;rw [current];omega
  have port:=StageRows.ports (L:=L) («step»:=step) (row:=row₀) (v:=z) (u:=u) (seedCount:=seedCount)
    (bank:=arc) («family»:=family) (trees:=trees) (orig:=orig) (pointer:=pointer) (tag:=tag₀)
    (m:=entry) (b:=b) entryRows native.childOrder st nodes
    (deq.symm ▸ (capSize.trans_lt (by omega))) listRoom halfFit (by exact ex.trans_lt (by omega)) children
  have oldWidth:=recorded_root_width (B:=B) (level:=level) (u:=u) (K:=K) (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch)
    (v:=v) (order:=O v) cur before issued c H L z placed (J).nodePorts (family).childBound T (numeric entry)
    rfl rfl rfl port (show (step).stage.count target ≤ d*2^(2*d+1) from
      (show d*2^(2*d+1) = (step).stage.count target from (step).count_eq (row₀) z).symm.le)
  have childSmall (i : Fin (sites).layer.childCount) : (row₀).data.child rank₀ i<V^2:=by
    exact (prior_id (row₀) z i).trans smallNode
  obtain ⟨nativeCount,cached,childTable,arrayRoom,childIds⟩:=
    occupied_children (K:=K) (u:=u) (rom:=rom) B level hD small A branch L z v O old numbered first
      b placed st nodes entryRows port nav listRoom
  have fields := PhysicalStage.shrink_allocated_fields B.shrink s D rem hD small A (K:=K) c branch
  have selectedDir : DirectoryRow b (sites).layer rank₀ entry :=
    Eq.mp (congrArg (fun a : ((M).next branch).ArchiveSites =>
      DirectoryRow b a.layer (a.ord z) entry) archiveSites_eq) entryRows.directory
  have kernelBase : DescriptorSpan.fields K c dims₀ lay 34 = (sites).layer.kernels := fields.1
  have incidentBase : DescriptorSpan.fields K c dims₀ lay 38 = (sites).layer.incident := fields.2.1
  have originalHead : entry (Diagonal.TickWorkspace.base u 44+8*idx+5)=
      ((DescriptorSpan.fields K c dims₀ lay 34+5*siteNo:ℕ):Word W):=by
    simpa only [nodes, State.ArchiveSites.id, kernelBase, ←ord, Nat.mul_comm 5 (rank₀).val]
      using selectedDir.kernel
  have nativeAddress : HistoryStageRoot.node T=b.nodes+8*idx:=by
    unfold HistoryStageRoot.node;rw [st,nodes]; rfl
  have atHalf : numeric entry (HistoryStageRoot.node T+6)=(sites).layer.incident+(rank₀).val*2:=by
    rw [nativeAddress]
    exact (congrArg (fun a : Word W => a.val) selectedDir.incident).trans (Fin.val_cast_of_lt halfFit)
  have headAt : numeric entry (HistoryStageRoot.node T+6)=DescriptorSpan.fields K c dims₀ lay 38+2*siteNo:=by
    simpa only [incidentBase, ←ord, Nat.mul_comm 2 (rank₀).val] using atHalf
  have newBits := recorded_new_bits sourceHalf z (J).nodePorts T
    (fun k=>(past₀).ports.halfBits ((ordered₀ k).val)) _ rfl rfl rfl
    nativeCount (by change d*2^(2*d+1)≤d*2^(2*d+1);rfl) cached atHalf oldWidth
  have oldSites:=occupied_old_directory (K:=K) (u:=u) B level hD small A branch z O old numbered first
    b (by omega) smallNode nodes oldHalf oldDirectory
  have ⟨copies,pages⟩:=occupied_page_margin (K:=K) (u:=u) B level hD small A branch L z v O old numbered
    first b trees orig placed paid resource positive allowance (by omega)
  have elected:=recorded_occupied_arms (B:=B) (level:=level) (u:=u) (start:=rom) (height:=W)
    (K:=K) (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=H.tagPos)
    (words:=L) (v:=v) (order:=O v) (node:=idx) (input:=entry)
    cur ctr before issued final c heads H saved caps bounds control keep area current originalHead
    (by omega) smallNode room mounted strt static stridePos strideRoom le_rfl priorS
    (laneOrdered lanesEq A L ordered) (laneHalfRows lanesEq A old oldHalf) oldSites
    T st rfl rfl nativeCount cached newBits headAt list₀ childTable arrayRoom childIds
    sizes.1 sizes.2 (archiveColumn b paidMem idx 0/b.unitWork) copies pages
  obtain ⟨post,ticks,run,records,info,frame,price⟩:=emit_recorded_shrink (B:=B) (level:=level) (u:=u)
    (start:=rom) (height:=W) (K:=K) (rem:=rem) (hD:=hD) (small:=small) (A:=A)
    (branch:=branch) (gt:=H.tagPos) (v:=v) (order:=O v) (node:=idx) (input:=entry) (words:=L)
    cur ctr before issued final c heads H saved caps bounds control
    (fun a lo hi=>keep a (.inl ⟨lo,by omega⟩) (by have h:=H.cursor.earlier;have:=heap_step K c (.shrink dims₀);omega))
    stridePos strideRoom (fun a lo hi=>keep a (.inr lo) hi) area current (by omega) smallNode room strt static
    sizes.2 sizes.1 z sourceHalf ⟨rfl,ord⟩ b nodes entryRows.directory (row₀).data
    entryRows.reads (entryRows.footprint.mono nav) childSmall oldWidth elected
  have priced:=kernel_ticks_at_id B level hD small A branch L z v (O v) placed paid positive wordFee trees price
  have real : RecordedWordStep K cur ctr heads heapEnd final Pins B.publicTemplate (M) branch L step old charge row₀ :=
    Or.inl native
  have tags (tt) : tag₀ tt<2^W:=
    (Fintype.equivFin _ tt).isLt.trans_le (block_tags_at_age B room)
  have finalDegree : 2^B.exponent B.levels<2^W:=by
    have h:=(grid_page_rate_le_block B (List.mem_append_right _ (List.mem_singleton_self (refreshGrid B)))).trans room
    dsimp [gridPageRate,refreshGrid] at h
    omega
  refine ⟨⟨_, selection.1⟩, ?_⟩
  exact HistoryWordStepRun.write_recorded L (step) (row₀) z u seedCount arc family trees orig pointer tag₀
    post b real native.childOrder B rom W levels fee paidMem positive wordFee paid resource margin age smallNode
    deq.le capSize listRoom halfFit sector capacity (fun _ _ _ modeEquality => nomatch modeEquality)
    entry st entryRows nodes charges children tags later ticks run records info frame priced
    selection.1 selection.2 finalDegree shape pub vals j number same

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
/-- The cache-writing projection used by the original receiver. -/
theorem write_occurrence {fee levels : ℕ} {paidMem : ℕ→ℕ}
    (native : ShrinkWordVisit K cur ctr heads heapEnd final B.publicTemplate
      (M) branch L step old charge row₀)
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (caps : ShrinkNativeCaps B.shrink s D rem W A) (bounds : RecordedArrayBounds W heads c A)
    (saved : SavedFrame cur ctr heads (en).next.header (en).next.heap issued final)
    (keep : ∀a,(c.header≤a ∧ a<c.header+64 ∨ heads≤a)→a<(en).next.heap→entry a=final a)
    (area : Diagonal.TickWorkspace.base u 19≤heads) (control : cur.val<ctr.val)
    (stridePos : 0<K) (strideRoom : K<2^W)
    (strt : Diagonal.TickWorkspace.base u 19≤rom) (static : rom+libraryWords B W<2^W)
    (age : 40≤u) (threshold : B.archiveConstant B.localCoefficient≤u)
    (current : numeric entry (Diagonal.TickWorkspace.base u 18)=idx+1) (smallNode : idx<V^2)
    (placed : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (nodes : b.nodes=Diagonal.TickWorkspace.base u 44) (charges : b.charges=Diagonal.TickWorkspace.base u 43)
    (entryRows : StageRows L step row₀ z u b entry)
    (children : ∀ i : Fin (sites).layer.childCount,(childN i).Cached tag₀ u ((row₀).data.child rank₀ i) entry)
    (wordFee : (W+1)^3≤fee) (positive : 0<b.unitWork)
    (paid : (M).ResourceReceipt fee levels peak b paidMem L step old charge row₀)
    (margin : 10*(levels+2)^2*fee≤b.unitWork)
    (resource : Run.PricedAt (F := F) (Pins := Pins) (E := E) b paidMem fee levels peak idx
      (selectedStepSite (K₀ := F) (Pins₀ := Pins) (E₀ := E) (Y := A) M branch L step trees orig z))
    (ordered : A.OrderedHalves L)
    (oldHalf : State.HalfRows old (fun a=>Diagonal.TickWorkspace.base u 19≤a ∧ a<2^W) (numeric entry))
    (oldDirectory : ∀k : Fin old.layer.count,DirectoryRow b old.layer k entry)
    (mounted : Mounted B W W rom entry)
    {horizon : ℕ} (allowance : B.archiveUnit u B.localCoefficient horizon≤b.unitWork)
    (later : seedCount≤ idx) (shape : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W)
    {n : ℕ} (vals : Fin n→NodeValue F) (j : Fin n) (number : j.val=idx)
    (same : vals j=NodeValue.ofSite (F := F) (Pins := Pins) (E := E)
      (selectedStepSite (K₀ := F) (Pins₀ := Pins) (E₀ := E) (Y := A) M branch L step trees orig z)
      pointer (streamAt u seedCount idx) (endsAt u seedCount idx)) :
    let arm:=fun i : Fin n=>B.nativeArmTime levels fee b paidMem i.val
    CacheWrite arc shape pub (families B rom W) vals tag₀ (B.nativeVisitCost levels fee b paidMem)
      arm (fun i _=>arm i) j entry := by
  exact (write_occurrence_with_selection
    (F:=F) (Pins:=Pins) (E:=E) (K:=K) (u:=u) (rom:=rom) (rem:=rem) (c:=c)
    (B:=B) (level:=level) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (L:=L) (z:=z) (v:=v) (O:=O)
    (old:=old) (numbered:=numbered) (first:=first) (b:=b) (seedCount:=seedCount) (trees:=trees)
    (orig:=orig) (pointer:=pointer)
    native H caps bounds saved keep area control stridePos
    strideRoom strt static age threshold current smallNode placed nodes
    charges entryRows children wordFee positive paid margin resource ordered
    oldHalf oldDirectory mounted allowance later shape pub vals j
    number same).2


end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.Diagonal.PhysicalStage.Run.StageOccurrence
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.NavigationPass Diagonal.TickWorkspace RAM RAM.NavigationNodeRows
open Diagonal.HistoryContraction Diagonal.NavigationDirectory HistoryPartyBatchExec HistoryStageBody.Physical
open HistoryStageSetup HistoryWordStepRun HistoryNodeDirectory.Selected NativeNavigation
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F Pins E : Type} [Field F] [Fintype F] {a l c k u K heads heap n fee levels degree : ℕ}
    {X : State a l} {R : Move F X c k} {i : Fin R.rules.count} {L : X.Words Pins}
    {step : R.WordStep Pins L i} {O : X.ArchiveSites} {pay : (R.next i).Site→ℕ}
    {row : R.ArchiveStep i O pay}
local notation "W" => (16*u^10)
local notation "V" => (volume u)
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "tag₀" => HistoryRefreshEmitter.tag (K:=F)
local notation "rom" => base u 38
local notation "keep₀" => TickTerminalRoot.slotKeep u
variable (B : Block F) {cur ctr : Word (16*u^10)} {mid out warm prev : Memory (16*u^10)} {b : Banks}
    {xs : List NodeRow} {D₀ : HistoryNodeDirectory.Selected.Directory (16*u^10) n} {j : Fin n} {vals : Fin n→NodeValue F}
    (seedCount : ℕ) (trees : Forest F L.ports.form) (orig : ∀ x,Fin (L.ext x)→E)
    (pointer : E→ℕ) (v : (R.next i).Site)
local notation "node" => row.sites.id v
local notation "rnk" => row.sites.ord v
local notation "entry" => bump (ownerData W u) prev
local notation "srcNode" => nodeOfSite step.words (step.nextForest trees) (pushedOrigin step orig) v
local notation "childN" h:arg => NodeValue.ofSite (nodeOfSite L trees orig (row.row.children v h).val)
  pointer (streamAt u seedCount (row.data.child rnk h)) (endsAt u seedCount (row.data.child rnk h))

/-- The stage packet after a true chronological lookup. The reads, old
half rows, and cache entries are those of the issued and warmed navigation. -/
structure Source (shape : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W) : Type where
  visit : RecordedWordStep K cur ctr heads heap mid Pins B.publicTemplate R i L step O pay row
  warmData : WarmSources u b xs mid out warm
  current : Ledger u D₀ tag₀ vals keep₀ warm j.val prev
  dir : warmDirectoryVisit b warm R i L step O pay row
  priorOrder : X.OrderedHalves L
  predecessor : State.HalfRows O (halfArchiveCell u) (numeric mid)
  successor : State.HalfRows row.sites (halfArchiveCell u) (numeric mid)
  pairs : 2*archiveColumn b (numeric out) node 1=step.words.ext v
  prior : ∀ h : Fin row.sites.layer.childCount,(childN h).Cached tag₀ u (row.data.child rnk h) entry
  charges : R.ResourceReceipt fee levels peak b (numeric out) L step O pay row
  priced : PricedAt b (numeric out) fee levels peak node srcNode
  allowance : B.archiveUnit u B.localCoefficient degree≤b.unitWork
  coefficient : (W+1)^3≤fee
  margin : 10*(levels+2)^2*fee≤b.unitWork
  unit : 0<b.unitWork
  age : 40≤u
  fixed : B.archiveConstant B.localCoefficient≤u
  index : j.val=node
  numbered : vals j=NodeValue.ofSite srcNode pointer (streamAt u seedCount node) (endsAt u seedCount node)
  later : seedCount≤node
  fits : node<V^2
  nodes : b.nodes=base u 44
  cash : b.charges=base u 43
  headsAbove : base u 20≤heads
  heapBelow : heap≤base u 40
  table : Mounted B W W rom warm
  tableSize : rom+libraryWords B W<2^W
  stridePos : 0<K
  strideFit : K<2^W
  counters : cur.val<ctr.val

variable {shape : TraceBucketAtom.Layout} {pub : Fin TraceEndpointROM.params→Word (16*u^10)}
local notation "physical" => Source (K:=K) (heads:=heads) (heap:=heap) (levels:=levels) (fee:=fee)
  (degree:=degree) (cur:=cur) (ctr:=ctr) (xs:=xs) (D₀:=D₀) (j:=j) (vals:=vals)
  (b:=b) (mid:=mid) (out:=out) (warm:=warm) (prev:=prev) (step:=step) (row:=row)
  B seedCount trees orig pointer v shape pub

/-- Native field bounds and directory values used by either branch. -/
private theorem Source.widths (s : physical) :
    2+V<2^W ∧ base u 60<2^W ∧ base u 18<2^W ∧ (entry (base u 18)).val=node+1 ∧
      step.words.ext v<2^W := by
  obtain ⟨big,_,_,_,bound⟩:=HistoryWordStepRanges.scale (u:=u) s.age s.fits (show 0≤V from Nat.zero_le _)
  have sq : V^2 ≤ Diagonal.TickWorkspace.stride u:=Nat.pow_le_pow_right (by omega) (by decide:2≤4)
  have smallV:V ≤ Diagonal.TickWorkspace.stride u:=Nat.le_self_pow (by decide : 4≠0) _
  have far:=Diagonal.TickWorkspace.word_space (u:=u) (i:=60) ((by decide : 1≤40).trans s.age) (by omega)
  change 20*Diagonal.TickWorkspace.stride u<2^W at bound
  have w : 2+V<2^W:=by omega
  have ctrl : base u 18<2^W:=by change 19*Diagonal.TickWorkspace.stride u<_;omega
  have feeBig : 2≤fee:=by
    have z : 2≤W+1:=by have:=s.age;have:=Nat.le_self_pow (by decide : 10≠0) u;omega
    exact z.trans ((Nat.le_self_pow (by decide : 3≠0) _).trans s.coefficient)
  exact ⟨w,(Nat.le_add_right _ _).trans_lt far,ctrl,
    (NativeNavigation.bumped_index s.current ctrl (by rw [s.index];have:=s.fits;omega)).trans (by rw [s.index]),
    (s.priced.native_words (u:=u) (by have:=s.age;omega) feeBig s.margin).2.1.trans_lt
      ((Nat.le_add_left V 2).trans_lt w)⟩

private theorem Source.rows (s : physical) :
    StageRows L step row v u b entry :=
  StageRows.of_bumped_source L step row v u s.current s.warmData s.visit s.dir
    (s.warmData.half_rows s.successor) s.pairs s.cash s.nodes s.headsAbove s.heapBelow s.fits s.age

private theorem Source.retained (s : physical) {issuedCursor : Cursor} {stop height : ℕ}
    (head : base u 20 ≤ issuedCursor.header) (bound : height≤heap) :
    (∀ a,(issuedCursor.header ≤ a ∧ a<stop ∨ heads≤a)→a<height→warm a=mid a) ∧
    ∀ a,(issuedCursor.header ≤ a ∧ a<stop ∨ heads≤a)→a<height→entry a=mid a := by
  have keep:=s.warmData.stage_frame (next:=stop) head s.headsAbove (bound.trans s.heapBelow)
  refine ⟨keep,?_⟩
  intro a lo hi
  have after : base u 20≤a:=lo.elim (fun h=>head.trans h.1) (fun h=>s.headsAbove.trans h)
  exact (NativeNavigation.bumped_kept s.current s.widths.2.2.1 (by unfold Diagonal.TickWorkspace.stride;positivity) a
    (.inr ((Nat.mul_le_mul_right _ (by decide:20≤21)).trans after))).trans (keep a lo hi)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
/-- Read the correct cached child and emit the single constructor recorded along
the selected chronological path. -/
theorem write_selected (s : physical) :
    let arm:=fun i:Fin n=>B.nativeArmTime levels fee b (numeric out) i.val
    (∃ f, (families B rom W).find? (matchesFamily u entry)=some f) ∧
    CacheWrite (archive B rom W K) shape pub (families B rom W) vals tag₀
      (B.nativeVisitCost levels fee b (numeric out)) arm (fun i _=>arm i) j entry := by
  classical
  have start:base u 19≤rom:=Nat.mul_le_mul_right _ (by decide : 20≤39)
  have area:base u 19≤heads:=(Nat.mul_le_mul_right _ (by decide:20≤21)).trans s.headsAbove
  have static : Mounted B W W rom entry:=by
    refine ⟨fun k=>?_⟩
    have kept:=NativeNavigation.bumped_kept s.current s.widths.2.2.1 (by unfold Diagonal.TickWorkspace.stride;positivity)
      (rom+k.val) (.inr (start.trans (Nat.le_add_right _ _)))
    exact kept.trans (s.table.words k)
  have past:=s.warmData.half_rows s.predecessor
  have atOld : State.HalfRows O (fun a=>keep₀ a ∧ a<2^W) (numeric warm):=
    past.transfer (fun _ _=>rfl) (fun i hi=>⟨Or.inr ((Nat.mul_le_mul_right _ (by decide:20≤21)).trans hi.1),
      hi.2.trans s.widths.2.1⟩)
  have kept (a) (lo : base u 19≤a) : entry a=warm a:=
    NativeNavigation.bumped_kept s.current s.widths.2.2.1 (by unfold Diagonal.TickWorkspace.stride;positivity) a (Or.inr lo)
  have atInput : State.HalfRows O (fun a=>base u 19≤a ∧ a<2^W) (numeric entry):=
    past.transfer (fun a hi=>congrArg Fin.val (kept a ((Nat.mul_le_mul_right _ (by decide:20≤21)).trans hi.1)))
      (fun a h=>⟨(Nat.mul_le_mul_right _ (by decide:20≤21)).trans h.1,h.2.trans s.widths.2.1⟩)
  have oldDir (k : Fin O.layer.count) : DirectoryRow b O.layer k entry:=by
    apply (s.dir.1 k).1.retain
    · intro field _
      apply kept
      rw [s.nodes]
      exact (Nat.mul_le_mul_right _ (by decide:20≤45)).trans
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · apply kept
      rw [s.cash]
      exact (Nat.mul_le_mul_right _ (by decide:20≤44)).trans
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have occurrence:=s.visit
  rcases occurrence with shrink|fresh
  · have authenticated:=shrink
    cases shrink with
    | @of_native T t degree' rem hD small A c branch original archived bits O₀ L₀
        fit hit stored arrays caps H roster numbered first row' chosen published saved extent allowed pubData =>
      obtain ⟨level,rfl,rfl,rfl⟩:=B.public_shrink allowed
      subst row'
      let order := shrinkPackOrder (B.exponent level.val) (2^B.exponent (level.val+1)) k A
      let move := shrinkBinary B.shrink (B.exponent level.val) (2^B.exponent (level.val+1)) k hD small A
      let elected := shrinkNextOrder B.shrink (B.exponent level.val)
        (2^B.exponent (level.val+1)) k hD small A branch ((move.next branch).chart.symm v)
      let site := order.symm elected
      have placed : order site=elected := order.apply_symm_apply elected
      have retained := Source.retained (B:=B) (seedCount:=seedCount) (trees:=trees)
        (orig:=orig) (pointer:=pointer) (v:=v) s (issuedCursor:=c) (stop:=c.header+64) arrays.header20_at extent
      apply HistoryShrinkEmitter.write_occurrence_with_selection (B:=B) (level:=level) (hD:=hD) (small:=small)
        (A:=A) (branch:=branch) (L:=L₀) (z:=v) (v:=site) (O:=roster) (old:=O₀)
        (numbered:=numbered) (first:=first) (b:=b) (seedCount:=seedCount) (trees:=trees)
        (orig:=orig) (pointer:=pointer) authenticated H caps arrays saved retained.2 area s.counters
        s.stridePos s.strideFit start s.tableSize s.age s.fixed s.widths.2.2.2.1 s.fits placed
        s.nodes s.cash s.rows s.prior s.coefficient s.unit s.charges s.margin s.priced
        s.priorOrder atInput oldDir static s.allowance s.later
        shape pub vals j s.index s.numbered
  · cases fresh with
    | native q limit saved bounds arrays words allowed =>
      have one : q.step.sites.layer.childCount=1:=by rw [q.issued_layer];rfl
      have listRoom : q.step.sites.layer.children+(q.step.sites.ord v).val*q.step.sites.layer.childCount<2^W:=by
        let k : Fin q.step.sites.layer.childCount:=⟨0,by omega⟩
        simpa only [k,Nat.add_zero] using ((s.rows.footprint.child _ k).2.trans s.widths.2.1)
      have halfRoom:=(s.rows.footprint.halves (q.step.sites.ord v)).2.trans s.widths.2.1
      exact NavigationPass.RefreshReceipt.write_occurrence_with_selection q B words v b s.current seedCount trees orig pointer
        allowed saved bounds arrays s.priorOrder s.charges s.allowance s.unit s.age s.fixed s.index s.fits
        s.nodes s.cash area limit start s.tableSize s.table
          (Source.retained (B:=B) (seedCount:=seedCount) (trees:=trees) (orig:=orig)
            (pointer:=pointer) (v:=v) s (issuedCursor:=q.cursor) (stop:=q.entry.next.header) arrays.header20_at limit).1
        (s.dir.2 _).1 (s.dir.1 _).1 atOld s.rows listRoom halfRoom s.widths.2.2.2.2 s.prior
        s.coefficient s.later shape pub s.margin s.priced s.numbered

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
/-- The cache-writing projection used by the original receiver. -/
theorem write (s : physical) :
    let arm:=fun i:Fin n=>B.nativeArmTime levels fee b (numeric out) i.val
    CacheWrite (archive B rom W K) shape pub (families B rom W) vals tag₀
      (B.nativeVisitCost levels fee b (numeric out)) arm (fun i _=>arm i) j entry := by
  exact (write_selected (B:=B) (seedCount:=seedCount) (trees:=trees) (orig:=orig) (pointer:=pointer) (v:=v) s).2


end
end ThreeFlat.Diagonal.PhysicalStage.Run.StageOccurrence

end OAI
