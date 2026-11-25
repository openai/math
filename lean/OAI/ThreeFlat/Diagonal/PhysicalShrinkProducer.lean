import OAI.ThreeFlat.Diagonal.PhysicalShrinkOutputData

namespace OAI
/-! # Publishing the binary successor, stage header and graph records -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast
noncomputable section
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPre
open private rawConditions tag_size from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "P" => shrinkRecordPacking s rem A
local notation "oldDegree" => (2^s : ℕ)
local notation "palette" => (2*oldDegree+1 : ℕ)
local notation "hc" => palette_two s
local notation "good" => rawConditions s rem (shrinkRecordState s rem A)
local notation "S" => shrinkStage s D
local notation "tagCount" => tagBits oldDegree
local notation "x" => dims S N tagCount rem
local notation "stagePad" => PhysicalShrink.padding palette oldDegree D
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
local notation "entry" => allocate K c (NavigationDirectory.Stage.shrink x)
local notation "p" => pointers K c x
local notation "C" => outgoing S N tagCount p
local notation "mid" => Prod.snd (Execution.run (shrinkChoices cur T) (Prod.snd (Execution.run (shrinkOld cur s D) m)))
local notation "commit" => Prod.snd (Execution.run (shrinkCostScans T cur K) mid)
local notation "code" => shrinkPublish cur K s D T

def shrinkPublishBudget (K : ℕ) (c : Cursor) :=
  let old:=DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x false) (NodeRecipe.after S K 1)
  let new:=DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x true) (NodeRecipe.after S K 1)
  shrinkDataTicks T cur K (shrinkBinaryFamily T s D rem hD small A).motifs+max old new+6

private theorem publication_read_intervals {wordBits alphabet : ℕ} {shape : Dimensions} {cursor : Cursor}
    {cell : Word wordBits} {mem : Memory wordBits} (space : CursorSpace cell mem cursor alphabet shape) :
    let cols := pointers alphabet cursor shape
    (∀ i k : ℕ, i < shape.motifs → k < 2 →
      let addr := cursor.heap + 3*i+k
      cursor.header+27 < addr ∧ addr < cols.supply ∧ addr < cols.newGraph ∧ addr < cols.costs) ∧
    (∀ i e : ℕ, i < shape.motifs → e < 2 →
      let addr := cols.demands+i*2+e
      cursor.header+27 < addr ∧ cols.supply+8*shape.motifs ≤ addr ∧
        cursor.heap+3*shape.motifs ≤ addr ∧ addr < cols.newGraph ∧ addr < cols.costs) ∧
    (∀ i j : ℕ, i < shape.motifs → j < alphabet →
      let addr := cursor.dense+i*alphabet+j
      addr < cursor.heap ∧ addr < cols.supply ∧ addr < cols.newGraph ∧ addr < cols.costs) := by
  dsimp only
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9⟩ := space.allocated
  have headerBound := space.earlier
  refine ⟨?_,?_,?_⟩
  · intro i k hi hk
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro i e hi he
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · intro i j hi hj
    have rows := Nat.mul_le_mul_left alphabet hi
    rw [Nat.mul_succ, Nat.mul_comm alphabet i] at rows
    have denseBound := space.counts
    exact ⟨by omega, by omega, by omega, by omega⟩

private theorem publication_ranges {wordBits alphabet : ℕ} {shape : Dimensions} {cursor : Cursor}
    {cell : Word wordBits} {mem : Memory wordBits} (space : CursorSpace cell mem cursor alphabet shape) :
    let cols := pointers alphabet cursor shape
    cols.costs+2*(shape.motifs+1) ≤ (allocate alphabet cursor (.shrink shape)).next.heap ∧
      (∀ i, (∀ a, Read shape cols a i) → i < cols.newGraph) ∧
      cols.newGraph+6*shape.newEdges ≤ cell.val ∧
      cols.newWidths+shape.newEdges*shape.residual ≤ cell.val := by
  dsimp only
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9⟩ := space.allocated
  have arena : (pointers alphabet cursor shape).costs+2*(shape.motifs+1) ≤
      (allocate alphabet cursor (.shrink shape)).next.heap := by
    change _ ≤ extraEnd shape ((pointers alphabet cursor shape).costs+2*(shape.motifs+1))
    rw [extra_extent]
    omega
  have finish := space.controls
  refine ⟨arena, ?_, ?_, ?_⟩
  · intro i persistent
    have head := space.earlier
    cases persistent (i+1) with
    | current same => omega
    | header h =>
      change cursor.header ≤ i ∧ i < cursor.header+34 at h
      omega
    | graph h =>
      change cursor.graph ≤ i ∧ i < cursor.graph+6*shape.oldEdges at h
      have := space.graph
      omega
    | widths h =>
      change cursor.width ≤ i ∧ i < cursor.width+shape.oldEdges*shape.originalLanes at h
      have := space.widths
      omega
    | sliced h => rcases h with ⟨_,hi⟩; omega
    | colors h => rcases h with ⟨_,hi⟩; omega
    | offsets h => rcases h with ⟨_,hi⟩; omega
    | issued h => rcases h with ⟨_,hi⟩; omega
  · omega
  · rw [←r9]
    exact (Nat.le_add_right ..).trans (arena.trans finish)


private theorem archive_intervals {wordBits alphabet : ℕ} {shape : Dimensions} {cursor : Cursor}
    {cell : Word wordBits} {mem : Memory wordBits} (space : CursorSpace cell mem cursor alphabet shape)
    (i : ℕ) (side : i < cursor.heap ∨ (allocate alphabet cursor (.shrink shape)).next.heap ≤ i) :
    let cols := pointers alphabet cursor shape
    (i < cols.newGraph ∨ (allocate alphabet cursor (.shrink shape)).next.heap ≤ i) ∧
    (i < cols.costs ∨ cols.costs + 2*(shape.motifs+1) ≤ i) ∧
    (i < cols.supply ∨ cols.supply + 8*shape.motifs ≤ i) ∧
    (i < cursor.heap ∨ cursor.heap + 3*shape.motifs ≤ i) ∧
    (i < cols.demands ∨ cols.newGraph ≤ i) := by
  dsimp only
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9⟩ := space.allocated
  have costEnd := (publication_ranges space).1
  rcases side with before | after
  · exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl before, Or.inl (by omega)⟩
  · exact ⟨Or.inr after, Or.inr (costEnd.trans after), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩

private theorem advanced_header {w n : ℕ} (address : Word w) (image : Memory w)
    (cursor : Cursor) (shape : Dimensions) (layout : Bool)
    (header : RAM.HeaderScan.Scans.Header address image cursor.header 63
      (DescriptorSpan.fields n cursor shape layout)) :
    (NextStage.memory address image address.val).val =
      (allocate n cursor (NavigationDirectory.Stage.shrink shape)).next.header := by
  simp only [NextStage.memory, writeMemory]
  exact (header.get 4 (by decide)).trans (by rfl)

private theorem layout_time_le (work : Bool → ℕ) (layout : Bool) :
    work layout ≤ max (work false) (work true) := by
  cases layout
  · exact le_max_left ..
  · exact le_max_right ..

private theorem seq_postcondition {w : ℕ} (first second : Recipe) (cell : Word w)
    (publicWord : Fin 1 → Word w) (input : Memory w) (post : Memory w → Prop)
    (proved : post (((second.install cell).execute cell publicWord
      (((first.install cell).execute cell publicWord input).2)).2)) :
    post ((((Recipe.seq first second).install cell).execute cell publicWord input).2) :=
  proved

private theorem descriptors_after {w : ℕ} (stage : Graph.Stage) (alphabet : ℕ)
    (cursor : Cursor) (shape : Dimensions) (layout : Bool) (cell : Word w)
    (publicWord : Fin 1 → Word w) (input : Memory w)
    (header : RAM.HeaderScan.Scans.Header cell input cursor.header 63
      (DescriptorSpan.fields alphabet cursor shape layout))
    (early : cursor.header+64 ≤ cursor.heap)
    (late : (allocate alphabet cursor (NavigationDirectory.Stage.shrink shape)).next.heap ≤ cell.val) :
    DescriptorSpan.PublishedDescriptors stage alphabet cursor shape layout cell 1
      (((afterRecipe stage).install cell).execute cell publicWord input).2
      (((NodeRecipe.after stage alphabet 1).install cell).execute cell publicWord input).2 := by
  let graphImage := (((afterRecipe stage).install cell).execute cell publicWord input).2
  let post := fun out => DescriptorSpan.PublishedDescriptors stage alphabet cursor shape layout cell 1 graphImage out
  have scan := DescriptorSpan.post_run stage alphabet cursor shape layout cell publicWord input header early late
  have reads : post ((((NodeRecipe.descriptors stage alphabet 1).install cell).execute cell publicWord graphImage).2) :=
    @DescriptorSpan.publish_descriptors w stage alphabet cursor shape layout cell 1 graphImage publicWord
      scan.header early late
  unfold NodeRecipe.after
  intro address row atWord
  exact @seq_postcondition w (afterRecipe stage) (NodeRecipe.descriptors stage alphabet 1) cell publicWord
    input post (@reads) address row atWord

private theorem publish_execution {w : ℕ} (cell : Word w)
    (alphabet bits target : ℕ) (table : ShrinkMotif.Table F) (input : Memory w) :
    let costs := shrinkCostScans table cell alphabet
    let receipt := costs.run input
    let scan := (NodeRecipe.after (shrinkStage bits target) alphabet 1).install cell
    let graph := scan.execute cell (fun _=>0) receipt.2
    let installed := shrinkPublish cell alphabet bits target table
    (installed.fits input ↔ costs.fits input ∧ scan.fits cell (fun _=>0) receipt.2) ∧
      (installed.run input).1 = receipt.1 + (graph.1 + 6) ∧
      (installed.run input).2 = NextStage.memory cell graph.2 := by
  refine ⟨?_,rfl,rfl⟩
  exact ⟨fun h=>⟨h.1,h.2.1⟩,fun h=>⟨h.1,h.2,trivial⟩⟩

attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin

private theorem published_copy_word {blocks wordBits alphabet control base : ℕ}
    (family : RecordFamily blocks) (fit : family.Fits alphabet wordBits)
    {data : HistogramRegister.Words family.motifs alphabet wordBits}
    {before after : Memory wordBits} (bank : HistogramRegister.BankLayout control (family.rows fit) data before)
    (atBase : AdmissionBank.descBase control before = base) (row : Fin family.motifs)
    (keep : after (base+3*row.val+0) = before (base+3*row.val+0)) :
    (after (base+3*row.val)).val = family.copies row := by
  have same : after (base+3*row.val) = before (base+3*row.val) := keep
  calc
    _ = (before (base+3*row.val)).val := congrArg (fun value : Word wordBits => value.val) same
    _ = family.copies row := by
      rw [← atBase]
      exact bank.copies row

section
attribute [local irreducible] Nat.pow tagBits shrinkCharge
set_option maxHeartbeats 1100000 in
set_option maxRecDepth 8192 in
private theorem publication_readbacks {fit : (Q).Fits K W} {raw : HistogramRegister.Words (Q).motifs K W}
    (prep : ShrinkPrefix T s D rem hD small A cur m c fit raw)
    (branch : Fin (M).rules.count)
    (accepted : ((Q).record fit).read (List.ofFn (HistogramRegister.bitTable raw)) = some branch)
    (committed : ShrinkCommitted (K:=K) T s D rem hD small A cur m c branch)
    (postMem outMem : Memory W)
    (postFrame : ∀ i, i < (p).newGraph → postMem i = commit i)
    (outFrame : ∀ i, i < (p).newGraph → outMem i = commit i) :
    (∀ a : (P).Motif, (postMem (c.heap+3*(shrinkRecordOrder s rem A a).val)).val =
      shrinkRecordCopies T s rem A a) ∧
    (∀ (q : (P).Motif) (e : Fin 2), (outMem ((p).demands+(shrinkRecordOrder s rem A q).val*2+e.val)).val =
      PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc q e) ∧
    (∀ a : (P).Motif, (postMem (c.heap+3*(shrinkRecordOrder s rem A a).val+1)).val =
      (RefreshDemandRows.tileNumber (PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc a) (T.base ∘ T.row)).val) ∧
    (∀ (i : Fin (Q).motifs) (v : (Q).alphabet i),
      c.dense+i.val*K+(Fintype.equivFin _ v).val ≠ c.header+27 →
      (outMem (c.dense+i.val*K+(Fintype.equivFin _ v).val)).val = (((Q).order branch i).val v).val) := by
  obtain ⟨choiceRange, demandRange, denseRange⟩ := publication_read_intervals prep.cursor
  have choiceRead (i : Fin (Q).motifs) (k : ℕ) (hk : k < 2) :
      postMem (c.heap+3*i.val+k) = mid (c.heap+3*i.val+k) := by
    obtain ⟨headRoom, supplyRoom, graphRoom, costRoom⟩ := choiceRange i.val k i.isLt hk
    exact (postFrame _ graphRoom).trans
      (committed.keep _ headRoom.ne' (Or.inl costRoom) (Or.inl supplyRoom))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    let i := shrinkRecordOrder s rem A a
    have db : AdmissionBank.descBase cur.val mid = c.heap := by
      change (mid ((mid cur.val).val+2)).val = c.heap
      rw [prep.cursor.header.pointer]
      exact prep.cursor.header.values 2 (by decide)
    have copies : (postMem (c.heap+3*i.val)).val = (Q).copies i :=
      published_copy_word Q fit prep.bank.2 db i (choiceRead i 0 (by decide))
    exact copies.trans (shrinkBinaryFamily_copies T s D rem hD small A a)
  · intro q e
    let row := shrinkRecordOrder s rem A q
    let addr := (p).demands+row.val*2+e.val
    obtain ⟨headRoom,supplyEnd,choiceEnd,graphRoom,costRoom⟩ := demandRange row.val e.val row.isLt e.isLt
    have same : outMem addr = ((shrinkOld cur s D).run m).2 addr :=
      (outFrame _ graphRoom).trans ((committed.keep _ headRoom.ne' (Or.inl costRoom) (Or.inr supplyEnd)).trans
        (prep.choiceFrame addr (Or.inr choiceEnd)))
    exact (congrArg Fin.val same).trans (prep.demandWords q e)
  · intro a
    let i := shrinkRecordOrder s rem A a
    have tile := prep.tiles i
    rw [Nat.mul_comm i.val 3] at tile
    have selected : (shrinkRecordOrder s rem A).symm i = a := Equiv.symm_apply_apply _ _
    rw [selected] at tile
    exact (congrArg Fin.val (choiceRead i 1 (by decide))).trans tile
  · intro i v apart
    let j : Fin K := (Fintype.equivFin _ v).castLE (fit.1 i)
    let addr := c.dense+i.val*K+j.val
    obtain ⟨_,supplyRoom,graphRoom,costRoom⟩ := denseRange i.val j.val i.isLt j.isLt
    have same : outMem addr = mid addr := (outFrame _ graphRoom).trans
      (committed.keep _ apart (Or.inl costRoom) (Or.inl supplyRoom))
    have db : AdmissionBank.denseBase cur.val mid = c.dense := by
      change (mid ((mid cur.val).val+1)).val = c.dense
      rw [prep.cursor.header.pointer]
      exact prep.cursor.header.values 1 (by decide)
    have word := congrArg Fin.val (prep.bank.2.words i j)
    rw [db,Nat.mul_comm K i.val] at word
    have rawEq := shrink_table_of_read T s D rem hD small A fit raw branch accepted
    have table := congrArg (fun words : HistogramRegister.Words (Q).motifs K W => (words i j).val) rawEq.symm
    exact (congrArg Fin.val same).trans (word.trans (table.trans ((Q).words_val fit branch i v)))

end

attribute [local irreducible] tagBits shrinkCharge Nat.pow

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem shrink_published {fit : (Q).Fits K W} {raw : HistogramRegister.Words (Q).motifs K W}
    (prep : ShrinkPrefix T s D rem hD small A cur m c fit raw)
    (branch : Fin (M).rules.count) (accepted : ((Q).record fit).read (List.ofFn (HistogramRegister.bitTable raw))=some branch)
    (committed : ShrinkCommitted (K:=K) T s D rem hD small A cur m c branch)
    (old : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀a j,supply branch a j≤top) (bound : top<2^W) :
    (code).fits mid ∧ ((code).run mid).1≤ shrinkPublishBudget T s D rem hD small A cur K c ∧
      ShrinkOutput (K:=K) T s D rem hD small A cur m c branch ((code).run mid).2 := by
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  let ht : 0<tagCount := by
    apply Nat.pos_of_ne_zero
    intro tagZero
    have enough := tag_size s
    rw [tagZero, pow_zero] at enough
    exact (Nat.lt_irrefl 1) enough
  let count:=shrinkPieceBound s D
  let graph:=successor (pad:=stagePad) S P (B).order count lay hc good ht
  let widths:=newWidth (pad:=stagePad) S P (B).order count lay hc good (supply branch)
  let num:=Template.tagNumber (t:=tagCount) (B).order
  let pub:=fun _:Fin 1=>(0:Word W)
  let result:=(((NodeRecipe.after S K 1).install cur).execute cur pub commit).2
  let out:=NextStage.memory cur result
  have cs:=prep.cursor
  have h:=shrink_output_bounds s D rem A hD old extra (supply branch) top size bound lay hc good ht
  have image:=materialized_with_keys (pad:=stagePad) good ht h.1 cs.separation committed.ready pub h.2.1 h.2.2
  have run:=DescriptorSpan.after_run S K c x lay cur pub commit committed.elected cs.earlier cs.controls 1
  have avoids:=DescriptorSpan.descriptor_avoids_graph_width S K c x lay cur pub commit committed.elected cs.earlier cs.controls 1
  have postStage:=DescriptorSpan.post_run S K c x lay cur pub commit committed.elected cs.earlier cs.controls
  have records : DescriptorSpan.PublishedDescriptors S K c x lay cur 1
      (((afterRecipe S).install cur).execute cur pub commit).2 result :=
    @descriptors_after W S K c x lay cur pub commit committed.elected cs.earlier cs.controls
  have eqDegree:=shrink_output_degree s D hD
  have edgeCount : N*2^tagCount*(liveDegree S+stagePad) = (x).newEdges :=
    congrArg (fun degree=>N*2^tagCount*degree) eqDegree
  have widthCount : N*2^tagCount*(liveDegree S+stagePad)*2^rem = (x).newEdges*(x).residual :=
    congrArg (fun rows=>rows*2^rem) edgeCount
  have «meta» : SlotImage.Stored graph num (tagOrdinal rem) C (fun i=>(result i).val) widths := by
    apply descriptors_preserve graph num (tagOrdinal rem) C widths S K 1 cur pub commit image.1 avoids.1
    rw [widthCount]
    exact avoids.2
  obtain ⟨newHeap,inputRange,graphLimit,widthLimit⟩ := publication_ranges cs
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9⟩ := cs.allocated
  have endMem := cs.controls
  have start := cs.earlier
  have keep (i : ℕ) (other : i≠cur.val) : out i=result i := by
    simp only [out,NextStage.memory,writeMemory,ite_eq_right other]
  have graphEnd : (C).graph+6*(C).rows≤cur.val := graphLimit
  have widthEnd : (C).widths+N*2^tagCount*(liveDegree S+stagePad)*2^rem≤cur.val := by
    rw [eqDegree]
    exact widthLimit
  have safe : SlotImage.Stored graph num (tagOrdinal rem) C (fun i=>(out i).val) widths :=
    «meta».frame (fun i _ hi=>congrArg Fin.val (keep i (hi.trans_le graphEnd).ne))
      (fun i _ hi=>congrArg Fin.val (keep i (hi.trans_le widthEnd).ne))
  have clockBound : DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x lay) (NodeRecipe.after S K 1)≤
      max (DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x false) (NodeRecipe.after S K 1))
        (DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x true) (NodeRecipe.after S K 1)) := by
    exact layout_time_le (fun bit=>DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x bit)
      (NodeRecipe.after S K 1)) lay
  have machine := publish_execution cur K s D T mid
  refine ⟨machine.1.mpr ⟨committed.fits,run.fits⟩,?_,?_⟩
  · rw [machine.2.1,committed.clocks,run.clocks]
    exact (Nat.add_le_add_left (Nat.add_le_add_right clockBound 6) _).trans_eq (Nat.add_assoc ..).symm
  · rw [machine.2.2]
    change ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out
    obtain ⟨copiesRead,demandRead,shapeRead,histogramRead⟩ :=
      publication_readbacks T s D rem hD small A cur m c prep branch accepted committed
        (((afterRecipe S).install cur).execute cur pub commit).2 out
        (fun i hi => postStage.frame i (Or.inl hi))
        (fun i hi => (keep i (by omega)).trans (run.frame i (Or.inl hi)))
    refine ⟨?_,shrink_stored_at T s D rem hD small A branch count ht C _ safe,committed.ready,?_,?_,?_,?_,?_,?_,?_,ht,safe,image.1,postStage.header,?_,prep.entryCursor,copiesRead,demandRead,shapeRead,histogramRead,fit⟩
    · exact advanced_header cur result c x lay run.header
    · intro i hi
      rw [keep _ (by omega)]
      exact run.header.values i hi
    · intro i ctrl header side
      have motifCount : (Q).motifs = (x).motifs := rfl
      obtain ⟨post, costs, supplyRange, choices, old⟩ := archive_intervals cs i side
      exact (keep i ctrl).trans ((run.frame i post).trans
        ((committed.keep i header (by rw [motifCount]; exact costs) (by rw [motifCount]; exact supplyRange)).trans
        ((prep.choiceFrame i (by rw [motifCount]; exact choices)).trans (prep.oldFrame i old))))
    · exact records.frameOut (fun i hi=>keep i (hi.trans_le endMem).ne)
    · exact fun i hi=>keep i (hi.trans_le endMem).ne
    · intro a persistent
      have earlier:=inputRange a persistent
      exact (keep a (by omega)).trans (run.frame a (.inl earlier))
    · intro kernel pointer
      apply committed.ready.frameWith kernel pointer
      intro i persistent
      have earlier := inputRange i persistent
      exact (keep i (by omega)).trans (run.frame i (.inl earlier))
    · intro u
      let a:=(p).keys+SlotImage.ordinal num u
      have boundSlot : SlotImage.ordinal num u<(x).newEdges :=
        (SlotImage.ordinal_lt num u).trans_le edgeCount.le
      have before : a<(p).costs+2*((x).motifs+1) := by dsimp only [a];omega
      have metaRun:=DescriptorSpan.descriptor_run S K c x lay cur pub _ postStage.header cs.earlier cs.controls 1
      have untouched : out a = result a :=
        keep a (before.trans_le (newHeap.trans endMem)).ne
      have savedKey : result a = (((afterRecipe S).install cur).execute cur pub commit).2 a :=
        seq_postcondition (afterRecipe S) (NodeRecipe.descriptors S K 1) cur pub commit
          (fun memory=>memory a = (((afterRecipe S).install cur).execute cur pub commit).2 a)
          (metaRun.frame a (.inl before))
      exact (untouched.trans savedKey).trans (image.2 u)
    · exact committed.ready.frameWith cur postStage.header.pointer
        (fun i persistent=>postStage.frame i (.inl (inputRange i persistent)))



end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
