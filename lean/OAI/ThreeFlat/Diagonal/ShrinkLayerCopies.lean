import OAI.ThreeFlat.Diagonal.ShrinkArchiveStep
import OAI.ThreeFlat.Diagonal.ShrinkLayerData
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCharges
import OAI.ThreeFlat.Diagonal.PhysicalShrinkPublished

namespace OAI
/-! # Copy totals in the published occupied-motif rows -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.Placement Native.Graph MotifKernel PhysicalShrink
open Native.ShrinkStage.Resident
open NavigationDirectory NavigationPass ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "t" => CompressorPacking.tagBits (2^s)
local notation "packSite" => Computability.VPVNP.Compression.Site (State.Base (shrinkRecordState s rem A)) (BitWord t) (BitWord rem)
local notation "S" => shrinkStage s D
local notation "x" => dims S (Fintype.card (State.Base (shrinkRecordState s rem A))) t rem
local notation "supply" => shrinkIssuedWords T s D rem hD small A

section ArchiveAssembly

/-- The typed archive step used by the journal is recovered from the true native output,
including the predecessor's separate parent-ordinal bank. -/
theorem shrink_archive_step_at_scale {u K : ℕ} (hu : 40≤u) (cur : Word (16*u^10))
    (m out : Memory (16*u^10)) (c : Cursor) (branch : Fin (M).rules.count)
    (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : shrinkFixedWords T s D≤u) (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) (offset : 0<c.width) (ids : (allocate K c (.shrink x)).next.node≤2^(16*u^10))
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node) :
    ∃ step : (M).ArchiveStep branch old (shrinkBinaryCharge T s D rem hD small A branch),
      let en:=allocate K c (.shrink x)
      let owner:=fun j:Fin old.layer.count=>(step.sites.ord ((M).parent branch (old.ord.symm j))).val
      let mem:=fun i=>(out i).val
      step.sites.Numbered ∧ step.sites.layer=nodeLayer K c (.shrink x) ∧ step.ownerPtr=en.words 44 ∧
      step.data.Reads mem ∧ step.data.Below en.next.heap mem ∧
      step.data.Footprint (fun i=>c.heap≤ i ∧ i<en.next.heap) mem ∧
      ParentReads ⟨false,step.sites.layer.first,step.ownerPtr⟩ owner mem ∧
      (∀ j : Fin old.layer.count,c.heap≤ step.ownerPtr+j.val ∧ step.ownerPtr+j.val<en.next.heap) ∧
      (∀ j,(step.data.halfWidth j).length≤ stageHalves (.shrink x)) ∧
      (∀ j,(step.data.motifCopies j).length≤ stageMotifs (.shrink x)) ∧
      ∃ O : ∀v : packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v (16*u^10),
        step=shrinkArchiveStep (K:=K) T s D rem hD small A c branch O old numbered first := by
  obtain ⟨O,reads,below,safe,halves,motifs⟩:=shrink_layer_footprint_at_scale T s D rem hD small A hu cur m out c branch H fixed arena wire offset ids
  let step:=shrinkArchiveStep (K:=K) T s D rem hD small A c branch O old numbered first
  refine ⟨step,shrinkArchive_numbered T s D rem hD small A c branch,rfl,rfl,reads,below,safe,?_⟩
  have entry (j : Fin old.layer.count) :
      (out (step.ownerPtr+j.val)).val=(step.sites.ord ((M).parent branch (old.ord.symm j))).val ∧
      c.heap≤ step.ownerPtr+j.val ∧ step.ownerPtr+j.val<(allocate K c (.shrink x)).next.heap := by
    let v:=old.ord.symm j
    have position : ChildRows.oldNumber P (B).order (shrinkOldPosition s rem A v)=j.val := by
      rw [shrinkOldPosition_number]
      exact (numbered v).symm.trans (congrArg Fin.val (old.ord.apply_symm_apply j))
    have y := shrink_owner_at_scale T s D rem hD small A hu cur m out c branch H fixed arena wire (shrinkOldPosition s rem A v)
    rw [position,←shrink_parent_number] at y
    exact ⟨y.1.trans ((shrinkArchive_numbered (K:=K) T s D rem hD small A c branch) _).symm,y.2⟩
  exact ⟨fun _ j=>(entry j).1,fun j=>(entry j).2,halves,motifs,O,rfl⟩

/-- The native prefix and last width are the sum of the ordered list used by
the S43 projection of this exact shrink row. -/
theorem shrinkArchiveStep_tail {K W : ℕ} (c : Cursor) (branch : Fin (M).rules.count)
    (O : ∀v : packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v W)
    (old : A.ArchiveSites) (_numbered : old.Numbered) (_first : old.layer.first=c.node)
    {safe : ℕ→Prop} {m : ℕ→ℕ}
    (hr : State.HalfRows (shrinkArchiveSites (K:=K) T s D rem hD small A c branch) safe m) :
    let data:=shrinkLayerData T s D rem hD small A (K:=K) c branch O
    data.Tail m ∧ data.TailCells safe m := by
  let X:=(M).next branch
  let y:=shrinkNextOrder T s D rem hD small A branch
  let sites:=shrinkArchiveSites (K:=K) T s D rem hD small A c branch
  let data:=shrinkLayerData T s D rem hD small A (K:=K) c branch O
  let z:=fun j:Fin (x).outputSites=>sites.ord.symm j
  let last : Fin (2*D):=⟨2*D-1,by omega⟩
  have ix (j:Fin (x).outputSites) : sites.ord (z j)=j := sites.ord.apply_symm_apply j
  have co (j:Fin (x).outputSites) : X.chart.symm (z j)=y.symm j := by
    change X.chart.symm (X.chart (y.symm j))=_
    exact X.chart.symm_apply_apply _
  have len (j:Fin (x).outputSites) : (data.halfWidth j).length=2*D := List.length_ofFn
  refine ⟨?_,⟨?_,?_⟩⟩
  · intro j pos
    have w:=hr.width (z j) last
    have p:=hr.start (z j) last
    change m (m (sites.layer.incident+(sites.ord (z j)).val*2+1)+4*last.val+2)=_ at w
    change m (m (sites.layer.incident+(sites.ord (z j)).val*2+1)+4*last.val+3)=_ at p
    rw [ix j,co j] at w p
    change m (m (sites.layer.incident+j.val*2+1)+4*((data.halfWidth j).length-1)+3)+
      m (m (sites.layer.incident+j.val*2+1)+4*((data.halfWidth j).length-1)+2)=(data.halfWidth j).sum
    rw [len j]
    change m (m (sites.layer.incident+j.val*2+1)+4*last.val+3)+
      m (m (sites.layer.incident+j.val*2+1)+4*last.val+2)=_
    rw [p,w]
    change Halves.prefixValue X.graph X.width (y.symm j) last+
      X.width (Halves.sourceHalf X.graph (y.symm j) last)=
        (List.ofFn (fun i : Fin (2*D)=>X.width (Halves.sourceHalf X.graph (y.symm j) i))).sum
    rw [List.sum_ofFn]
    exact half_tail_total (N:=2*D) (Nat.mul_pos (by decide : 0<2) hD)
      (fun i=>X.width (Halves.sourceHalf X.graph (y.symm j) i))
  · intro j k
    have read:=hr.headerSafe (z j) k
    change safe (sites.layer.incident+(sites.ord (z j)).val*2+k.val) at read
    rw [ix j] at read
    exact read
  · intro j pos
    have lo:=hr.entriesSafe (z j) last 2
    have hi:=hr.entriesSafe (z j) last 3
    change safe (m (sites.layer.incident+(sites.ord (z j)).val*2+1)+4*last.val+2) at lo
    change safe (m (sites.layer.incident+(sites.ord (z j)).val*2+1)+4*last.val+3) at hi
    rw [ix j] at lo hi
    dsimp only
    rw [len j]
    exact ⟨lo,hi⟩


end ArchiveAssembly

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalStage NavigationDirectory CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident

/-- A saved shrink receipt is indexed by the very move, histogram, predecessor order,
charge, and archive row selected by the native journal. -/
inductive ShrinkVisit {F : Type} [Field F] {W : ℕ} (K : ℕ) (cur ctr : Word W)
    (headerEnd heapEnd : ℕ) (final : Memory W) :
    {d l D L : ℕ} → {A : State d l} → (R : Move F A D L) → (b : Fin R.rules.count) →
    (old : A.ArchiveSites) → (charge : (R.next b).Site→ℕ) → R.ArchiveStep b old charge → Prop where
  | of_native {T : ShrinkMotif.Table F} {s D rem : ℕ} {hD : 0<D}
      {small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024}
      {A : State (2^s) (shrinkCharge s+rem)} {c : Cursor}
      {b : Fin (shrinkBinary T s D rem hD small A).rules.count} {mid out : Memory W} {raw : List Bool}
      {old : A.ArchiveSites}
      (fit : (shrinkBinaryFamily T s D rem hD small A).Fits K W)
      (hit : let code:=(shrinkBinaryFamily T s D rem hD small A).record fit
             code.read (raw.take code.width)=some b)
      (stored : SlotImage.Stored A.graph A.order (tagOrdinal _)
        (RefreshStageNav.oldColumns c (Fintype.card A.Base) (2^s)) (fun i=>(mid i).val) A.width)
      (oldArrays : RecordedArrayBounds W headerEnd c A)
      (caps : ShrinkNativeCaps T s D rem W A)
      (output : ShrinkOutput (K:=K) T s D rem hD small A cur mid c b out)
      (O : ∀ site, Incidents.SiteOrder (S:=shrinkStage s D) (shrinkRecordPacking s rem A) (shrinkRecordState s rem A).order
        (ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A b)) site W)
      (numbered : old.Numbered) (first : old.layer.first=c.node)
      {row : (shrinkBinary T s D rem hD small A).ArchiveStep b old (shrinkBinaryCharge T s D rem hD small A b)}
      (chosen : row=shrinkArchiveStep (K:=K) T s D rem hD small A c b O old numbered first)
      (publishedHalves : State.HalfRows row.sites (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val))
      (saved : let x:=dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base) (CompressorPacking.tagBits (2^s)) rem
               let next:=(allocate K c (.shrink x)).next
               SavedFrame cur ctr headerEnd next.header next.heap out final)
      (extent : let x:=dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base) (CompressorPacking.tagBits (2^s)) rem
                (allocate K c (.shrink x)).next.heap≤heapEnd) :
      ShrinkVisit K cur ctr headerEnd heapEnd final (shrinkBinary T s D rem hD small A) b old
        (shrinkBinaryCharge T s D rem hD small A b) row

theorem ShrinkVisit.transfer {F : Type} [Field F] {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final final' : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkVisit K cur ctr headerEnd heapEnd final R b old charge row)
    (same : ∀ i,i<heapEnd→final' i=final i) :
    ShrinkVisit K cur ctr headerEnd heapEnd final' R b old charge row := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent =>
    exact .of_native fit hit stored oldArrays caps output O numbered first chosen
      (halves.transfer (fun i hi=>congrArg Fin.val (same i hi.2)) (fun _ h=>h)) (saved.transfer extent same) extent

theorem ShrinkVisit.halfRows {F : Type} [Field F] {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkVisit K cur ctr headerEnd heapEnd final R b old charge row)
    : State.HalfRows row.sites (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent =>exact halves

theorem ShrinkVisit.halfTail {F : Type} [Field F] {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkVisit K cur ctr headerEnd heapEnd final R b old charge row)
    : row.data.Tail (fun i=>(final i).val) ∧
      row.data.TailCells (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent =>
    rw [chosen] at halves ⊢
    exact shrinkArchiveStep_tail _ _ _ _ _ _ _ _ _ O _ numbered first halves


end ThreeFlat.Diagonal.NavigationPass

end OAI
