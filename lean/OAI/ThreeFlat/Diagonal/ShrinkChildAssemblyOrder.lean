import OAI.ThreeFlat.Diagonal.HistorySelectedChronology
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly
import OAI.ThreeFlat.Diagonal.ShrinkLayerCopies
import OAI.ThreeFlat.RAM.HistoryNodeDirectoryRow

namespace OAI
/-! # Child array order in the physical shrink assembler and the native S44 archive -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM RAM Computability.VPVNP.Compression CompressorPacking HistoryContraction
open Native Native.ShrinkStage Native.Placement PhysicalShrink
open NavigationDirectory NavigationPass
open private oldNumber_injective oldNumber_split shrinkPackedSuccessor archive_branch_read from OAI.ThreeFlat.Diagonal.ShrinkArchiveStep
open private sitesAfterCast from OAI.ThreeFlat.Diagonal.ShrinkArchiveTransport
open scoped Classical
noncomputable section
variable {F Pins : Type} [Field F]

def State.laneWords {d l l' : ℕ} (e : l=l') (A : State d l) (L : A.Words Pins) :
    (e ▸ A : State d l').Words Pins := by cases e;exact L

/-- Reindex the old sites along the shrink input lane equality. -/
abbrev laneSite {d l l' : ℕ} (e : l=l') (A : State d l) :
    A.Site ≃ (e ▸ A : State d l').Site := sitesAfterCast e A

/-- Keep the original S44 layer and number its recast sites by their old ordinals. -/
def priorSites {d l l' : ℕ} (e : l=l') (A : State d l) (O : A.ArchiveSites) :
    (e ▸ A : State d l').ArchiveSites :=
  ⟨O.layer,(laneSite e A).symm.trans O.ord⟩

section LaneTransfer
variable {d l l' : ℕ} (e : l=l') (A : State d l) (O : A.ArchiveSites)
  (L : A.Words Pins)

@[simp] theorem priorSites_ord (z : A.Site) :
    (priorSites e A O).ord (laneSite e A z)=O.ord z := by
  change O.ord ((laneSite e A).symm (laneSite e A z))=_
  rw [Equiv.symm_apply_apply]

@[simp] theorem priorSites_id (z : A.Site) :
    (priorSites e A O).id (laneSite e A z)=O.id z := by
  change O.layer.first+((priorSites e A O).ord (laneSite e A z)).val=O.layer.first+(O.ord z).val
  rw [priorSites_ord]

theorem laneNumbered (h : O.Numbered) : (priorSites e A O).Numbered := by
  cases e
  exact h

theorem laneOrdered (h : A.OrderedHalves L) :
    (e ▸ A : State d l').OrderedHalves (A.laneWords e L) := by
  cases e
  exact h

@[simp] theorem laneHalfBits (z : A.Site) :
    (A.laneWords e L).ports.halfBits (laneSite e A z)=L.ports.halfBits z := by
  cases e
  rfl

@[simp] theorem laneExt (z : A.Site) :
    (A.laneWords e L).ext (laneSite e A z)=L.ext z := by
  cases e
  rfl

theorem laneHalfRows {safe : ℕ→Prop} {mem : ℕ→ℕ} (h : State.HalfRows O safe mem) :
    State.HalfRows (priorSites e A O) safe mem := by
  cases e
  exact h

theorem laneDirectory {W : ℕ} {banks : RAM.NavigationNodeRows.Banks} {mem : Memory W} (z : A.Site)
    (h : RAM.HistoryStageSetup.DirectoryRow banks O.layer (O.ord z) mem) :
    RAM.HistoryStageSetup.DirectoryRow banks (priorSites e A O).layer
      ((priorSites e A O).ord (laneSite e A z)) mem := by
  rw [priorSites_ord]
  exact h

end LaneTransfer

/-- Check a numerical child clause simultaneously for every term, site and slot. -/
private def ChildrenAt {d l D m : ℕ} {A : State d l} {R : Move F A D m}
    (J : R.Assembler Pins) (test : ℕ→ℕ→ℕ→ℕ→Prop) : Prop :=
  ∀L i v j,test i.val (Halves.siteNumber (R.next i).order ((R.next i).chart.symm v)) j.val
    (Halves.siteNumber A.order (A.chart.symm (((J L i).children v j).val)))

private theorem childrenAt_degree {d l D D' m : ℕ} {A : State d l} (e : D=D') (R : Move F A D m)
    (J : R.Assembler Pins) (test : ℕ→ℕ→ℕ→ℕ→Prop) (h : ChildrenAt J test) :
    ChildrenAt (Move.castAssembler e R J) test := by cases e;exact h

private theorem childrenAt_lanes {d l l' D m : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) (test : ℕ→ℕ→ℕ→ℕ→Prop)
    (h : ChildrenAt J test) : ChildrenAt (Move.inputAssembler e A R J) test := by cases e;exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem shrinkMove_childrenAt {d lanes rem h t D : ℕ} (T : ShrinkMotif.Table F)
    (A : State d lanes) (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<d) (hD : 0<D)
    (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D≤1/1024) (tagSize : 1<2^t)
    (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) (test : ℕ→ℕ→ℕ→ℕ→Prop)
    (verify : ∀ (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
      (v : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)) (j : Fin (d*2^(2*d+1))),
      let hc : 2≤2*d+1 := by omega
      let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm i
      let lay := ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code hc hist)
      test i.val (Incidents.siteNumber A.order v) j.val
        (Halves.siteNumber A.order ((StageAddress.splitSite u).symm ((Owner.childOrder P lay v j).val)))) :
    ChildrenAt (Pins:=Pins) (shrinkMove_assembler T A u P agree good hd hD small tagSize code order) test := by
  unfold shrinkMove_assembler
  apply childrenAt_degree
  intro L i v j
  have row : Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((v.1,v.2.1),v.2.2)=
      Incidents.siteNumber A.order v := by
    simp [Halves.siteNumber,Incidents.siteNumber,productOrder,finProdFinEquiv_apply_val]; ring
  let lay:=ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code (by omega : 2≤2*d+1)
    ((Fintype.equivFin (shrinkBranches T A u P hd code)).symm i))
  let old:=(StageAddress.splitSite u).symm ((Owner.childOrder P lay v j).val)
  change test i.val (Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((v.1,v.2.1),v.2.2)) j.val
    (Halves.siteNumber A.order (A.chart.symm (A.chart old)))
  rw [row,A.chart.symm_apply_apply]
  exact verify i v j

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*2^s+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A
local notation "packed" => Computability.VPVNP.Compression.Site (State.Base (shrinkRecordState s rem A)) (BitWord (CompressorPacking.tagBits (2^s))) (BitWord rem)
set_option quotPrecheck false in
local notation "assembler" => (shrinkBinary_assembler T s D rem hD small A : (M).Assembler Pins)

open Lean Elab Term in
local elab "childPopulation% " i:term:max : term => do
  let index ← elabTerm i none
  let domain ← Meta.whnf (← Meta.inferType index)
  unless domain.isAppOfArity ``Fin 1 do throwError "expected a histogram ordinal; found {domain}"
  let cardinal := domain.getAppArgs[0]!.consumeMData
  unless cardinal.isAppOfArity ``Fintype.card 2 do
    throwError "expected a finite histogram population; found cardinality {cardinal}"
  return ← instantiateMVars cardinal.getAppArgs[1]!

private def shrinkChildTest (i next ord prior : ℕ) : Prop :=
  ∀ (b : Fin (M).rules.count) (z : packed) (t : Fin (2^s*2^(2*2^s+1))),
    i=b.val → next=Incidents.siteNumber (B).order z → ord=t.val →
      prior=ChildRows.oldNumber P (B).order ((Owner.childOrder P (ShrinkMotif.chooseWidths (supply b)) z t).val)

private theorem oldNumber_unpacked (q : ChildRows.Actual P) :
    Halves.siteNumber (B).order ((StageAddress.splitSite (shrinkRecordLane s rem)).symm q) =
      ChildRows.oldNumber P (B).order q := by
  have eqv := oldNumber_split s rem A ((StageAddress.splitSite (shrinkRecordLane s rem)).symm q)
  rw [Equiv.apply_symm_apply] at eqv
  exact eqv.symm

section
attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin ShrinkMotif.chooseWidths

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem shrink_child_number_at {population : Fintype (shrinkRecordHists T s rem A)}
    (i : Fin (@Fintype.card _ population)) (z : packed) (j : Fin (2^s*2^(2*2^s+1))) :
    let words := issued T P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A)
      (by have := Nat.two_pow_pos s; omega : 2≤2*2^s+1) ((@Fintype.equivFin _ population).symm i)
    shrinkChildTest T s D rem hD small A i.val (Incidents.siteNumber (B).order z) j.val
      (Halves.siteNumber (B).order ((StageAddress.splitSite (shrinkRecordLane s rem)).symm
        ((Owner.childOrder P (ShrinkMotif.chooseWidths words) z j).val))) := by
  dsimp only [shrinkChildTest]
  intro b v t ib zv jt
  have siteEq : z=v := (shrinkPackOrder s D rem A).injective (Fin.ext
    ((shrinkPackOrder_val s D rem A z).trans (zv.trans (shrinkPackOrder_val s D rem A v).symm)))
  have num : j=t := Fin.ext jt
  subst z
  subst j
  have words := archive_branch_read T s D rem hD small A b (fin := population) i ib
  exact (congrArg (fun wordData => Halves.siteNumber (B).order
    ((StageAddress.splitSite (shrinkRecordLane s rem)).symm
      ((Owner.childOrder P (ShrinkMotif.chooseWidths wordData) v t).val))) words).trans (oldNumber_unpacked s rem A _)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem shrink_numbers_from_raw (test : ℕ→ℕ→ℕ→ℕ→Prop)
    (raw : ChildrenAt (Pins := Pins) (shrinkRaw_assembler T s D rem hD small B) test) :
    ChildrenAt (Pins := Pins) assembler test := by
  unfold shrinkBinary_assembler
  apply childrenAt_lanes
  exact raw

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem shrink_assembly_numbers :
    ChildrenAt (Pins := Pins) assembler (shrinkChildTest T s D rem hD small A) := by
  apply shrink_numbers_from_raw
  unfold shrinkRaw_assembler
  apply shrinkMove_childrenAt
  intro i z j
  exact shrink_child_number_at T s D rem hD small A (population := childPopulation% i) i z j

end

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
/-- The stage's chosen dependent-site numbering gives exactly the child
ordinal read by the successor's native array, including every surviving lane. -/
theorem shrink_childrenAt (L : A.Words Pins) (branch : Fin (M).rules.count) (v : ((M).next branch).Site)
    (j : Fin ((assembler L branch).stage.count (Move.WordStep.targetSite (R:=M) (i:=branch) v)))
    (k : Fin (2^s*2^(2*2^s+1))) (same : j.val=k.val) :
    ((assembler L branch).children v j).val=(shrinkChildFiber T s D rem hD small A branch v k).val := by
  have numbers := shrink_assembly_numbers (Pins := Pins) T s D rem hD small A
  let U:=shrinkOldPosition s rem A
  let V:=shrinkPackedSuccessor T s D rem hD small A branch
  have nextOrd : Halves.siteNumber ((M).next branch).order (((M).next branch).chart.symm v)=Incidents.siteNumber (B).order (V v) := by
    rw [←shrinkNextOrder_val,←shrinkPackOrder_val]
    change _=(shrinkPackOrder s D rem A ((shrinkPackOrder s D rem A).symm _)).val
    rw [Equiv.apply_symm_apply]
    rfl
  have atOld := numbers L branch v j branch (V v) k rfl nextOrd same
  apply U.injective
  apply oldNumber_injective P (B).order
  rw [shrinkOldPosition_number]
  change _=ChildRows.oldNumber P (B).order (U (U.symm ((Owner.childOrder P (ShrinkMotif.chooseWidths (supply branch)) (V v) k).val)))
  rw [U.apply_symm_apply]
  exact atOld

theorem shrink_childOrder {K W : ℕ} (c : Cursor) (branch : Fin (M).rules.count)
    (order : ∀ v : packed,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node) (L : A.Words Pins) :
    (assembler L branch).ChildOrder (shrinkArchiveStep (K:=K) T s D rem hD small A c branch order old numbered first) := by
  intro v j
  exact (shrink_childrenAt T s D rem hD small A L branch v _ j rfl).symm

end

end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalStage NavigationDirectory CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident

/-- The native receipt also fixes the emitted assembler on the current physical words.
All saved arrays, the child chart and the assembled kernel use the same shrink term. -/
inductive ShrinkWordVisit {F Pins : Type} [Field F] {W : ℕ} (K : ℕ) (cur ctr : Word W)
    (headerEnd heapEnd : ℕ) (final : Memory W) (allow : StaticMotif F→Prop := fun _=>True) :
    {d l D L : ℕ} → {A : State d l} → (R : Move F A D L) → (b : Fin R.rules.count) →
    (L₀ : A.Words Pins) → R.WordStep Pins L₀ b → (old : A.ArchiveSites) → (charge : (R.next b).Site→ℕ) → R.ArchiveStep b old charge → Prop where
  | of_native {T : ShrinkMotif.Table F} {s D rem : ℕ} {hD : 0<D}
      {small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024}
      {A : State (2^s) (shrinkCharge s+rem)} {c : Cursor}
      {b : Fin (shrinkBinary T s D rem hD small A).rules.count} {mid out : Memory W} {raw : List Bool}
      {old : A.ArchiveSites} {L₀ : A.Words Pins}
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
                (allocate K c (.shrink x)).next.heap≤heapEnd)
      (permitted : allow (.shrink s D T))
      (publishedData : row.data.Reads (fun i=>(final i).val) ∧
        row.data.Footprint (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val)) :
      ShrinkWordVisit K cur ctr headerEnd heapEnd final allow (shrinkBinary T s D rem hD small A) b L₀
        (shrinkBinary_assembler T s D rem hD small A L₀ b) old
        (shrinkBinaryCharge T s D rem hD small A b) row

theorem ShrinkWordVisit.transfer {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final final' : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {L₀ : A.Words Pins} {wstep : R.WordStep Pins L₀ b} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L₀ wstep old charge row)
    (same : ∀ i,i<heapEnd→final' i=final i) :
    ShrinkWordVisit K cur ctr headerEnd heapEnd final' allow R b L₀ wstep old charge row := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent permitted published =>
    have equal (i : ℕ) (hi : headerEnd≤ i ∧ i<heapEnd) : (final' i).val=(final i).val :=
      congrArg Fin.val (same i hi.2)
    exact .of_native fit hit stored oldArrays caps output O numbered first chosen
      (halves.transfer equal (fun _ h=>h)) (saved.transfer extent same) extent permitted
      ⟨published.1.of_footprint published.2 equal,published.2.transfer published.2 equal⟩

theorem ShrinkWordVisit.erase {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {L₀ : A.Words Pins} {wstep : R.WordStep Pins L₀ b} {old : A.ArchiveSites}
    {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L₀ wstep old charge row) :
    ShrinkVisit K cur ctr headerEnd heapEnd final R b old charge row := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent permitted =>
    exact .of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent

theorem ShrinkWordVisit.childOrder {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L} {b : Fin R.rules.count}
    {L₀ : A.Words Pins} {wstep : R.WordStep Pins L₀ b} {old : A.ArchiveSites}
    {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L₀ wstep old charge row) :
    wstep.ChildOrder row := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent permitted =>
    rw [chosen]
    exact shrink_childOrder _ _ _ _ _ _ _ _ _ O _ numbered first _

theorem ShrinkWordVisit.halfRows {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {L₀ : A.Words Pins} {wstep : R.WordStep Pins L₀ b} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L₀ wstep old charge row)
    : State.HalfRows row.sites (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  cases v with
  | of_native fit hit stored oldArrays caps output O numbered first chosen halves saved extent permitted =>exact halves

theorem ShrinkWordVisit.published_data {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {L₀ : A.Words Pins} {wstep : R.WordStep Pins L₀ b} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L₀ wstep old charge row)
    : row.data.Reads (fun i=>(final i).val) ∧
      row.data.Footprint (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  cases v with
  | of_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ published => exact published

theorem ShrinkWordVisit.halfTail {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {b : Fin R.rules.count} {L₀ : A.Words Pins} {wstep : R.WordStep Pins L₀ b} {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (v : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L₀ wstep old charge row)
    : row.data.Tail (fun i=>(final i).val) ∧
      row.data.TailCells (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  exact v.erase.halfTail


end ThreeFlat.Diagonal.NavigationPass

end OAI
