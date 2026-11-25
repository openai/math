import OAI.ThreeFlat.Diagonal.PhysicalShrinkOutputData

namespace OAI
/-! # Reading the histogram address, copy count and tile from shrink incident records -/
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

open scoped Fin.CommRing in
private theorem incident_histogram_field {baseTy groupTy : Type} [AddCommGroup groupTy]
    [Fintype baseTy] [Fintype groupTy] {stage : Graph.Stage} {hosts tags lanes w width : ℕ}
    (pack : PackingData baseTy groupTy (BitWord tags) (BitWord lanes) stage.degree stage.colors)
    (order : baseTy ≃ Fin hosts) (colors : 2 ≤ stage.colors) (layout : Bool)
    (cursor : Cursor) (pointer : Word w) (raw saved : Memory w)
    (space : CursorSpace pointer raw cursor width (dims stage hosts tags lanes))
    (head : RAM.HeaderScan.Scans.Header pointer saved cursor.header 63
      (DescriptorSpan.fields width cursor (dims stage hosts tags lanes) layout))
    (site : Computability.VPVNP.Compression.Site baseTy (BitWord tags) (BitWord lanes)) (a : pack.Motif) :
    (Incidents.descriptor («S» := stage) pack order Template.ptr (fun _=>pointer) saved
      (fun _=>0) colors width layout site a 1).val=
      cursor.dense+(denseMotifRow pack order (tagOrdinal tags) (tagOrdinal lanes) colors a).val*width := by
  let idx := (denseMotifRow pack order (tagOrdinal tags) (tagOrdinal lanes) colors a).val
  have inRows : idx<(dims stage hosts tags lanes).motifs :=
    (denseMotifRow pack order (tagOrdinal tags) (tagOrdinal lanes) colors a).isLt
  have atField : RAM.PhysicalPinsExpr.Formula.value (fun _=>pointer) saved (fun _ : Fin 1=>0)
      (Template.f countTable)=(cursor.dense:Word w) :=
    DescriptorSpan.field_word head (fun _=>0) countTable (by decide)
  have fits : cursor.dense+idx*width<2^w := by
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := space.allocated
    have first := space.counts
    have stop := space.end_lt
    have scaled := Nat.mul_le_mul_left width inRows.le
    rw [Nat.mul_comm idx width]
    omega
  change ((RAM.PhysicalPinsExpr.Formula.value (fun _=>pointer) saved (fun _ : Fin 1=>0)
    (Template.f countTable))+(idx:Word w)*(width:Word w)).val=cursor.dense+idx*width
  rw [atField,←Nat.cast_mul,←Nat.cast_add,Fin.val_cast_of_lt fits]

/-- The second incident word locates its actual histogram in the original dense bank. -/
theorem ShrinkOutput.incident_record_histogram (branch : Fin (M).rules.count) {out : Memory W}
    (z : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (site : Computability.VPVNP.Compression.Site (B).Base (BitWord tagCount) (BitWord rem)) (a : (P).Motif) :
    (Incidents.descriptor («S» := shrinkStage s D) P (B).order Template.ptr (fun _=>cur)
      (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 (fun _=>0) hc K
      (ShrinkMotif.chooseWidths (supply branch)) site a 1).val=
      c.dense+(shrinkRecordOrder s rem A a).val*K := by
  exact incident_histogram_field (stage := shrinkStage s D) (tags := tagBits (2^s)) (lanes := rem)
    (width := K) P (B).order hc (ShrinkMotif.chooseWidths (supply branch)) c cur m
    (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 z.cursor z.descHeader site a

open scoped Fin.CommRing in
private theorem incidentChoiceReads {Host Label : Type} [AddCommGroup Label]
    [Fintype Host] [Fintype Label] {hosts tags lanes width alphabet : ℕ}
    (stage : Graph.Stage)
    (pack : PackingData Host Label (BitWord tags) (BitWord lanes) stage.degree stage.colors)
    (order : Host ≃ Fin hosts) (paletteFit : 2 ≤ stage.colors) (layout : Bool)
    (place : Computability.VPVNP.Compression.Site Host (BitWord tags) (BitWord lanes)) (motif : pack.Motif)
    (address : Cursor) (cell : Word width) (raw old : Memory width)
    (space : CursorSpace cell raw address alphabet (dims stage hosts tags lanes))
    (read : RAM.HeaderScan.Scans.Header cell old address.header 63
      (DescriptorSpan.fields alphabet address (dims stage hosts tags lanes) layout)) :
    let row := (denseMotifRow pack order (tagOrdinal tags) (tagOrdinal lanes) paletteFit motif).val
    let desc := Incidents.descriptor («S» := stage) pack order Template.ptr
      (fun _ => cell) old (fun _ => 0) paletteFit alphabet layout place motif
    (desc 3).val = (old (address.heap+3*row)).val ∧
    (desc 2).val = (old (address.heap+3*row+1)).val := by
  let row := (denseMotifRow pack order (tagOrdinal tags) (tagOrdinal lanes) paletteFit motif).val
  have inside : row < (dims stage hosts tags lanes).motifs :=
    (denseMotifRow pack order (tagOrdinal tags) (tagOrdinal lanes) paletteFit motif).isLt
  have top : address.heap+3*row+1 < 2^width := by
    obtain ⟨a,b,d,e,f,g,i,j,k,l⟩ := space.allocated
    have cutoff := space.end_lt
    omega
  let base := RAM.PhysicalPinsExpr.Formula.value (fun _ => cell) old
    (fun _ : Fin 1 => 0) (Template.f choiceTable)
  have header : base = (address.heap : Word width) :=
    DescriptorSpan.field_word read (fun _ => 0) choiceTable (by decide)
  have addr₀ : (base+(row : Word width)*3).val = address.heap+3*row := by
    rw [header]
    have sum : (address.heap : Word width)+(row : Word width)*3 =
        ((address.heap+3*row : ℕ) : Word width) := by
      simp only [Nat.mul_comm 3 row,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [sum,Fin.val_cast_of_lt (by omega)]
  have addr₁ : (base+(row : Word width)*3+1).val = address.heap+3*row+1 := by
    rw [header]
    have sum : (address.heap : Word width)+(row : Word width)*3+1 =
        ((address.heap+3*row+1 : ℕ) : Word width) := by
      simp only [Nat.mul_comm 3 row,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    rw [sum,Fin.val_cast_of_lt top]
  change (old (base+(row : Word width)*3).val).val = (old (address.heap+3*row)).val ∧
    (old (base+(row : Word width)*3+1).val).val = (old (address.heap+3*row+1)).val
  exact ⟨congrArg (fun address => (old address).val) addr₀,
    congrArg (fun address => (old address).val) addr₁⟩

/-- The fourth word of an occupied motif is its actual chosen copy count. -/
theorem ShrinkOutput.incident_record_copies (branch : Fin (M).rules.count) {out : Memory W}
    (z : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (site : Computability.VPVNP.Compression.Site (B).Base (BitWord tagCount) (BitWord rem)) (a : (P).Motif) :
    (Incidents.descriptor («S» := shrinkStage s D) P (B).order Template.ptr (fun _=>cur)
      (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 (fun _=>0) hc K
      (ShrinkMotif.chooseWidths (supply branch)) site a 3).val=shrinkRecordCopies T s rem A a := by
  exact ((incidentChoiceReads (alphabet:=K) (shrinkStage s D) P (B).order hc
    (ShrinkMotif.chooseWidths (supply branch)) site a c cur m _ z.cursor z.descHeader).1).trans
    (z.choiceCopies a)

/-- Column two in the actual local incident row selects the ROM tile used by the physical move. -/
theorem ShrinkOutput.incident_record_tile (branch : Fin (M).rules.count) {out : Memory W}
    (z : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (site : Computability.VPVNP.Compression.Site (B).Base (BitWord tagCount) (BitWord rem)) (a : (P).Motif) :
    (Incidents.descriptor («S» := shrinkStage s D) P (B).order Template.ptr (fun _=>cur)
      (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 (fun _=>0) hc K
      (ShrinkMotif.chooseWidths (supply branch)) site a 2).val=
      (RefreshDemandRows.tileNumber (PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc a) (T.base ∘ T.row)).val := by
  exact ((incidentChoiceReads (alphabet:=K) (shrinkStage s D) P (B).order hc
    (ShrinkMotif.chooseWidths (supply branch)) site a c cur m _ z.cursor z.descHeader).2).trans
    (z.choiceShape a)


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
