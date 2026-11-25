import OAI.Hierarchy.TraceShrinkOwnerRead
import OAI.Hierarchy.TraceShrinkRoom
import OAI.ThreeFlat.Diagonal.PhysicalShrinkOutputData
import OAI.ThreeFlat.Diagonal.ShrinkArchiveStep
import OAI.ThreeFlat.Diagonal.ShrinkLayerRows

namespace OAI
/-! # Native owner, child, wire-width and charge rows retained by a shrinking stage -/

namespace Hierarchy.TraceShrinkRetained

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.ShrinkStage.DescriptorSpan Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators Fin.NatCast
noncomputable section
open private table_parts from OAI.Hierarchy.TraceShrinkRoom
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B).Base
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s:ℕ)
local notation "k" => (2*d+1:ℕ)
local notation "hc" => (show 2≤k from by have:=Nat.two_pow_pos s;omega)
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "x" => dims S N t rem
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A

/-- Recover the numbered archive and its `R.parent` pointers from the actual
writer output, including per-node motif-copy and incident-width records. -/
theorem archive {K W q : ℕ} (r : TraceRetainedRoom.Room q W) (wide : 8 ≤ W)
    (cur : Word W) (m out : Memory W) (c : Cursor) (branch : Fin (M).rules.count)
    (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : fixedWords T s D ≤ q) (arena : (Stage.shrink x).heapWords≤q)
    (wire : A.maxWidth+1≤q^4) (offset : 0<c.width) (ids : (allocate K c (.shrink x)).next.node≤2^W)
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
      ∃ O : ∀v,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v W,
        step=shrinkArchiveStep (K:=K) T s D rem hD small A c branch O old numbered first := by
  have room := scalar_room T s D rem hD small A r fixed arena wire
  obtain ⟨colors,slots,_,_,degree,_,_,_,_,_,_⟩ :=
    table_parts d (2^k) (2^t) (3*(2^k*d)/4) D (S).pieceRadix (keyBound S 1 t)
      T.more.length (widthMultiplicity k d) (shrinkBaseBound T) (shrinkMotifWidthFactor T k d) q fixed
  have bound : d≤q ∧ 2^k≤q ∧ D≤q := ⟨slots,colors,degree⟩
  have capBound : Incidents.capacity S ≤ q^4 := calc
    _ = 8*d^2*2^k := rfl
    _ ≤ q*q^2*q := Nat.mul_le_mul (Nat.mul_le_mul (by have := r.table; omega)
      (Nat.pow_le_pow_left bound.1 _)) bound.2.1
    _ = _ := by ring
  have childBound : d*2^k < 2^W := (Nat.mul_le_mul bound.1 bound.2.1).trans_lt r.square
  have degreeBound : 2*D < 2^W :=
    (Nat.mul_le_mul (by have := r.table; omega : 2≤q) bound.2.2).trans_lt r.square
  obtain ⟨O,reads,below,safe,halves,motifs⟩ :=
    ShrinkOutput.layer_records T s D rem hD small A cur m c branch H room.1
      ((Nat.le_mul_of_pos_right N (Nat.two_pow_pos t)).trans room.2.1.bases) wide
      childBound (capBound.trans_lt (r.power (by decide))) degreeBound offset ids
  let step:=shrinkArchiveStep (K:=K) T s D rem hD small A c branch O old numbered first
  refine ⟨step,shrinkArchive_numbered T s D rem hD small A c branch,rfl,rfl,reads,below,safe,?_⟩
  have entry (j : Fin old.layer.count) :
      (out (step.ownerPtr+j.val)).val=(step.sites.ord ((M).parent branch (old.ord.symm j))).val ∧
      c.heap≤ step.ownerPtr+j.val ∧ step.ownerPtr+j.val<(allocate K c (.shrink x)).next.heap := by
    let v:=old.ord.symm j
    have position : ChildRows.oldNumber P (B).order (shrinkOldPosition s rem A v)=j.val := by
      rw [shrinkOldPosition_number]
      exact (numbered v).symm.trans (congrArg Fin.val (old.ord.apply_symm_apply j))
    have y := owner T s D rem hD small A cur m out c branch H room.1 (shrinkOldPosition s rem A v)
    rw [position,←shrink_parent_number] at y
    exact ⟨y.1.trans ((shrinkArchive_numbered (K:=K) T s D rem hD small A c branch) _).symm,y.2⟩
  exact ⟨fun _ j=>(entry j).1,fun j=>(entry j).2,halves,motifs,O,rfl⟩


end
end Hierarchy.TraceShrinkRetained

end OAI
