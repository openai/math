import OAI.ThreeFlat.Diagonal.ShrinkLayerRows
import OAI.ThreeFlat.Diagonal.PhysicalStateHalfRows

namespace OAI
/-! # Scalar capacities and the published half-edge rows of a shrink step -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.ShrinkStage.DescriptorSpan Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators Fin.NatCast
noncomputable section
set_option quotPrecheck false
open private half_base_lower from OAI.ThreeFlat.Diagonal.ShrinkLayerRows
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B).Base
local notation "d" => (2^s:ℕ)
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "x" => dims S N t rem
local notation "supply" => shrinkIssuedWords T s D rem hD small A


/-- The finite scalar bounds used to reopen a selected physical shrink record. -/
structure ShrinkNativeCaps {F : Type} [Field F] (T : ShrinkMotif.Table F)
    (s D rem W : ℕ) (A : State (2^s) (shrinkCharge s+rem)) : Prop where
  old : ShrinkOldCaps s rem W
  ordinals : Fintype.card (shrinkRecordState s rem A).Base≤2^W ∧ Incidents.capacity (shrinkStage s D)<2^W
  output : ShrinkOutputCaps s D (Fintype.card (shrinkRecordState s rem A).Base) W
  demand : 1+2*(widthMultiplicity (2*2^s+1) (2^s)*A.maxWidth)+shrinkBaseBound T<2^W
  issued : shrinkMotifWidthFactor T (2*2^s+1) (2^s)*(1+A.maxWidth)<2^W
  halfCount : 2*D<2^W
  score : 80*(Fintype.card (shrinkRecordPacking s rem A).Motif)*
    (shrinkMotifWidthFactor T (2*2^s+1) (2^s)*(1+A.maxWidth))^2<2^W

private theorem halfBankAddress {floor₀ base limit count stride site offset : ℕ}
    (lo : floor₀ ≤ base) (hi : base + stride * count ≤ limit)
    (atSite : site < count) (inside : offset < stride) :
    floor₀ ≤ base + site * stride + offset ∧ base + site * stride + offset < limit := by
  constructor
  · exact (lo.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  · calc
      _ = base + (site * stride + offset) := Nat.add_assoc ..
      _ < base + count * stride := Nat.add_lt_add_left (DescriptorSpan.half_index_lt atSite inside) _
      _ = base + stride * count := by rw [Nat.mul_comm count stride]
      _ ≤ limit := hi

private theorem halfEntryAddress {floor₀ base limit ptr₀ site count degree slot column : ℕ}
    (lo : floor₀ ≤ base) (hi : base + (8 * degree) * count ≤ limit)
    (atSite : site < count) (atSlot : slot < 2 * degree) (atColumn : column < 4)
    (issued : ptr₀ = base + site * (8 * degree)) :
    floor₀ ≤ ptr₀ + 4 * slot + column ∧ ptr₀ + 4 * slot + column < limit := by
  have inside : 4 * slot + column < 8 * degree := calc
    _ = slot * 4 + column := by rw [Nat.mul_comm 4 slot]
    _ < (2 * degree) * 4 := DescriptorSpan.half_index_lt atSlot atColumn
    _ = 8 * degree := by ring
  rw [issued, Nat.add_assoc (base + site * (8 * degree)) (4 * slot) column]
  exact halfBankAddress lo hi atSite inside

set_option maxHeartbeats 1600000 in
/-- Read each half-edge header and its four-word descriptor from the admitted output. -/
theorem shrink_half_rows_of_bounds {W K : ℕ} (cur : Word W) (m out : Memory W)
    (c : Cursor) (branch : Fin (M).rules.count) (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (df : 2*D<2^W) (residual : 2^rem<2^W)
    (widthFit : ∀ e, ((M).next branch).width e<2^W)
    (prefixFit : ∀ z i, Halves.prefixValue ((M).next branch).graph ((M).next branch).width z i<2^W) :
    let O:=shrinkArchiveSites (K:=K) T s D rem hD small A c branch
    State.HalfRows O (fun i=>c.heap≤ i ∧ i<(allocate K c (.shrink x)).next.heap) (fun i=>(out i).val) := by
  let X:=(M).next branch
  let O:=shrinkArchiveSites (K:=K) T s D rem hD small A c branch
  let en:=allocate K c (.shrink x)
  let nativeLayer:=nodeLayer K c (.shrink x)
  let f:=DescriptorSpan.fields K c x (ShrinkMotif.chooseWidths (supply branch))
  have bound : en.next.heap<2^W := H.cursor.controls.trans_lt cur.isLt
  obtain ⟨_,hf,_,_,_,he,we,_⟩:=shrink_allocated_fields T s D rem hD small A (K:=K) c branch
  have halfEnd : f 40+(8*D)*(x).outputSites ≤ en.next.heap := we
  have lower := half_base_lower K c x (ShrinkMotif.chooseWidths (supply branch))
  have lo38 : c.heap≤f 38 := lower.1
  have lo40 : c.heap≤f 40 := lower.2
  have nSites : Fintype.card X.Base*2^rem=(x).outputSites := by
    simpa only [Fintype.card_prod,Fintype.card_fin,show Fintype.card (BitWord rem)=2^rem by simp [BitWord]]
      using Fintype.card_congr (shrinkNextOrder T s D rem hD small A branch)
  have ef (e : Halves.Live X.Base D rem) : Halves.edgeNumber X.order e<2^W := by
    have h:=half_index_lt (half_index_lt (X.order e.1.1).isLt e.1.2.isLt) (tagOrdinal rem e.2).isLt
    change Halves.edgeNumber X.order e<Fintype.card X.Base*D*2^rem at h
    have mass : Fintype.card X.Base*D*2^rem=D*(x).outputSites := by rw [←nSites];ring
    rw [mass] at h
    have le : D*(x).outputSites≤(8*D)*(x).outputSites := Nat.mul_le_mul_right _ (by omega)
    exact (h.trans_le (le.trans ((Nat.le_add_left _ _).trans halfEnd))).trans bound
  have graph:=shrink_stored_at T s D rem hD small A branch (shrinkPieceBound s D) H.tagPos _ _ H.descGraph
  let site:=fun z:X.Site=>X.chart.symm z
  let ordinal:=fun z:X.Site=>(O.ord z).val
  have route (z : X.Site) : Halves.siteNumber X.order (site z)=ordinal z :=
    (shrinkNextOrder_val T s D rem hD small A branch (site z)).symm
  have ptr (z : X.Site) : (out (O.layer.incident+ordinal z*2+1)).val=f 40+ordinal z*(8*D) := by
    have hp:=PublishedDescriptors.half_header_word («S» := S) H.records H.cursor H.descHeader (O.ord z) 1
    change out (f 38+(2*ordinal z+1))=((f 40+ordinal z*(8*D):ℕ):Word W) at hp
    have fit : f 40+ordinal z*(8*D)<2^W := by
      have atSite : ordinal z < (x).outputSites := (O.ord z).isLt
      have first := (halfBankAddress lo40 halfEnd atSite (show 0 < 8*D by omega)).2
      simpa only [Nat.add_zero] using first.trans bound
    have address : nativeLayer.incident+ordinal z*2+1 = f 38+(2*ordinal z+1) := by
      calc
        _ = f 38+ordinal z*2+1 := congrArg (fun a : ℕ => a+ordinal z*2+1) hf.symm
        _ = _ := by ring
    exact (congrArg (fun a : ℕ => (out a).val) address).trans ((congrArg Fin.val hp).trans (Fin.val_cast_of_lt fit))
  have addr (z : X.Site) (i : Fin (2*D)) (k : ℕ) :
      f 40+ordinal z*(8*D)+4*i.val+k=f 40+((ordinal z*(2*D)+i.val)*4+k) := by ring
  have word (z : X.Site) (i : Fin (2*D)) (k : Fin 4) :=
    PublishedDescriptors.half_word («S» := S) H.records H.cursor H.descHeader X.graph X.order X.width graph rfl rfl df residual
      (site z) i k ((route z).trans_lt (O.ord z).isLt)
  have emitted (z : X.Site) (i : Fin (2*D)) (column : Fin 4) :
      let edge := Halves.sourceHalf X.graph (site z) i
      out ((out (O.layer.incident+ordinal z*2+1)).val+4*i.val+column.val) =
        ((![Halves.edgeNumber X.order edge,if i.val < D then 0 else 1,X.width edge,
          Halves.prefixValue X.graph X.width (site z) i] : Fin 4 → ℕ) column : Word W) := by
    have native := word z i column
    have address : (out (O.layer.incident+ordinal z*2+1)).val+4*i.val+column.val =
        f 40+((Halves.siteNumber X.order (site z)*(2*D)+i.val)*4+column.val) := by
      rw [ptr z,route z]
      exact addr z i column.val
    exact (congrArg out address).trans native
  constructor
  · intro z
    have val := PublishedDescriptors.half_header_word («S» := shrinkStage s D) H.records
      H.cursor H.descHeader (O.ord z) 0
    change out (f 38+(2*ordinal z+0))=((2*D : ℕ) : Word W) at val
    have address : O.layer.incident+ordinal z*2 = f 38+(2*ordinal z+0) :=
      congrArg₂ Nat.add hf.symm ((Nat.mul_comm (ordinal z) 2).trans (Nat.add_zero _).symm)
    exact ((congrArg (fun n => (out n).val) address).trans (congrArg Fin.val val)).trans
      (Fin.val_cast_of_lt df)
  · intro z i
    exact (congrArg Fin.val (emitted z i 0)).trans (Fin.val_cast_of_lt (ef _))
  · intro z i
    exact (congrArg Fin.val (emitted z i 2)).trans (Fin.val_cast_of_lt (widthFit _))
  · intro z i
    exact (congrArg Fin.val (emitted z i 3)).trans (Fin.val_cast_of_lt (prefixFit _ _))
  · intro z hdrColumn
    have headers : O.layer.incident + 2 * (x).outputSites ≤ en.next.heap :=
      (congrArg (fun base => base + 2 * (x).outputSites) hf.symm).le.trans he
    exact halfBankAddress (lo38.trans_eq hf) headers (O.ord z).isLt hdrColumn.isLt
  · intro z i column
    exact halfEntryAddress lo40 we (O.ord z).isLt i.isLt column.isLt (ptr z)


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
