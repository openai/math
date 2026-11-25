import OAI.ThreeFlat.Diagonal.RefreshPartyFits
import OAI.ThreeFlat.Diagonal.SlotImageViews

namespace OAI
/-! # Bounds of refresh-party lookup from its real predecessor and header -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows
open CompressorPacking.Native RefreshDemandRows RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {W v a t : ℕ} (m : Memory W) (r : Fin 7 → Word W)
private abbrev valueAt {W : ℕ} (mem : Memory W) (registers : Fin 7 → Word W) : Formula 7 → ℕ :=
  Formula.natural W (fun _=>0) (fun i=>(mem i).val) (fun i=>(registers i).val)

private abbrev fitsAt {W : ℕ} (mem : Memory W) (registers : Fin 7 → Word W) : Formula 7 → Prop :=
  Formula.Fits W (fun _=>0) (fun i=>(mem i).val) (fun i=>(registers i).val)

/-- These reads use the stage pointer archived in the node, even after the
outer compressor has advanced to a later stage in its directory. -/
structure Source (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)) (C : SlotImage.Columns)
    (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ) : Prop where
  image : SlotImage.Stored G (Equiv.refl _) (SlotImage.pairLane (tagOrdinal a) (tagOrdinal t)) C (fun i=>(m i).val) w
  shifts : SlotImage.SplitColumns C split (fun i=>(m i).val) v a
  header : (r 0).val+40<2^W
  remain : (valueAt m r) (stageField 8)=2^t
  widths : (valueAt m r) (stageField 9)=C.widths
  graph : (valueAt m r) (stageField 10)=C.graph
  rows : (valueAt m r) (stageField 11)=C.rows
  divided : (valueAt m r) (stageField 12)=split
  graphBound : C.graph+6*C.rows≤2^W
  widthBound : C.widths+v*mPort a*(mPort a*2^t)≤2^W
  shiftBound : split+3*C.rows≤2^W

variable {m r} {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)} {C : SlotImage.Columns}
    {split : ℕ} {w : SlotImage.RefreshInput v a t → ℕ}
    (S : Source m r G C split w)

include S in
/-- Move the predecessor image to the current party memory. Only the stored
stage header, old graph and widths, and the split table carry live input. -/
theorem Source.reopen {m' : Memory W} {r' : Fin 7→Word W}
    (head : (r' 0).val=(r 0).val)
    (header : ∀ i,8≤ i→i≤12→m' ((r 0).val+i)=m ((r 0).val+i))
    (graph : ∀ i,C.graph≤ i→i<C.graph+6*C.rows→m' i=m i)
    (widths : ∀ i,C.widths≤ i→i<C.widths+v*mPort a*(mPort a*2^t)→m' i=m i)
    (shifts : ∀ i,split≤ i→i<split+3*C.rows→m' i=m i) :
    Source m' r' G C split w := by
  have stage (j : ℕ) (l : 8≤j) (u : j≤12) :
      (stageField j).natural W (fun _=>0) (fun i=>(m' i).val) (fun i=>(r' i).val)=
      (stageField j).natural W (fun _=>0) (fun i=>(m i).val) (fun i=>(r i).val) := by
    change (m' ((r' 0).val+j)).val=(m ((r 0).val+j)).val
    rw [head,header j l u]
  have edge (p : Fin v×Fin (mPort a)) (back : Bool) :=
    graph _ (SlotImage.cell_range S.image p back 2).1 (SlotImage.cell_range S.image p back 2).2
  have pos (p : Fin v×Fin (mPort a)) : SlotImage.ordinal (Equiv.refl _) p<C.rows:=by
    rw [S.image.rowCount];exact SlotImage.ordinal_lt _ p
  refine ⟨S.image.frame (fun i l u=>congrArg Fin.val (graph i l u))
    (fun i l u=>congrArg Fin.val (widths i l u)),?_,by rw [head];exact S.header,
    (stage 8 (by decide) (by decide)).trans S.remain,(stage 9 (by decide) (by decide)).trans S.widths,
    (stage 10 (by decide) (by decide)).trans S.graph,(stage 11 (by decide) (by decide)).trans S.rows,
    (stage 12 (by decide) (by decide)).trans S.divided,S.graphBound,S.widthBound,S.shiftBound⟩
  constructor
  · intro p
    have h:=pos p
    rw [shifts _ (by omega) (by omega),edge p false]
    exact S.shifts.forward p
  · intro p
    have h:=pos p
    rw [shifts _ (by omega) (by omega),edge p true]
    exact S.shifts.reverse p
  · intro p
    have h:=pos p
    rw [shifts _ (by omega) (by omega),edge p true]
    exact S.shifts.consumed p

include S in
theorem Source.field (j : ℕ) (hj : j≤40) : (fitsAt m r) (stageField j) := by
  have cap := S.header
  exact ⟨⟨trivial,trivial,trivial⟩,(by change (r 0).val+j<_; omega)⟩

include S in
theorem Source.demands : Stored G (inputs.map (valueAt m r)) (fun i=>(m i).val) (SlotImage.demandWidth w) := by
  have eq : inputs.map (valueAt m r)=SlotImage.demandColumns C split := by
    change Columns.mk ((valueAt m r) (stageField 9)) ((valueAt m r) (stageField 10)+(valueAt m r) (stageField 11)*3)
      ((valueAt m r) (stageField 10)+(valueAt m r) (stageField 11)*4) ((valueAt m r) (stageField 12)+(valueAt m r) (stageField 11)*2)
      ((valueAt m r) (stageField 12)+(valueAt m r) (stageField 11)*1)=_
    rw [S.widths,S.graph,S.rows,S.divided,Nat.mul_one]
    rfl
  rw [eq]
  exact SlotImage.demandStored S.image S.shifts

include S in
theorem Source.column_fits :
    (fitsAt m r) inputs.widths ∧ (fitsAt m r) inputs.sourceBase ∧ (fitsAt m r) inputs.sourceSlot ∧ (fitsAt m r) inputs.portShift ∧ (fitsAt m r) inputs.laneShift := by
  have pair (src j : ℕ) (h : src≤40) : (fitsAt m r) (plus (stageField src) (.op .mul (stageField 11) (.lit j))) :=
    ⟨S.field src h,⟨S.field 11 (by decide),trivial,trivial⟩,trivial⟩
  exact ⟨S.field 9 (by decide),pair 10 3 (by decide),pair 10 4 (by decide),pair 12 2 (by decide),pair 12 1 (by decide)⟩

include S in
theorem Source.column_bounds (f : F) (sel : f∈[inputs.sourceBase,inputs.sourceSlot,inputs.portShift,inputs.laneShift]) :
    (valueAt m r) f+v*mPort a≤2^W := by
  have row := S.image.rowCount
  have graph := S.graphBound
  have shifts := S.shiftBound
  simp only [List.mem_cons,List.not_mem_nil,or_false] at sel
  rcases sel with rfl|rfl|rfl|rfl
  · change (valueAt m r) (stageField 10)+(valueAt m r) (stageField 11)*3+_≤_
    rw [S.graph,S.rows,←row]; omega
  · change (valueAt m r) (stageField 10)+(valueAt m r) (stageField 11)*4+_≤_
    rw [S.graph,S.rows,←row]; omega
  · change (valueAt m r) (stageField 12)+(valueAt m r) (stageField 11)*2+_≤_
    rw [S.divided,S.rows,←row]; omega
  · change (valueAt m r) (stageField 12)+(valueAt m r) (stageField 11)*1+_≤_
    rw [S.divided,S.rows,←row]; omega

include S in
theorem Source.address_and_prefix (z : Block v t) (block : (m (r 2).val).val=blockId z)
    (back : Bool) (port slot : F) (i j : Fin (mPort a)) (fp : (fitsAt m r) port) (fs : (fitsAt m r) slot)
    (xp : (valueAt m r) port=i.val) (xs : (valueAt m r) slot=j.val) (mf : mPort a<2^W) (lf : 2^t<2^W) :
    let row := coordinates (mPort a) inputs (stageField 8) (.load (.reg 2)) back port slot
    (fitsAt m r) row ∧ (valueAt m r) row<2^W ∧ (fitsAt m r) (bundleBefore (mPort a) inputs.widths row) := by
  let row := coordinates (mPort a) inputs (stageField 8) (.load (.reg 2)) back port slot
  have widthEnd : (valueAt m r) inputs.widths+v*mPort a*(mPort a*2^t)≤2^W := by
    change (valueAt m r) (stageField 9)+_≤_
    rw [S.widths]
    exact S.widthBound
  have fit := coordinates_fit (fun _=>0) (fun i=>(m i).val) (fun i=>(r i).val) G inputs (stageField 8) (.load (.reg 2)) z back port slot i j _ S.demands xp xs fp fs
    S.remain block ⟨trivial,(r 2).isLt⟩ (S.field 8 (by decide)) (m _).isLt mf.le lf
    S.column_fits widthEnd S.column_bounds
  refine ⟨fit.1,fit.2,?_⟩
  let e := addr (arrival G (tagOrdinal a).symm) z (back,i,j)
  let offset := (e.1.1.val*mPort a+e.2.2.val)*2^t+(tagOrdinal t e.1.2).val
  have ev : (valueAt m r) row=(valueAt m r) inputs.widths+index e := by
    have read := coordinates_read (W:=W) (fun _=>0) (fun n=>(m n).val) (fun n=>(r n).val)
      (mPort a) inputs (stageField 8) (.load (.reg 2)) back port slot
    apply read.trans
    change absAddress (mPort a) (inputs.map (valueAt m r)) (fun n=>(m n).val)
      (valueAt m r (stageField 8)) (m (r 2).val).val back (valueAt m r port) (valueAt m r slot)=_
    rw [S.remain,block,xp,xs]
    exact demand_address G S.demands z back i j
  have form : index e=offset*mPort a+e.2.1.val := by dsimp [index,ordinal,offset]; ring
  have base : e.1.1.val*mPort a+e.2.2.val<v*mPort a := by
    have b := Nat.mul_le_mul_right (mPort a) e.1.1.isLt
    rw [Nat.succ_mul] at b
    omega
  have bound : offset<v*mPort a*2^t := by
    have b := Nat.mul_le_mul_right (2^t) base
    rw [Nat.succ_mul] at b
    dsimp [offset]; have := (tagOrdinal t e.1.2).isLt; omega
  have span := Nat.mul_le_mul_right (mPort a) bound
  rw [Nat.succ_mul] at span
  have eq : v*mPort a*2^t*mPort a=v*mPort a*(mPort a*2^t) := by ac_rfl
  apply before_fit (fun _=>0) (fun i=>(m i).val) (fun i=>(r i).val) (mPort a) inputs.widths row offset e.2.1 S.column_fits.1 fit.1
    (m _).isLt fit.2 mf
  · change valueAt m r row = valueAt m r inputs.widths + offset*mPort a + e.2.1.val
    rw [ev,form,Nat.add_assoc]
  · change valueAt m r inputs.widths + offset*mPort a + mPort a ≤ 2^W
    omega

end
end ThreeFlat.Diagonal.RefreshParty

end OAI
