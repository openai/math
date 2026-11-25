import OAI.ThreeFlat.Diagonal.CompressorSupplyKeyRead
import OAI.ThreeFlat.Diagonal.CompressorSupplyCopyRead
import OAI.ThreeFlat.Diagonal.CompressorSuccessorFiles

namespace OAI
/-! # Reading the physical outgoing or mate port for one particular retained supply copy -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped Fin.NatCast Classical

variable {w n : ℕ} (data : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data mem vs

theorem port_word {d : ℕ} (origin first key : F n) (ports : List (Fin d)) (i : Fin d) (hit : i∈ports)
    (test : ∀j : Fin d,V (.load (.op .add origin (.op .add first (.lit j.val))))=V key ↔ j=i) :
    V (portLookup origin first key ports)=(i.val:Word w) := by
  induction ports with
  | nil => simp at hit
  | cons a tail ih =>
    by_cases eqv : a=i
    · subst a
      have h: V (.load (.op .add origin (.op .add first (.lit i.val))))=V key := (test i).2 rfl
      change (if RAM.DescriptorExpr.Comparison.eq.test _ _ then (i.val:Word w) else _)=_
      simp only [RAM.DescriptorExpr.Comparison.test,beq_iff_eq,h,ite_true]
    · have neq := (test a).not.mpr eqv
      change (if RAM.DescriptorExpr.Comparison.eq.test (V (.load (.op .add origin (.op .add first (.lit a.val))))) (V key)
        then (a.val:Word w) else V (portLookup origin first key tail))=_
      rw [RAM.DescriptorExpr.Comparison.test,ite_eq_right (by simpa only [beq_iff_eq] using neq)]
      exact ih ((List.mem_cons.mp hit).resolve_left (Ne.symm eqv))

private theorem row_address (start vertex degree lane : ℕ) (room : start+(vertex*degree+lane)<2^w) :
    ((start:Word w)+((vertex:Word w)*(degree:Word w)+(lane:Word w))).val =
      start+(vertex*degree+lane) := by
  have product : (vertex:Word w)*(degree:Word w)=((vertex*degree:ℕ):Word w) :=
    Fin.ext (Nat.mul_mod vertex degree (2^w)).symm
  rw [product, ←Nat.cast_add (vertex*degree) lane, ←Nat.cast_add start, Fin.val_cast_of_lt room]

variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {N t l pad : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (bound : ∀k,S.pieces k≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
local notation "tagged" => Template.tagNumber (t:=t) b
local notation "D" => Graph.liveDegree S+pad
local notation "ord" => ordinalOf S P (baseNat b) bound lay false hc
local notation "eid" => edgeId S P (baseNat b) bound

theorem crossing_slot_words (ptr : F n) (e : Ends (F n)) (kind : Fin 4) (copy : Fin (S.pieces kind))
    (z : ShrinkEdge P S.pieces) (G : LiftedSlots (B × BitWord t) D (BitWord l))
    (C : SlotImage.Columns) (width : SlotImage.Edge (B × BitWord t) (BitWord l) D→ℕ)
    (stored : SlotImage.Stored G tagged (tagOrdinal l) C (fun a=>(mem a).val) width)
    (kb : ℕ) (keyRead : ∀ u : (B × BitWord t) × Fin D,mem (kb+SlotImage.ordinal tagged u)=(Template.sourceKey S P b bound lay hc u:Word w))
    (idFit : ∀ z,eid z<2^w) (keyRoom : kb+C.rows≤2^w) (graphRoom : C.graph+6*C.rows≤2^w)
    (live : S.liveDegree=Graph.liveDegree S) (full : S.outputDegree=D)
    (keysAt : V (atField (Demand.formulaOps n) ptr keys)=(kb:Word w))
    (graphAt : V (atField (Demand.formulaOps n) ptr nextGraph)=(C.graph:Word w))
    (rowsAt : V (atField (Demand.formulaOps n) ptr nextSlots)=(C.rows:Word w))
    (baseWord : V (crossingBase ptr S lay e kind)=((tagged (ord z).1).val:Word w))
    (keyWord : V (crossingKey ptr S lay e kind copy)=(eid z:Word w)) :
    let slot:=CompressorRefresh.leftRow (b:=pad) (ord z)
    V (crossingPort ptr S lay e kind copy)=(slot.2.val:Word w) ∧
    V (crossingMate ptr S lay e kind copy)=((SlotImage.oriented G false slot).2.val:Word w) := by
  let u:=ord z
  let slot:=CompressorRefresh.leftRow (b:=pad) u
  let headed : Fin (Graph.liveDegree S)→(B × BitWord t) × Fin D := fun j=>CompressorRefresh.leftRow (b:=pad) (u.1,j)
  let first:=Formula.op .mul (crossingBase ptr S lay e kind) (.lit S.outputDegree)
  let origin:=atField (Demand.formulaOps n) ptr keys
  have row (j : Fin (Graph.liveDegree S)) : SlotImage.ordinal tagged (headed j)=(tagged u.1).val*D+j.val := rfl
  have loc (j : Fin (Graph.liveDegree S)) : kb+((tagged u.1).val*D+j.val)<2^w := by
    have lim:=SlotImage.ordinal_lt tagged (headed j)
    rw [row,←stored.rowCount] at lim
    omega
  have fetch (j : Fin (Graph.liveDegree S)) : V (.load (.op .add origin (.op .add first (.lit j.val))))=
      (eid ((ord).symm (u.1,j)):Word w) := by
    change mem ((V origin+(V (crossingBase ptr S lay e kind)*(S.outputDegree:Word w)+(j.val:Word w))).val)=_
    have address : ((kb : Word w) + (((tagged u.1).val : Word w) * ((D : ℕ) : Word w) + (j.val : Word w))).val =
        kb+((tagged u.1).val*D+j.val) := by
      exact row_address kb (tagged u.1).val D j.val (loc j)
    rw [show V origin=(kb:Word w) from keysAt,baseWord,full,address,←row j,keyRead,Template.sourceKey_left]
  have reader (j : Fin (Graph.liveDegree S)) :
      V (.load (.op .add origin (.op .add first (.lit j.val))))=V (crossingKey ptr S lay e kind copy) ↔ j=u.2 := by
    rw [fetch,keyWord]
    constructor
    · intro h
      have val:=congrArg Fin.val h
      rw [Fin.val_cast_of_lt (idFit _),Fin.val_cast_of_lt (idFit _)] at val
      have same : (ord).symm (u.1,j)=z :=
        (idEmbedding S P (baseNat b) bound idFit).injective (Fin.ext val)
      have pair:=congrArg ord same
      rw [Equiv.apply_symm_apply] at pair
      exact congrArg Prod.snd pair
    · rintro rfl
      change (eid ((ord).symm ((ord z).1,(ord z).2)):Word w)=(eid z:Word w)
      rw [Prod.mk.eta,Equiv.symm_apply_apply]
  have readPort : V (crossingPort ptr S lay e kind copy)=(u.2.val:Word w) := by
    unfold crossingPort
    rw [live]
    exact port_word data mem vs origin first _ _ u.2 (List.mem_finRange _) reader
  refine ⟨readPort,?_⟩
  have matAddr : SlotImage.cell C tagged slot false 1=C.graph+C.rows+((tagged u.1).val*D+u.2.val) := by
    change C.graph+C.rows*(0+1)+((tagged u.1).val*D+u.2.val)=_
    simp
  have room := (SlotImage.cell_range stored slot false 1).2.trans_le graphRoom
  rw [matAddr] at room
  change mem ((V (atField (Demand.formulaOps n) ptr nextGraph)+
    V (atField (Demand.formulaOps n) ptr nextSlots)*1+
    (V (crossingBase ptr S lay e kind)*(S.outputDegree:Word w)+V (crossingPort ptr S lay e kind copy))).val)=_
  have address : ((C.graph:Word w)+(C.rows:Word w)+
      (((tagged u.1).val:Word w)*((D:ℕ):Word w)+(u.2.val:Word w))).val =
      C.graph+C.rows+((tagged u.1).val*D+u.2.val) := by
    rw [←Nat.cast_add C.graph C.rows]
    exact row_address (C.graph+C.rows) (tagged u.1).val D u.2.val room
  rw [graphAt, rowsAt, mul_one, baseWord, full, readPort, address, ←matAddr]
  have mate:=stored.mate slot false
  rw [←mate,Fin.cast_val_eq_self]

theorem crossing_party_word (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party bit : F n) (kind : Fin 4) (copy : Fin (S.pieces kind)) (u : Fin 6) (h8 : 8≤2^w)
    (outgoing incoming : ℕ) (port : V (crossingPort ptr S lay e kind copy)=(outgoing:Word w))
    (mate : V (crossingMate ptr S lay e kind copy)=(incoming:Word w)) (atParty : V party=(u.val:Word w))
    (col : Fin 4) : V (crossing ptr S lay e party kind copy bit col)=
      (![2,0,((if u=ShrinkMotif.supplySrc (ShrinkMotif.survivor lay kind) then outgoing else S.outputDegree+incoming : ℕ):Word w),V bit]
      : Fin 4→Word w) col := by
  fin_cases col
  · rfl
  · rfl
  · change (if RAM.DescriptorExpr.Comparison.eq.test (V party) ((ShrinkMotif.supplySrc (ShrinkMotif.survivor lay kind)).val:Word w)
      then V (crossingPort ptr S lay e kind copy) else (S.outputDegree:Word w)+V (crossingMate ptr S lay e kind copy))=_
    rw [atParty,port,mate]
    by_cases hit : u=ShrinkMotif.supplySrc (ShrinkMotif.survivor lay kind) <;>
      simp [RAM.DescriptorExpr.Comparison.test,supply_digit_eq (w:=w) (k:=6) (by omega),hit]
  · rfl


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
