import OAI.Hierarchy.DescentBatchedRotor
import OAI.Hierarchy.DescentWordProduct

namespace OAI
/-! # Issuing a rotor pointer in whole payload units from layer, row and batch counters -/

namespace Hierarchy.DescentResetLaneIssue
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section

/-- Every variable summand in the physical mixed-radix offset starts on a p-digit boundary. -/
def start (m p prior span bit layers layer batch : ℕ) :=
  bit+p*((m*prior)*layers+(m*span)*layer+span*batch)

def block (m p prior span bit layers layer batch : ℕ) :=
  bit/p+(m*prior)*layers+(m*span)*layer+span*batch

theorem start_div {p : ℕ} (hp : 0<p) (m prior span bit layers layer batch : ℕ) :
    start m p prior span bit layers layer batch/p=block m p prior span bit layers layer batch := by
  simp [start,block,Nat.add_mul_div_left,add_assoc,hp]

theorem start_mod (m p prior span bit layers layer batch : ℕ) :
    start m p prior span bit layers layer batch%p=bit%p := by simp [start,Nat.add_mod]

def factor (w c : ℕ) (reg : Fin 3) : Term w 0 3 :=
  (ProtocolRAMPortScale.scale w (ProtocolRAMPortScale.bitWidth c) c).rename (fun _=>reg)

/-- Three changing counters are scaled only by coefficients fixed for this menu slot and epoch. -/
def blockTerm (w m p prior span bit : ℕ) : Term w 0 3 :=
  .binary .add (.binary .add (.binary .add (.literal (bit/p : ℕ)) (factor w (m*prior) 0))
    (factor w (m*span) 1)) (factor w span 2)

theorem factor_eval {w : ℕ} (c : ℕ) (reg : Fin 3) (mem : Memory w) (vs : Fin 3 → Computability.VPVNP.BurstRAM.Word w) :
    (factor w c reg).eval Fin.elim0 mem vs=vs reg*(c : Computability.VPVNP.BurstRAM.Word w) := by
  rw [factor,Term.eval_rename,ProtocolRAMPortScale.eval_scale _ _ _ _ (ProtocolRAMPortScale.fits _)]
  rfl

theorem blockTerm_read {w : ℕ} (m p prior span bit : ℕ) (mem : Memory w) (vs : Fin 3 → Computability.VPVNP.BurstRAM.Word w) :
    (blockTerm w m p prior span bit).eval Fin.elim0 mem vs=
      ((block m p prior span bit (vs 0).val (vs 1).val (vs 2).val : ℕ) : Computability.VPVNP.BurstRAM.Word w) := by
  simp only [blockTerm,Term.eval_binary,Term.eval_literal,factor_eval,BinaryOp.eval,block,Nat.cast_add,Nat.cast_mul]
  simp only [Fin.cast_val_eq_self]
  ring

theorem blockTerm_cheap (w m p prior span bit : ℕ) :
    admissible (blockTerm w m p prior span bit) := by
  simp [blockTerm,factor,Term.binary,Term.literal,admissible_let,admissible,opAllowed,allowed,
    DescentWordProduct.scale_ok]

theorem blockTerm_binds (w m p prior span bit : ℕ) :
    (blockTerm w m p prior span bit).binds≤16+2*(ProtocolRAMPortScale.bitWidth (m*prior)+
      ProtocolRAMPortScale.bitWidth (m*span)+ProtocolRAMPortScale.bitWidth span) := by
  have a:=ProtocolRAMPortScale.binds w (ProtocolRAMPortScale.bitWidth (m*prior)) (m*prior)
  have b:=ProtocolRAMPortScale.binds w (ProtocolRAMPortScale.bitWidth (m*span)) (m*span)
  have c:=ProtocolRAMPortScale.binds w (ProtocolRAMPortScale.bitWidth span) span
  simp only [blockTerm,factor,Term.binary,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  omega

def portPrefix {q : ℕ} (span : Fin q→ℕ) (j : Fin q) := ∑i : Fin j,span (Fin.castLE j.isLt.le i)

theorem spine_start {q layers m p : ℕ} (hp : 0<p) (span len : Fin q→ℕ)
    (fit : ∀i,len i=layers*((m*p)*span i)) (t : SpineRow (r:=layers) (m:=m) span) :
    (spineBit span len fit (t,⟨0,hp⟩)).val=
      start m p (portPrefix span t.1) (span t.1) t.2.2.2.val layers t.2.1.val t.2.2.1.val := by
  change (finSigmaFinEquiv ⟨t.1,Fin.cast (fit t.1).symm (blockBit layers m p (span t.1) (t.2,⟨0,hp⟩))⟩).val=_
  rw [finSigmaFinEquiv_apply]
  simp only [Fin.val_cast,blockBit_val,zero_add]
  have sumEq : (∑i : Fin t.1,len (Fin.castLE t.1.isLt.le i))=layers*((m*p)*portPrefix span t.1) := by
    simp [portPrefix,fit,Finset.mul_sum]
  rw [sumEq]
  unfold start
  ring

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => m*p
local notation "src" => fun e : Item contact owner s w => first (root contact input site owner s w align e)
local notation "dst" => fun e : Item contact owner s w => last (link contact owner s w e)
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers C₀ b u
local notation "A" => DescentGoodRouter.device D u contact input site owner align s w G first last P
local notation "sz" => tapBits D u G P
local notation "prg" => program D m p hp contact input site owner align s w G first last P key
local notation "tapAt" => tapLane D m p hp contact input site owner align s w G first last P
local notation "RT" => rootLane D m p hp contact input site owner align s w G first last P
open private leftEdge rightEdge from OAI.Hierarchy.DescentBatchedRotor
open private cablePort from OAI.Hierarchy.DescentPhysicalSplit
open private Physical.endpoint from OAI.Hierarchy.DescentRotorNetwork

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem tap_fields (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (back : Bool) (t : SpineRow (r:=P.layers) (m:=m) (sz v)) :
    let l:=tapLane (K:=K) D m p hp contact input site owner align s w G first last P v i back t
    (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (.inl (.inr ⟨v,if back then i.castSucc else i.succ⟩),
        start m p (portPrefix (sz v) t.1) (sz v t.1) t.2.2.2.val P.layers t.2.1.val t.2.2.1.val,sz v t.1) := by
  have atZero := spine_start hp (tapBits D (m*p) G P v) (localWidth H v)
    (tapWidth_eq D (m*p) G P v) t
  cases back <;> exact Prod.ext rfl (Prod.ext atZero rfl)

/-- The slot index is the immutable local incidence enumeration already used by the
physical trivalent rotor. The width and all three running counters are absent from its data. -/
def rootHostSlot (v : Fin (2^n)) : Slot G.arcs v →
    Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n))
      (Physical.host G.arcs D P.layers C₀ b (m*p)) v)
  | .inl side=>DescentPhysicalSplit.index H v ⟨.inl (v,side),rfl⟩
  | .inr q=>DescentPhysicalSplit.index H v (cablePort H v (Physical.endpoint G.arcs v q))

private theorem root_offset (off prior span bit layers layer batch m p : ℕ)
    (amount : off=layers*((m*p)*prior)) :
    off + (bit + span*(0+p*batch) + ((m*p)*span)*layer) =
      start m p prior span bit layers layer batch := by
  rw [amount]
  unfold start
  ring

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem root_start (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m) (t : RowBit G.arcs C₀ b v) :
    (RT v r k t).start=start m p (portPrefix (sz v) (rootHostSlot D m p contact input site owner align s w G first last P v t.1))
      (SlotWidth G.arcs C₀ b v t.1) t.2.val P.layers r.val k.val := by
  have sumEq (j : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) :
      (∑i : Fin j,localWidth H v (Fin.castLE j.isLt.le i))=
      P.layers*(u*portPrefix (sz v) j) := by
    simp only [portPrefix,Finset.mul_sum,tapWidth_eq D (m*p) G P v]
  rcases t with ⟨side|port,x⟩ <;>
    simp only [rootLane,affine,rootColumn,tupleBit,finSigmaFinEquiv_apply]
  · exact root_offset _ _ b x.val P.layers r.val k.val m p
      (sumEq (rootHostSlot D m p contact input site owner align s w G first last P v (.inl side)))
  · exact root_offset _ _ (C₀*b) x.val P.layers r.val k.val m p
      (sumEq (rootHostSlot D m p contact input site owner align s w G first last P v (.inr port)))

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem root_fields (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m) (t : RowBit G.arcs C₀ b v) :
    let l:=((prg ⟨v,.inl false⟩).op (r,k)).arg (rowSerial G.arcs C₀ b v t)
    (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (.inl (.inr ⟨v,0⟩),start m p (portPrefix (sz v)
        (rootHostSlot D m p contact input site owner align s w G first last P v t.1))
        (SlotWidth G.arcs C₀ b v t.1) t.2.val P.layers r.val k.val,SlotWidth G.arcs C₀ b v t.1) := by
  have selected : ((prg ⟨v,.inl false⟩).op (r,k)).arg (rowSerial G.arcs C₀ b v t)=RT v r k t :=
    rotor_operand G.arcs C₀ b (P.rotation r) v (RT v r k) t
  dsimp only
  rw [selected]
  exact Prod.ext rfl (Prod.ext (root_start D m p hp contact input site owner align s w G first last P v r k t) rfl)

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
/-- The actual pair of spine operands is selected directly by operand ordinal zero or one. -/
theorem tap_spine_operand (v : Fin (2^n)) (i : Fin (count H v)) (t : SpineRow (r:=P.layers) (m:=m) (sz v)) (j : Fin 2) :
    ((prg ⟨v,.inr i⟩).op (.inl t)).arg j=tapAt v i (decide (j=0)) t := by fin_cases j <;> rfl

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem tap_select_operand (v : Fin (2^n)) (i : Fin (count H v)) (t : Block P.layers m (sz v i)) :
    (prg ⟨v,.inr i⟩).op (.inr t)=equalOp (.wire (tapAt v i true ⟨i,t⟩))
      (tapLegLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp v i t.1 t.2.1 t.2.2) := rfl

open DescentOrderedWords DescentOrderedReset
open private DescentResetGates.affine from OAI.Hierarchy.DescentOrderedRotorTapLanes

omit [Fintype R] in
theorem public_source_fields (v : Fin (2^n)) (k : Fin m) (e : {e : Item contact owner s w // src e=v}) :
    let l:=falseLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl v k e hp
    let ids:=fibreKey key (input s) (input s e.val.val)
    let occ : DescentNamedContact.Fibre (input s) (input s e.val.val):=⟨e.val.val,rfl⟩
    (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (.inr (rootSlot D contact input site owner (fun _=>u) s w (root contact input site owner s w align e.val)),
        ((before ids occ).card*m+k.val)*p,1) := by
  simp [falseLane,DescentResetGates.affine,portRefFalse,offset,Finset.sum_const]
 ; ring

omit [Fintype R] in
theorem public_target_fields (v : Fin (2^n)) (k : Fin m) (e : {e : Item contact owner s w // dst e=v}) :
    let l:=trueLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl v k e hp
    let ids:=fibreKey key contact (contact e.val.val)
    let occ : DescentNamedContact.Fibre contact (contact e.val.val):=⟨e.val.val,rfl⟩
    (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (.inr (linkSlot D contact input site owner (fun _=>u) s w (link contact owner s w e.val)),
        ((before ids occ).card*m+k.val)*p,1) := by
  simp [trueLane,DescentResetGates.affine,portRefTrue,offset,Finset.sum_const]
 ; ring

private def wireFields {X Y : Type} {left : X→Prop} {right : Y→Prop} {p : ℕ}
    {width : Subtype left ⊕ Subtype right → ℕ}
    (operand : LaneSource p width) : Option ((X ⊕ Y) × ℕ × ℕ) :=
  match operand with
  | .fixed _ => none
  | .wire f => some (Sum.map Subtype.val Subtype.val f.port, f.start, f.stride)

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
/-- A genuinely carried host arc has its original wire ID on either oriented tap. -/
theorem private_supply_fields (e : (H).Edge) (dir : Bool) (r : Fin P.layers) (k : Fin m) (j : Fin (C₀*b)) :
    let l:=legLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp (.inr (e,dir)) r k j
    wireFields l=
      some (.inl (.inl e),start m p 0 (C₀*b) j.val P.layers r.val k.val,C₀*b) := by
  cases dir <;> simp [wireFields,legLane,supplyLane,DescentResetGates.affine,start] <;> ring

end
end Hierarchy.DescentResetLaneIssue

end OAI
