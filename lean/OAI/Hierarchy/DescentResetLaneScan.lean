import OAI.Hierarchy.DescentResetLaneIssue
import OAI.Hierarchy.DescentCensusStraightLine
import OAI.Hierarchy.DescentMeasuredHeaderScan

namespace OAI
/-! # A native scan emits the block field directly from the measured layer count and the running row -/

namespace Hierarchy.DescentResetLaneScan
open DescentResetLaneIssue DescentCensusRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section

/-- The row counter is batch + m * layer, exactly the dense rotor root gate order. -/
def blockColumn (w m p prior span bit : ℕ) (layers : Expr) : Expr :=
  .op .add (.op .add (.lit (bit/p)) (DescentSixParty.MarkedCensus.scale (m*prior) layers w))
    (DescentSixParty.MarkedCensus.scale span .row w)

def emitter (w m p prior span bit : ℕ) (layers : Expr) : RowProgram w (blockColumn w m p prior span bit layers) :=
  ((RowProgram.plain w (.lit (bit/p))).plus ((RowProgram.plain w layers).times (m*prior))).plus
    ((RowProgram.plain w .row).times span)

theorem column_fits {w out : ℕ} (m p prior span bit : ℕ) (layers : Expr) (fits : layers.Fits w out) :
    (blockColumn w m p prior span bit layers).Fits w out :=
  ⟨⟨trivial,DescentSixParty.MarkedCensus.scale_fits (m*prior) layers fits w⟩,
    DescentSixParty.MarkedCensus.scale_fits (w:=w) (a:=out) span .row (by trivial) w⟩

theorem execute {w : ℕ} (m p prior span bit : ℕ) (layers : Expr) (mem : Memory w) (out rows : ℕ)
    (fits : layers.Fits w out) (room : out+rows<2^w) :
    ((emitter w m p prior span bit layers).writing out rows).Exec mem
      (ProtocolRAM.image out rows (blockColumn w m p prior span bit layers) mem)
      (4+rows*(2*(emitter w m p prior span bit layers).work+4)) :=
  RowProgram.writing_exec _ _ _ _ (column_fits _ _ _ _ _ _ fits) room

theorem work (w m p prior span bit : ℕ) (layers : Expr) :
    (emitter w m p prior span bit layers).work≤layers.work+10+
      2*(ProtocolRAMPortScale.bitWidth (m*prior)+ProtocolRAMPortScale.bitWidth span) := by
  simp [emitter,RowProgram.plus,RowProgram.times,RowProgram.byConstant,RowProgram.plain,Expr.work]
 ; omega

theorem column_read {w : ℕ} (m p prior span bit : ℕ) (layers : Expr) (count : ℕ) (mem : Memory w)
    (out : ℕ) (r : Fin count) (k : Fin m)
    (measured : layers.eval mem ((finProdFinEquiv (r,k)).val:Word w)=(count : Word w)) :
    ProtocolRAM.image out (count*m) (blockColumn w m p prior span bit layers) mem (out+(finProdFinEquiv (r,k)).val)=
      ((block m p prior span bit count r.val k.val : ℕ):Word w) := by
  rw [DescentMeasuredHeader.image_val _ _ (finProdFinEquiv (r,k))]
  change ((bit/p:ℕ):Word w)+(DescentSixParty.MarkedCensus.scale (m*prior) layers w).eval mem _+
    (DescentSixParty.MarkedCensus.scale span .row w).eval mem _=_
  rw [DescentSixParty.MarkedCensus.full_scale,DescentSixParty.MarkedCensus.full_scale,measured]
  change _+_+(span : Word w)*((k.val+m*r.val : ℕ):Word w)=_
  simp only [block,Nat.cast_add,Nat.cast_mul]
  ring

/-- A concrete installed layer-count cell is the only source word besides the row counter. -/
def layerCell (table : Bank) (base : ℕ) : Expr := .lookup table (.lit base)

theorem cell_scan_read {w : ℕ} (m p prior span bit : ℕ) (table : Bank) (base count : ℕ)
    (baseFits : base<table.size) (word : base<2^w) (mem : Memory w) (out : ℕ)
    (installed : mem (table.base+base)=(count:Word w)) (r : Fin count) (k : Fin m) :
    ProtocolRAM.image out (count*m) (blockColumn w m p prior span bit (layerCell table base)) mem
      (out+(finProdFinEquiv (r,k)).val)=((block m p prior span bit count r.val k.val:ℕ):Word w) := by
  apply column_read
  simpa [layerCell,Expr.eval,Bank.read,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt baseFits] using installed

/-- For public ordered root and leaf words, one true packet-prefix field and the running batch
are sufficient. Both conditional wire choices are made when choosing the endpoint, independently of batch. -/
def contactColumn (w m : ℕ) (prior : Expr) : Expr :=
  .op .add (DescentSixParty.MarkedCensus.scale m prior w) .row

def contactEmitter (w m : ℕ) (prior : Expr) : RowProgram w (contactColumn w m prior) :=
  ((RowProgram.plain w prior).times m).plus (RowProgram.plain w .row)

theorem contact_exec {w : ℕ} (m : ℕ) (prior : Expr) (mem : Memory w) (out : ℕ)
    (fits : prior.Fits w out) (room : out+m<2^w) :
    ((contactEmitter w m prior).writing out m).Exec mem
      (ProtocolRAM.image out m (contactColumn w m prior) mem) (4+m*(2*(contactEmitter w m prior).work+4)) :=
  RowProgram.writing_exec (contactEmitter w m prior) out m mem
    (show (contactColumn w m prior).Fits w out from
      ⟨DescentSixParty.MarkedCensus.scale_fits m prior fits w,trivial⟩) room

theorem contact_read {w : ℕ} (m : ℕ) (prior : Expr) (mem : Memory w) (out paid : ℕ) (k : Fin m)
    (measured : prior.eval mem (k.val:Word w)=(paid:Word w)) :
    ProtocolRAM.image out m (contactColumn w m prior) mem (out+k.val)=((paid*m+k.val:ℕ):Word w) := by
  rw [DescentMeasuredHeader.image_val _ _ k]
  change (DescentSixParty.MarkedCensus.scale m prior w).eval mem _+_=_
  rw [DescentSixParty.MarkedCensus.full_scale,measured]
  simp [Expr.eval,Nat.cast_add,Nat.cast_mul,mul_comm]

section Physical
open DescentLaneGates DescentBatchedRotor DescentPhysicalSplit DescentResetGates DescentRotor DescentRouterSlots
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => m*p
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "sz" => tapBits D u G P
local notation "prg" => DescentBatchedRotor.program D m p hp contact input site owner align s w G first last P key
local notation "slotAt" => rootHostSlot D m p contact input site owner align s w G first last P

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem root_scan {word : ℕ} (table : Bank) (base : ℕ) (baseFits : base<table.size) (numeral : base<2^word)
    (mem : Memory word) (out : ℕ) (installed : mem (table.base+base)=(P.layers:Word word))
    (v : Fin (2^n)) (t : RowBit G.arcs C₀ b v) (r : Fin P.layers) (k : Fin m) :
    let prior:=portPrefix (sz v) (slotAt v t.1)
    let span:=SlotWidth G.arcs C₀ b v t.1
    let node:=(prg ⟨v,.inl false⟩).op (r,k)
    ProtocolRAM.image out (P.layers*m) (blockColumn word m p prior span t.2.val (layerCell table base)) mem
      (out+(finProdFinEquiv (r,k)).val)=(((node.arg (rowSerial G.arcs C₀ b v t)).start/p:ℕ):Word word) := by
  dsimp only
  have address :
      (((prg ⟨v,.inl false⟩).op (r,k)).arg (rowSerial G.arcs C₀ b v t)).start =
      start m p (portPrefix (sz v) (slotAt v t.1)) (SlotWidth G.arcs C₀ b v t.1)
        t.2.val P.layers r.val k.val :=
    congrArg (fun row=>row.2.1) (root_fields D m p hp contact input site owner align s w G first last P key v r k t)
  have blockStart := start_div hp m (portPrefix (sz v) (slotAt v t.1))
    (SlotWidth G.arcs C₀ b v t.1) t.2.val P.layers r.val k.val
  have blockArg := blockStart.symm.trans (congrArg (fun a : ℕ=>a/p) address.symm)
  exact (cell_scan_read m p _ _ _ table base P.layers baseFits numeral mem out installed r k).trans
    (congrArg (fun a : ℕ=>(a : Word word)) blockArg)

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem tap_scan {word : ℕ} (table : Bank) (base : ℕ) (baseFits : base<table.size) (numeral : base<2^word)
    (mem : Memory word) (out : ℕ) (installed : mem (table.base+base)=(P.layers:Word word))
    (v : Fin (2^n)) (i col : Fin (count (P:=Physical.Pin (2^n)) (Physical.host G.arcs D P.layers C₀ b u) v)) (bit : Fin (sz v col))
    (r : Fin P.layers) (k : Fin m) (j : Fin 2) :
    let t : SpineRow (r:=P.layers) (m:=m) (sz v):=⟨col,r,k,bit⟩
    let node:=(prg ⟨v,.inr i⟩).op (.inl t)
    ProtocolRAM.image out (P.layers*m)
      (blockColumn word m p (portPrefix (sz v) col) (sz v col) bit.val (layerCell table base)) mem
      (out+(finProdFinEquiv (r,k)).val)=(((node.arg j).start/p:ℕ):Word word) := by
  dsimp only
  rw [tap_spine_operand]
  have address :
      (tapLane D m p hp contact input site owner align s w G first last P v i
        (decide (j=0)) ⟨col,r,k,bit⟩).start =
      start m p (portPrefix (sz v) col) (sz v col) bit.val P.layers r.val k.val :=
    congrArg (fun row=>row.2.1) (tap_fields D m p hp contact input site owner align s w G first last P
      v i (decide (j=0)) ⟨col,r,k,bit⟩)
  have quotient := (start_div hp m (portPrefix (sz v) col) (sz v col) bit.val P.layers r.val k.val).symm.trans
    (congrArg (fun a : ℕ => a/p) address.symm)
  exact (cell_scan_read m p (portPrefix (sz v) col) (sz v col) bit.val table base P.layers
    baseFits numeral mem out installed r k).trans (congrArg (fun a : ℕ => (a : Word word)) quotient)
end Physical

end
end Hierarchy.DescentResetLaneScan

end OAI
