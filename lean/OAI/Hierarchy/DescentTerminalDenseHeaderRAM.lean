import OAI.Hierarchy.DescentTerminalBankRead
import OAI.Hierarchy.DescentTerminalScanReads
import OAI.Hierarchy.DescentTerminalDenseHeader
import OAI.Hierarchy.DescentTerminalHeaderPrefixRAM

namespace OAI
/-! # Physical quotient, remainder, and clipped-format columns of the dense terminal tape -/

namespace Hierarchy.DescentTerminalDenseHeaderRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure ProtocolRAM DescentTerminalDenseHeader DescentTerminalDenseWindow
open scoped Fin.CommRing
noncomputable section



/-- Immutable tables and input stream, followed by four writable columns. -/
structure Layout where
  widths : Bank
  offset : Bank
  next : Bank
  carry : Bank
  format : Bank
  rem : Bank
  whole : Bank
  index : Bank
  control : Bank

def offsetExpr (L : Layout) : Expr := .lookup L.offset (.lookup L.widths .row)
def previous (b : Bank) : Expr := .branch .eq .row (.lit 0) (.lit 0) (.lookup b (.op .sub .row (.lit 1)))
def sourceKey (L : Layout) : Expr := .op .add (offsetExpr L) (previous L.rem)
def carryExpr (L : Layout) : Expr := .lookup L.carry (sourceKey L)
def fmtExpr (L : Layout) : Expr := .lookup L.format (sourceKey L)

def program (bits n : ℕ) (L : Layout) :=
  (((DescentTerminalHeaderPrefixRAM.program bits L.rem.base n (.read L.next) (offsetExpr L)).seq
    (DescentTerminalHeaderPrefixRAM.program bits L.whole.base n .add (carryExpr L))).seq
    (scan bits L.index.base n (previous L.whole))).seq (scan bits L.control.base n (fmtExpr L))

theorem cheap (bits n : ℕ) (L : Layout) : CheapCode (program bits n L) := by
  let rem:=DescentTerminalHeaderPrefixRAM.program bits L.rem.base n (.read L.next) (offsetExpr L)
  let whole:=DescentTerminalHeaderPrefixRAM.program bits L.whole.base n .add (carryExpr L)
  let index:=scan bits L.index.base n (previous L.whole)
  let control:=scan bits L.control.base n (fmtExpr L)
  change CheapCode (((rem.seq whole).seq index).seq control)
  exact @cheap_seq bits ((rem.seq whole).seq index) control
    (@cheap_seq bits (rem.seq whole) index
      (@cheap_seq bits rem whole
        (@DescentTerminalHeaderPrefixRAM.cheap bits L.rem.base n (.read L.next) (offsetExpr L))
        (@DescentTerminalHeaderPrefixRAM.cheap bits L.whole.base n .add (carryExpr L)))
      (@scan_cheap bits L.index.base n (previous L.whole)))
    (@scan_cheap bits L.control.base n (fmtExpr L))

variable {bits q p n : ℕ}
def remVal (a : Fin n→Profile q p) (k : ℕ) : Word bits := (priorBits a k%(q*p):ℕ)
def wholeVal (a : Fin n→Profile q p) (k : ℕ) : Word bits := (priorBits a k/(q*p):ℕ)

def Header (a : Fin n→Profile q p) (pos : 0<q*p) (i : Fin n) : Word bits :=
  (formatIndex q p (DescentTerminalDenseHeader.control (a i)
    ⟨priorBits a i.val%(q*p),Nat.mod_lt _ pos⟩)).val

def AsTable (b : Bank) (m : Memory bits) (f : Profile q p→Fin (q*p)→ℕ) :=
  ∀a r,b.read m ((key a r).val:Word bits)=(f a r:Word bits)

def Reads (L : Layout) (a : Fin n→Profile q p) (m : Memory bits) : Prop :=
  (∀i : Fin n,L.widths.read m (i.val:Word bits)=((encode q p (a i)).val:Word bits)) ∧
  (∀z : Fin (profiles q p),L.offset.read m (z.val:Word bits)=((z.val*(q*p):ℕ):Word bits)) ∧
  AsTable (q:=q) (p:=p) L.next m residue ∧ AsTable (q:=q) (p:=p) L.carry m DescentTerminalDenseHeader.carry ∧
  AsTable L.format m (fun z rem=>(formatIndex q p (DescentTerminalDenseHeader.control z rem)).val)

/-- The fields are the actual bank/word bounds required by each output
pass, including the short tables and the full input width-profile column. -/
structure Fits (L : Layout) (bits n : ℕ) : Prop where
  source : ∀b∈[L.widths,L.offset,L.next,L.carry,L.format],b.Fits bits L.rem.base
  rem : L.rem.Fits bits L.whole.base
  whole : L.whole.Fits bits L.index.base
  index : L.index.Fits bits L.control.base
  remRoom : n ≤ L.rem.size
  wholeRoom : n ≤ L.whole.size
  indexRoom : n ≤ L.index.size
  endAt : L.control.base+n<2^bits

theorem fits_mono {b : Bank} {old new : ℕ} (fit : b.Fits bits old) (le : old ≤ new) :
    b.Fits bits new := ⟨fit.1,fit.2.1,fit.2.2.trans le⟩

theorem before {b : Bank} {out k : ℕ} (m : Memory bits) (f : ℕ→Word bits) (j : Word bits)
    (fit : b.Fits bits out) : b.read (fillSegment out k f m) j=b.read m j := by
  have small:=Nat.mod_lt j.val fit.1
  have endAt:=fit.2.2
  have lt : b.base+j.val%b.size<out := by omega
  simp [Bank.read,fillSegment,not_le.mpr lt]

/-- A single copy of the four numerical ROM columns suffices for every
group, including every site and branch using this menu. -/
theorem mounted (L : Layout) (a : Fin n→Profile q p) (m : Memory bits) (fit : Fits L bits n)
    (profilesFit : n ≤ L.widths.size) (offsetsFit : profiles q p ≤ L.offset.size)
    (tablesFit : ∀b∈[L.next,L.carry,L.format],profiles q p*(q*p) ≤ b.size)
    (widthCol : ∀i : Fin n,m (L.widths.base+i.val)=((encode q p (a i)).val:Word bits))
    (offsetCol : ∀i : Fin (profiles q p),m (L.offset.base+i.val)=(offsets bits q p)[i.val])
    (nextCol : ∀i : Fin (profiles q p*(q*p)),m (L.next.base+i.val)=(table bits (residue (q:=q) (p:=p)))[i.val])
    (carryCol : ∀i : Fin (profiles q p*(q*p)),m (L.carry.base+i.val)=(table bits (DescentTerminalDenseHeader.carry (q:=q) (p:=p)))[i.val])
    (formatCol : ∀i : Fin (profiles q p*(q*p)),m (L.format.base+i.val)=
      (table bits (fun (z : Profile q p) rem=>(formatIndex q p (DescentTerminalDenseHeader.control z rem)).val))[i.val]) :
    Reads L a m := by
  have read (b : Bank) (which : b∈[L.next,L.carry,L.format]) (f : Profile q p→Fin (q*p)→ℕ)
      (col : ∀i : Fin (profiles q p*(q*p)),m (b.base+i.val)=(table bits f)[i.val]) :
      AsTable b m f := by
    intro z r
    have fromROM : b∈[L.widths,L.offset,L.next,L.carry,L.format] := by simp_all
    exact (bank_nat m (fit.source b fromROM) ((key z r).isLt.trans_le (tablesFit b which))).trans
      ((col (key z r)).trans (table_key bits f z r))
  refine ⟨fun i=>?_,fun i=>?_,read _ (by simp) _ nextCol,read _ (by simp) _ carryCol,read _ (by simp) _ formatCol⟩
  · exact (bank_nat m (fit.source L.widths (by simp)) (i.isLt.trans_le profilesFit)).trans (widthCol i)
  · simpa only [offsets,Vector.getElem_ofFn,Fin.eta] using
      (bank_nat m (fit.source L.offset (by simp)) (i.isLt.trans_le offsetsFit)).trans (offsetCol i)

theorem previous_reads {b : Bank} {t : ℕ} (m : Memory bits) (state : ℕ→Word bits)
    (fit : b.Fits bits t) (room : n ≤ b.size) (zero : state 0=0)
    (written : ∀i : Fin n,m (b.base+i.val)=state (i.val+1)) (i : Fin n) :
    (previous b).eval m (i.val:Word bits)=state i.val := by
  have small : i.val<2^bits := (i.isLt.trans_le room).trans fit.2.1
  have test : ((i.val:Word bits)=0) ↔ i.val=0 := by simp [Fin.ext_iff,Fin.val_cast_of_lt small]
  simp only [previous,Expr.eval,RowOp.opcode,BinaryOp.eval,DescriptorExpr.Comparison.test,
    Nat.cast_zero,Nat.cast_one,beq_iff_eq,test]
  cases eqn : i.val with
  | zero=>simp [zero]
  | succ j=>
    have hj : j<n := by have:=i.isLt;omega
    have diff : (((j+1:ℕ):Word bits)-1)=(j:Word bits) := by rw [Nat.cast_add];simp
    simpa [diff,bank_nat m fit (hj.trans_le room)] using written ⟨j,hj⟩

def cost (n : ℕ) (L : Layout) :=
  ((4+n*(2*DescentTerminalHeaderPrefixRAM.work (.read L.next) (offsetExpr L)+4))+
    (4+n*(2*DescentTerminalHeaderPrefixRAM.work .add (carryExpr L)+4))+
    (4+n*(2*(previous L.whole).work+4)))+(4+n*(2*(fmtExpr L).work+4))

theorem linear_cost (n : ℕ) (L : Layout) : cost n L ≤ 16+300*n := by
  simp [cost,DescentTerminalHeaderPrefixRAM.work,offsetExpr,carryExpr,sourceKey,previous,fmtExpr,Expr.work]; omega

/-- Four linked native passes produce the exact initial dense word number
and small clipped format for every row. The internal adder never stores
the potentially larger absolute bit count. -/
theorem exec_state (L : Layout) (a : Fin n→Profile q p) (pos : 0<q*p) (m : Memory bits)
    (fit : Fits L bits n) (reads : Reads L a m) :
    ∃after, (program bits n L).Exec m after (cost n L) ∧
      (∀i : Fin n,after (L.rem.base+i.val)=remVal a (i.val+1) ∧ after (L.whole.base+i.val)=wholeVal a (i.val+1)) ∧
      (∀i : Fin n,after (L.index.base+i.val)=wholeVal a i.val ∧
        after (L.control.base+i.val)=Header a pos i) := by
  obtain ⟨iw,offs,ns,cs,fs⟩:=reads
  have rEnd:=fit.rem.2.2
  have wEnd:=fit.whole.2.2
  have iEnd:=fit.index.2.2
  have rRoom:=fit.remRoom
  have wRoom:=fit.wholeRoom
  have iRoom:=fit.indexRoom
  have endAt:=fit.endAt
  let r:=fillSegment L.rem.base n (DescentTerminalHeaderPrefixRAM.file L.rem.base (remVal (bits:=bits) a)) m
  let u:=fillSegment L.whole.base n (DescentTerminalHeaderPrefixRAM.file L.whole.base (wholeVal (bits:=bits) a)) r
  let x:=image L.index.base n (previous L.whole) u
  let f:=image L.control.base n (fmtExpr L) x
  have r0 : remVal (bits:=bits) a 0=0 := by simp [remVal,prior_zero]
  have u0 : wholeVal (bits:=bits) a 0=0 := by simp [wholeVal,prior_zero]
  have ord (i : Fin n) : (offsetExpr L).eval m (i.val:Word bits)=(((encode q p (a i)).val*(q*p):ℕ):Word bits) := by
    exact (congrArg (L.offset.read m) (iw i)).trans (offs (encode q p (a i)))
  have oroom : (offsetExpr L).Fits bits L.rem.base := ⟨fit.source _ (by simp),fit.source _ (by simp),trivial⟩
  have runR : (DescentTerminalHeaderPrefixRAM.program bits L.rem.base n (.read L.next) (offsetExpr L)).Exec m r _ :=
    DescentTerminalHeaderPrefixRAM.spec L.rem.base (.read L.next) _ _ _ (fit.source _ (by simp)) oroom (by omega) r0 (by
      intro i
      let v : Fin (q*p):=⟨priorBits a i.val%(q*p),Nat.mod_lt _ pos⟩
      have ans:=ns (a i) v
      simp only [DescentTerminalHeaderPrefixRAM.value,ord,remVal,prior_next]
      rw [show (((priorBits a i.val%(q*p):ℕ):Word bits)+(((encode q p (a i)).val*(q*p):ℕ):Word bits))=
          ((key (a i) v).val:Word bits) by rw [key_val,Nat.cast_add,add_comm],ans,residue_step pos])
  have rread (i : Fin n) : r (L.rem.base+i.val)=remVal a (i.val+1) :=
    DescentTerminalHeaderPrefixRAM.at_row L.rem.base (remVal a) m i
  have prevR (i : Fin n) : (previous L.rem).eval r (i.val:Word bits)=remVal a i.val :=
    previous_reads r _ fit.rem rRoom r0 rread i
  have keyR (i : Fin n) :
      (sourceKey L).eval r (i.val:Word bits)=((key (a i) ⟨priorBits a i.val%(q*p),Nat.mod_lt _ pos⟩).val:Word bits) := by
    have below:=eval_below (offsetExpr L) (i.val:Word bits) m r oroom
      (by intro j h;simp [r,fillSegment,not_le.mpr h])
    change (offsetExpr L).eval r (i.val:Word bits) + (previous L.rem).eval r (i.val:Word bits) = _
    simp only [below,ord i,prevR i,key_val,remVal,Nat.cast_add]
  have sourceFit {out : ℕ} (sep : L.whole.base ≤ out) : (sourceKey L).Fits bits out := by
    have le : L.rem.base ≤ out := by omega
    simp only [sourceKey,offsetExpr,previous,Expr.Fits]
    exact ⟨⟨fits_mono (fit.source _ (by simp)) le,fits_mono (fit.source _ (by simp)) le,trivial⟩,
      trivial,trivial,trivial,fits_mono fit.rem sep,trivial,trivial⟩
  have carryFit : (carryExpr L).Fits bits L.whole.base :=
    ⟨fits_mono (fit.source _ (by simp)) (by omega),sourceFit le_rfl⟩
  have runU : (DescentTerminalHeaderPrefixRAM.program bits L.whole.base n .add (carryExpr L)).Exec r u _ :=
    DescentTerminalHeaderPrefixRAM.spec L.whole.base .add _ _ _ trivial carryFit (by omega) u0 (by
      intro i
      let v : Fin (q*p):=⟨priorBits a i.val%(q*p),Nat.mod_lt _ pos⟩
      change wholeVal a i.val+L.carry.read r ((sourceKey L).eval r (i.val:Word bits))=wholeVal a (i.val+1)
      rw [keyR,before m _ _ (fit.source _ (by simp)),cs]
      simpa only [wholeVal,prior_next,←Nat.cast_add] using congrArg (fun h : ℕ=>(h:Word bits)) (quotient_step pos (priorBits a i.val) (a i)))
  have uread (i : Fin n) : u (L.whole.base+i.val)=wholeVal a (i.val+1) :=
    DescentTerminalHeaderPrefixRAM.at_row L.whole.base (wholeVal a) r i
  have indexFits : (previous L.whole).Fits bits L.index.base :=
    ⟨trivial,trivial,trivial,fit.whole,trivial,trivial⟩
  have runX : (scan bits L.index.base n (previous L.whole)).Exec u x _ :=
    scan_exec L.index.base n (previous L.whole) u indexFits (by omega)
  have fold : (fmtExpr L).Fits bits L.whole.base :=
    ⟨fits_mono (fit.source _ (by simp)) (by omega),sourceFit le_rfl⟩
  have fFit : (fmtExpr L).Fits bits L.control.base :=
    ⟨fits_mono (fit.source _ (by simp)) (by omega),sourceFit (by omega)⟩
  have runF : (scan bits L.control.base n (fmtExpr L)).Exec x f _ :=
    scan_exec L.control.base n (fmtExpr L) x fFit endAt
  let remScan := DescentTerminalHeaderPrefixRAM.program bits L.rem.base n (.read L.next) (offsetExpr L)
  let wholeScan := DescentTerminalHeaderPrefixRAM.program bits L.whole.base n .add (carryExpr L)
  let indexScan := scan bits L.index.base n (previous L.whole)
  let formatScan := scan bits L.control.base n (fmtExpr L)
  have ru := @Procedure.Exec.then bits remScan wholeScan m r u _ _ runR runU
  have rux := @Procedure.Exec.then bits (remScan.seq wholeScan) indexScan m u x _ _ ru runX
  have written := @Procedure.Exec.then bits ((remScan.seq wholeScan).seq indexScan) formatScan m x f _ _ rux runF
  refine ⟨f,written,fun i=>⟨?_,?_⟩,fun i=>⟨?_,?_⟩⟩
  · have hi:=i.isLt
    have lower : L.rem.base+i.val<L.whole.base := by omega
    have low2 : L.rem.base+i.val<L.index.base := by omega
    have low3 : L.rem.base+i.val<L.control.base := by omega
    simpa [f,x,u,image,fillSegment,not_le.mpr lower,not_le.mpr low2,not_le.mpr low3] using
      rread i
  · have hi:=i.isLt
    have lower : L.whole.base+i.val<L.index.base := by omega
    have low2 : L.whole.base+i.val<L.control.base := by omega
    simpa [f,x,image,fillSegment,not_le.mpr lower,not_le.mpr low2] using uread i
  · have lower : L.index.base+i.val<L.control.base := by have hi:=i.isLt;omega
    change image L.control.base n (fmtExpr L) x (L.index.base+i.val)=_
    simp only [image,fillSegment,not_le.mpr lower,false_and,ite_false]
    exact (at_image _ _ u i).trans (previous_reads u _ fit.whole wRoom u0 uread i)
  · rw [show f (L.control.base+i.val)=(fmtExpr L).eval x (i.val:Word bits) from at_image _ _ x i]
    have prev:=eval_below (fmtExpr L) (i.val:Word bits) r x fold (by
      intro j h
      have below : j<L.index.base := by omega
      simp [x,image,u,fillSegment,not_le.mpr h,not_le.mpr below])
    rw [prev]
    change L.format.read r ((sourceKey L).eval r (i.val:Word bits))=_
    rw [keyR,before m _ _ (fit.source _ (by simp)),fs]; rfl

theorem exec (L : Layout) (a : Fin n→Profile q p) (pos : 0<q*p) (m : Memory bits)
    (fit : Fits L bits n) (reads : Reads L a m) :
    ∃after, (program bits n L).Exec m after (cost n L) ∧
      (∀i : Fin n,after (L.index.base+i.val)=wholeVal a i.val ∧
        after (L.control.base+i.val)=Header a pos i) := by
  obtain ⟨after,run,_,rows⟩:=exec_state L a pos m fit reads
  exact ⟨after,run,rows⟩

def eof (m : Memory bits) (b : Bank) (n : ℕ) : Word bits :=
  if n=0 then 0 else m (b.base+(n-1))

theorem eof_read (m : Memory bits) (b : Bank) (a : ℕ→Word bits) (zero : a 0=0)
    (written : ∀i : Fin n,m (b.base+i.val)=a (i.val+1)) :
    eof m b n=a n := by
  cases n with
  | zero=>simp [eof,zero]
  | succ k=>simpa [eof] using written (Fin.last k)

/-- The mathematical count need only fit after division by the dense-row
size. Every physical row advances by at most one whole dense word. -/
theorem number_room (a : Fin n→Profile q p) (pos : 0<q*p) (i : Fin n) :
    priorBits a i.val/(q*p) ≤ i.val := by
  have total := delta (fun s=>mass (a s)) (fun s=>mass_le (a s)) 0 i.val
  have cap : priorBits a i.val ≤ i.val*(q*p) := by simpa [priorBits,pref] using total
  exact (Nat.div_le_div_right cap).trans (by simp [Nat.mul_div_cancel _ pos])

end
end Hierarchy.DescentTerminalDenseHeaderRAM

end OAI
