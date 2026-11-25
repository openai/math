import OAI.Hierarchy.DescentStaticUnary
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! Apply one shared unary lookup to indexed source pages, with the option to copy a page. -/
namespace Hierarchy.DescentPackedUnaryPages
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Shape where
  pages : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  inputBits : ℕ
  outputBits : ℕ

namespace Shape
set_option quotPrecheck false
variable (C : Shape)
def rows:=C.hosts*chunks C.groups C.lanes
def width:=C.inputBits*C.lanes
def start (base : ℕ):=base+2*2^C.width
def finish (base : ℕ):=C.start base+C.pages*C.rows+2^Nat.clog 2 (C.rows+1)
def bank (base : ℕ)(j : Fin C.pages) : Bank :=⟨C.start base+j.val*C.rows,Nat.clog 2 (C.rows+1)⟩
theorem translated (base : ℕ) : C.finish base=base+C.finish 0:=by simp [finish,start,Nat.add_assoc]
theorem base_le (base : ℕ) : base≤C.finish base:=by rw [C.translated]; exact Nat.le_add_right ..
variable (law : Cell C.inputBits→Cell 0→Cell C.outputBits) (base : ℕ) (src : Fin C.pages→Bank) (useLut : Fin C.pages→Bool)
def term (j : ℕ) : Expr :=if hj:j<C.pages then
  if useLut ⟨j,hj⟩ then DescentStaticUnary.query law C.lanes base (.lookup (src ⟨j,hj⟩) .row) else .lookup (src ⟨j,hj⟩) .row
  else .lit 0
def passes:=DescentPackedFlowBatch.passes (C.start base) C.rows C.rows (C.term law base src useLut) 0 C.pages
def phase (w : ℕ) : NativePhase w where
  program:=(mount (binary law C.lanes) C.width w base).seq (program w (C.passes law base src useLut))
  ticks:=(4+10*(2*2^C.width))+clock (C.passes law base src useLut)
  image:=fun m=>result (C.passes law base src useLut) (after (binary law C.lanes) C.width base m)
  cheap:=cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap (binary law C.lanes) C.width w base) (program_cheap w (C.passes law base src useLut))
variable {w:ℕ} (m:Memory w) (old : ∀q,(src q).Fits w base) (room : C.finish base<2^w)
include old room in
private theorem fits (j : ℕ) (hj:j<C.pages) : (C.term law base src useLut j).Fits w (C.start base):=by
  let q : Fin C.pages:=⟨j,hj⟩
  have low : base≤C.start base:=Nat.le_add_right ..
  have plain : (Expr.lookup (src q) .row).Fits w (C.start base):=ProtocolRAMGeneratedWrite.fits_mono _ low ⟨old q,trivial⟩
  have top : C.start base<2^w:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt room
  have sz (i:Fin 2) : ((binary law C.lanes) i).bits≤C.width:=by fin_cases i <;> simp [binary,width]
  have placed (i:Fin 2):=(bank_room (binary law C.lanes) C.width base (C.start base) i (sz i) le_rfl top)
  rw [term,dite_eq_left hj]
  split
  · exact ⟨placed 1,trivial,placed 0,plain⟩
  · exact plain

include old room in
theorem any : (C.phase law base src useLut w).Runs m ∧
    ∀a,a<base ∨ C.finish base≤a → (C.phase law base src useLut w).image m a=m a:=by
  let mid:=after (binary law C.lanes) C.width base m
  have low : base≤C.start base:=Nat.le_add_right ..
  have done : C.start base+C.pages*C.rows<2^w:=(Nat.le_add_right ..).trans_lt room
  have top : C.start base<2^w:=(Nat.le_add_right ..).trans_lt done
  have mounted:=DescentOrdinaryAtomFieldRAM.ROM.run (binary law C.lanes) C.width base m top
  have emit:=DescentPackedFlowBatch.execute (C.start base) C.rows C.rows C.pages (C.term law base src useLut) mid
    (C.fits law base src useLut old room) done le_rfl
  refine ⟨?_,?_⟩
  · intro P R K mach pc reg pins stop rom advice cfg raw enter same
    exact Procedure.Exec.then mounted.1 emit.1 mach pc reg pins stop rom advice cfg raw enter same
  intro a away
  have keep:=frame (binary law C.lanes) C.width base m a (away.imp_right (((Nat.le_add_right _ _).trans (Nat.le_add_right ..)).trans ·))
  rcases away with lo|hi
  · exact (emit.2.2 a (lo.trans_le low)).trans keep
  · exact (DescentPackedFlowBatch.above (C.start base) C.rows C.rows _ mid 0 C.pages a le_rfl
      (by simpa only [Nat.zero_add] using (Nat.le_add_right _ _).trans hi)).trans keep

include old room in
theorem issued (empty : law 0 0=0) (q : Fin C.pages) (cap : C.rows≤(src q).size)
    (measured : Fin C.hosts→Fin C.groups→Cell C.inputBits) (copied : Fin C.hosts→Fin C.groups→Cell C.outputBits)
    (raw : useLut q=true→Reads (src q) measured C.lanes m)
    (copy : useLut q=false→Reads (src q) copied C.lanes m) :
    Reads (C.bank base q) (if useLut q then fun h g=>law (measured h g) 0 else copied) C.lanes
      ((C.phase law base src useLut w).image m):=by
  let P:=binary law C.lanes
  let mid:=after P C.width base m
  have done : C.start base+C.pages*C.rows<2^w:=(Nat.le_add_right ..).trans_lt room
  have top : C.start base<2^w:=(Nat.le_add_right ..).trans_lt done
  have emit:=DescentPackedFlowBatch.execute (C.start base) C.rows C.rows C.pages (C.term law base src useLut) mid
    (C.fits law base src useLut old room) done le_rfl
  have page:=DescentStaticUnary.read (H:=C.hosts) (G:=C.groups) (M:=C.lanes) law empty base m top
  intro r
  have row_:=emit.2.1 q (row C.hosts C.groups C.lanes r)
  rw [term,dite_eq_left q.isLt] at row_
  cases use_:useLut q
  · have retained:=eval_below (.lookup (src q) .row) ((row C.hosts C.groups C.lanes r).val:Word w) m mid ⟨old q,trivial⟩ (fun a ha=>page.2.2.1 a (.inl ha))
    have rd:=source_column (src q) base (old q) m copied cap (copy use_)
    simp only [Fin.eta,use_,Bool.false_eq_true,ite_false] at row_
    simpa only [use_,Bool.false_eq_true,ite_false,bank,phase,passes,mid,P] using row_.trans (retained.trans (rd r))
  · have rd:=source_column (src q) base (old q) m measured cap (raw use_)
    have result_:=page.2.1 (.lookup (src q) .row) measured ⟨old q,trivial⟩ rd
    simp only [Fin.eta,use_,ite_true] at row_
    simpa only [use_,ite_true,bank,phase,passes,mid,P] using row_.trans (result_.2 r)

include room in
theorem placed (q : Fin C.pages) : (C.bank base q).Fits w (C.finish base) ∧ C.rows≤(C.bank base q).size:=by
  let pad:=2^Nat.clog 2 (C.rows+1)
  have len : C.rows≤pad:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have hi:=Nat.mul_le_mul_right C.rows q.isLt.le
  change (0<pad ∧ pad<2^w ∧ C.start base+q.val*C.rows+pad≤C.finish base) ∧ _
  change C.start base+C.pages*C.rows+pad<2^w at room
  exact ⟨⟨Nat.two_pow_pos _,by omega,by unfold finish;omega⟩,len⟩

theorem tariff (w : ℕ) : (C.phase law base src useLut w).ticks+7*DescentStaticWordColumn.names
    (C.phase law base src useLut w).program ≤ 1024*(2^C.width+(C.pages+1)*(C.rows+1)):=by
  have work (i : ℕ) (hi : i<C.pages) : (C.term law base src useLut i).work≤25:=by
    rw [term,dite_eq_left hi];split
    · change (DescentPackedZip.Tables.read _ _ _).work≤_
      rw [DescentPackedZip.work];simp [Expr.work]
    · simp [Expr.work]
  have clk:=DescentPackedFlowBatch.tariff (C.start base) C.rows C.rows C.pages (C.term law base src useLut) 25 work
  have code:=DescentOperandVectorArena.names_passes (C.start base) C.rows C.rows w 25 (C.term law base src useLut) 0
    C.pages (fun i _ hi=>work i (by simpa using hi))
  simp only [phase,passes,DescentStaticWordColumn.names_seq,mount,DescentStaticWordColumn.names_mount] at *
  nlinarith only [clk,code,Nat.zero_le (2^C.width),Nat.zero_le C.rows,Nat.zero_le C.pages,
    Nat.zero_le (C.pages*C.rows)]

end Shape
end
end Hierarchy.DescentPackedUnaryPages

end OAI
