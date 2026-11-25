import OAI.Hierarchy.DescentPackedScalarDonorOperands
import OAI.Hierarchy.DescentColumnHardware

namespace OAI
/-! # One native old-geometry book run for all primitive pages and all venues -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F Q D k K K' cap a nb mb H G M w : ℕ}
set_option quotPrecheck false
local notation "P₀" => breadth D
local notation "donors" => (breadth D*2^k)
local notation "actors" => DescentPackedActorMask.actors donors cap
local notation "nodes" => DescentPackedActorMask.nodes donors K cap

structure Refs (D k K cap : ℕ) where
  tables : TablesAt
  gates : Fin (DescentPackedActorMask.nodes (breadth D*2^k) K cap)→Tables
  ports : Ports (breadth D)
  previous : Fin (2^k)→Bank
  birth : Fin (2^k)→Fin cap→Fin 6→Bank
  dictionary : Fin K→Bank
  want : Expr
  addr : Expr
  counts : Expr

def Refs.read (C : Refs D k K cap) (H : ℕ) (j : Fin nodes) : Expr :=
  operand C.ports C.previous C.birth C.dictionary H (bookRoot D k K cap j) (bookBlock D k K cap j) (bookItem D k K cap j)

def Refs.expr (C : Refs D k K cap) (H : ℕ) :=resultExpr C.tables C.gates (C.read H) C.want C.addr C.counts

structure Values (D k K cap H G a nb mb : ℕ) where
  walks : Fin H→Fin (breadth D)→Option (Fin H)
  old : Fin (2^k)→Fin H→Fin G→Cell (a*K)
  born : Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell a
  wanted : Fin H→Fin G→Cell nb
  venues : Fin H→Fin G→Fin (DescentPackedActorMask.actors (breadth D*2^k) cap)→Cell nb
  counts : Fin H→Fin G→Fin (breadth D*2^k)→Cell mb

def Values.book (V : Values D k K cap H G a nb mb) (K' : ℕ) (h : Fin H) (g : Fin G) :=
  let mask:=DescentPackedActorMask.occupied donors K cap mb (DescentPackedActorMask.target nb actors (V.wanted h g) (encode nb actors (V.venues h g))) (encode mb donors (V.counts h g))
  let fields:=fun j=>(DescentSortedRoster.indexed V.walks h (bookRoot D k K cap j)).elim 0
    (fun v=>item V.old V.born (bookBlock D k K cap j) (bookItem D k K cap j) v g)
  DescentPackedLocalAtoms.pack a nodes K' mask (encode a nodes fields)

structure Measured (C : Refs D k K cap) (V : Values D k K cap H G a nb mb) (K' M base : ℕ) (mem : Memory w) : Prop where
  mounted : Mounted C.ports (DescentSortedRoster.indexed V.walks) mem G M
  old : ∀b,Reads (C.previous b) (V.old b) M mem
  new_ : ∀b i j,Reads (C.birth b i j) (V.born b i j) M mem
  fromOld : ∀b,Accessible C.ports (C.previous b) H G M w base
  fromNew : ∀b i j,Accessible C.ports (C.birth b i j) H G M w base
  dictFits : ∀j,(C.dictionary j).Fits w base ∧ (C.dictionary j).bits=(a*K)*M
  dictionary : ∀j (x : Cell ((a*K)*M)),mem ((C.dictionary j).base+x.val)=((DescentSIMDLookup.table (M:=M) (take (a:=a) j) x).val:Word w)
  wants : Source C.want V.wanted M mem
  venues : Source C.addr (fun h g=>encode nb actors (V.venues h g)) M mem
  counts : Source C.counts (fun h g=>encode mb donors (V.counts h g)) M mem
  targetFits : DescentPackedZip.Fits C.tables.targets C.want C.addr nb (nb*actors) M base w
  actorFits : DescentPackedZip.Fits C.tables.actors (C.tables.targets.read C.want C.addr) C.counts (1*actors) (mb*donors) M base w
  fieldFits : Gather.Bounds (w:=w) (d:=a) (M:=M) C.gates (C.read H) base
  emitFits : DescentPackedZip.Fits C.tables.emitted (masked C.tables C.want C.addr C.counts) (Gather.assembly C.gates (C.read H)) (1*nodes) (a*nodes) M base w
  targets : Static C.tables.targets (DescentPackedActorMask.target nb actors) M mem
  «actors» : Static C.tables.actors (DescentPackedActorMask.occupied donors K cap mb) M mem
  fields : ∀j,Static (C.gates j) (Gather.setField (d:=a) j) M mem
  emit : Static C.tables.emitted (DescentPackedLocalAtoms.pack a nodes K') M mem

variable (C : Fin F→Fin Q→Refs D k K cap) (V : Fin F→Fin Q→Values D k K cap H G a nb mb)

def expressions (H : ℕ) :=List.ofFn fun j : Fin (F*Q)=>let z:=finProdFinEquiv.symm j;(C z.1 z.2).expr H

def columns (base H G M : ℕ) :=ProbeStage.Native.columns (H*chunks G M) base (expressions C H)

def place (base Q H G M page low : ℕ) :=base+(page*Q+low)*(H*chunks G M)

/-- The rectangular controller runs on every prior memory once the actual
immutable operand banks are earlier than the output region. -/
theorem exec (base H G M : ℕ) (m : Memory w)
    (early : ∀p l,((C p l).expr H).inputEnd≤base) (wide : base+(F*Q)*(H*chunks G M)<2^w) :
    let ps:=columns C base H G M;(program w ps).Exec m (result ps m) (clock ps) :=by
  intro ps;apply ProbeStage.Native.columns_exec
  apply ProbeStage.Native.columns_safe _ le_rfl
  · intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    apply Expr.fits_of_inputEnd _ (early _ _) ((Nat.le_add_right ..).trans_lt wide)
  · simpa only [expressions,List.length_ofFn] using wide

theorem all_books (base K' M : ℕ) (m : Memory w)
    (measured : ∀p l,Measured (C p l) (V p l) K' M base m) (end_ : base+(F*Q)*(H*chunks G M)<2^w) :
    let ps:=columns C base H G M;let state:=ProtocolRAM.result ps m
    (ProtocolRAM.program w ps).Exec m state (ProtocolRAM.clock ps) ∧
      (∀(page : Fin F) (l : Fin Q) (p : Row H G M),state (place base Q H G M page.val l.val+(row H G M p).val)=((data ((V page l).book K') p).val:Word w)) ∧
      (∀j,j<base ∨ base+(F*Q)*(H*chunks G M) ≤ j → state j=m j) ∧ CheapCode (ProtocolRAM.program w ps) :=by
  intro ps state
  let es:=expressions C H;let n:=H*chunks G M
  have length_:es.length=F*Q:=by simp [es,expressions]
  have fitted:∀e∈es,e.Fits w base:=by
    intro e member
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member
    let z:Fin F×Fin Q:=finProdFinEquiv.symm j;have data_:=measured z.1 z.2;let t:=C z.1 z.2
    change (t.tables.emitted.read (masked t.tables t.want t.addr t.counts) (Gather.assembly t.gates (t.read H))).Fits w base
    exact ⟨data_.emitFits.apply,data_.emitFits.right,data_.emitFits.shift,data_.emitFits.left⟩
  have cap_:base+es.length*n<2^w:=by simpa only [length_,n] using end_
  refine ⟨ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es le_rfl fitted cap_),?_,?_,@ProtocolRAM.program_cheap _ _⟩
  · intro page l p
    let z:Fin (F*Q):=finProdFinEquiv (page,l);let t:=C page l;let val:=V page l;have h:=measured page l
    have one : base+n<2^w:=(Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right n (Nat.zero_lt_of_lt z.isLt)) _).trans_lt end_
    have physical:=(run_books t.tables t.gates t.ports t.previous t.birth t.dictionary t.want t.addr t.counts base K' m val.walks h.mounted val.old val.born h.old h.new_ h.fromOld h.fromNew h.dictFits h.dictionary val.wanted val.venues val.counts h.wants h.venues h.counts h.targetFits h.actorFits h.fieldFits h.emitFits one h.targets h.actors h.fields h.emit).2.1 p
    have atZ:=ProbeStage.Native.columns_read es m le_rfl fitted z.val (z.isLt.trans_eq length_.symm) (row H G M p)
    have idx:z.val=page.val*Q+l.val:=by
      change l.val+Q*page.val=page.val*Q+l.val
      ac_rfl
    have seen:(es[z.val]'(z.isLt.trans_eq length_.symm))=t.expr H:=by
      simpa only [es,expressions,List.getElem_ofFn] using
        congrArg (fun pair : Fin F×Fin Q=>(C pair.1 pair.2).expr H)
          (finProdFinEquiv.symm_apply_apply (page,l))
    rw [seen,idx] at atZ
    exact atZ.trans ((ProtocolRAMGeneratedWrite.read_image base n (t.expr H) m (row H G M p)).symm.trans physical)
  · intro j away;apply ProbeStage.Native.columns_frame es m;simpa only [length_] using away

/-- One remote read costs 45 expression instructions. An inherited scalar
uses one additional five-instruction digit lookup. -/
theorem read_work (t : Refs D k K cap) (j : Fin nodes) : (t.read H j).work≤50 :=by
  unfold Refs.read operand
  cases finSumFinEquiv.symm (bookItem D k K cap j) with
  | inl slot => simp only [Sum.elim_inl,project,peerExpr,neighborID,Expr.work]; decide
  | inr slot => simp only [Sum.elim_inr,peerExpr,neighborID,Expr.work]; decide

def termBound («nodes» source : ℕ) :=source+34+«nodes»*61

theorem term_work (t : Refs D k K cap) : (t.expr H).work≤termBound nodes (t.want.work+t.addr.work+t.counts.work) :=by
  have compact (is : List (Fin nodes)) : (Gather.collect t.gates (t.read H) is).work≤1+is.length*61:=by
    induction is with
    | nil => rfl
    | cons j js ih =>
      have := read_work (H:=H) t j
      simp only [Gather.collect,Tables.read,Expr.work,List.length_cons,Nat.succ_mul];omega
  have bound:=compact (List.finRange nodes)
  simp only [List.length_finRange] at bound
  simp only [Refs.expr,resultExpr,masked,Tables.read,Expr.work,Gather.assembly,termBound];omega

theorem tariff (base H G M w source : ℕ) (inputs : ∀f l,let t:=C f l;t.want.work+t.addr.work+t.counts.work≤ source) :
    let bound:=termBound nodes source;let ps:=columns C base H G M;let p:=program w ps
    clock ps≤4+(F*Q)*(4+(H*chunks G M)*(2*bound+4)) ∧
      p.labels+p.registers+p.slots≤15+(F*Q)*(11+4*bound) :=by
  intro bound ps p
  have fit:∀e∈expressions C H,e.work≤bound:=by
    intro e he;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    let z:Fin F×Fin Q:=finProdFinEquiv.symm i
    apply (term_work (H:=H) (C z.1 z.2)).trans
    exact Nat.add_le_add_right (Nat.add_le_add_right (inputs z.1 z.2) _) _
  constructor
  · simpa [ps,columns,expressions] using ProbeStage.Native.columns_clock (H*chunks G M) base bound (expressions C H) fit
  · simpa [p,ps,columns,expressions] using labels_registers (expressions C H) base (H*chunks G M) bound w fit

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
