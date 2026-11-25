import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Numerical scalar root headers followed by a shared packed-word broadcast -/
namespace Hierarchy.DescentActorRaster.Headers
open DescentIssuedTerminalId Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H Q w : ℕ}

inductive Control
  | one
  | rotor
  | tree (bookField : ℕ)
  deriving DecidableEq

structure Banks where
  population : Bank
  originalDepth : Bank
  counts : Bank
  hostStart : Bank
  levels : Bank
  heights : Bank

def select (B : Banks) : Control→Expr
  | .one=>.lit 1
  | .rotor=>.lookup B.levels (.lookup B.originalDepth .row)
  | .tree i=>.lookup B.heights (.lookup B.counts (.op .add (.lookup B.hostStart .row) (.lit i)))

def expression (B : Banks) (op : Control) : Expr :=
  .branch .lt .row (.lookup B.population (.lit 0)) (select B op) (.lit 0)

def value (used common : ℕ) (depth : Fin H→ℕ) (total : Fin H→ℕ→ℕ) (op : Control) (h : Fin H) :=
  if h.val<used then match op with
    | .one=>1
    | .rotor=>depth h-common+1
    | .tree i=>Nat.clog 2 (total h i)+1
  else 0

def passes (B : Banks) (op : Fin Q → Control) (out H : ℕ) :=
  ProbeStage.Native.columns H out (List.ofFn (fun j=>expression B (op j)))

theorem evaluated (B : Banks) (op : Control) (m : Memory w) (out H used common width : ℕ)
    (v : Fin H) (depth : Fin H→ℕ) (total : Fin H→ℕ→ℕ)
    (fit : (expression B op).Fits w out) (live : used<2^w) (hosts : H≤2^w)
    (limits : ∀b∈[B.population,B.originalDepth,B.counts,B.hostStart,B.levels,B.heights],b.size<2^w)
    (roster : m B.population.base=(used:Word w))
    (rd : v.val<used→m (B.originalDepth.base+v.val)=(depth v:Word w))
    (start : m (B.hostStart.base+v.val)=((v.val*width:ℕ):Word w))
    (numbers : ∀i,op=.tree i→v.val<used→m (B.counts.base+(v.val*width+i))=(total v i:Word w))
    (depths : ∀j,j<B.levels.size→m (B.levels.base+j)=((j-common+1:ℕ):Word w))
    (heights : ∀j,j<B.heights.size→m (B.heights.base+j)=((Nat.clog 2 j+1:ℕ):Word w))
    (sizes : H≤B.originalDepth.size ∧ H≤B.hostStart.size ∧ H*width≤B.counts.size)
    (field : ∀i,op=.tree i→i<width)
    (values : v.val<used→(op=.rotor→depth v<B.levels.size) ∧ ∀i,op=.tree i→total v i<B.heights.size) :
    (expression B op).eval m (v.val:Word w)=(value used common depth total op v:Word w) := by
  have small:=v.isLt.trans_le hosts
  have countRead : (Expr.lookup B.population (.lit 0)).eval m (v.val:Word w)=(used:Word w):=by
    have z : 0<B.population.size:=Nat.two_pow_pos _
    exact (lookup_nat B.population m (v.val:Word w) (.lit 0) 0 rfl z (limits _ (by simp))).trans
      (by simpa only [Nat.add_zero] using roster)
  change (if Comparison.lt.test (v.val:Word w) ((Expr.lookup B.population (.lit 0)).eval m (v.val:Word w)) then (select B op).eval m _ else 0)=_
  rw [countRead]
  simp only [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt small,Fin.val_cast_of_lt live,decide_eq_true_eq]
  by_cases yes:v.val<used
  · simp only [value,yes,ite_true]
    cases op with
    | one=>rfl
    | rotor=>
      have b:= (lookup_nat B.originalDepth m (v.val:Word w) .row v.val rfl (v.isLt.trans_le sizes.1)
        (limits _ (by simp))).trans (rd yes)
      apply (lookup_nat B.levels m (v.val:Word w) (.lookup B.originalDepth .row) (depth v) b
        ((values yes).1 rfl) (limits _ (by simp))).trans (depths _ ((values yes).1 rfl))
    | tree ix=>
      let addr:=Expr.op .add (.lookup B.hostStart .row) (.lit ix)
      have hi:=field ix rfl
      have startRead:=(lookup_nat B.hostStart m (v.val:Word w) .row v.val rfl (v.isLt.trans_le sizes.2.1)
        (limits _ (by simp))).trans start
      have atWord : addr.eval m (v.val:Word w)=((v.val*width+ix:ℕ):Word w):=by
        change (Expr.lookup B.hostStart .row).eval m _+(ix:Word w)=_
        rw [startRead,Nat.cast_add]
      have addrFit:v.val*width+ix<B.counts.size:=(Nat.add_lt_add_left hi _).trans_le
        (by rw [←Nat.succ_mul];exact (Nat.mul_le_mul_right _ v.isLt).trans sizes.2.2)
      have cnt:=(lookup_nat B.counts m (v.val:Word w) addr _ atWord addrFit (limits _ (by simp))).trans (numbers _ rfl yes)
      exact (lookup_nat B.heights m (v.val:Word w) (.lookup B.counts addr) _ cnt
        ((values yes).2 _ rfl) (limits _ (by simp))).trans (heights _ ((values yes).2 _ rfl))
  · simp [value,yes]

theorem issue (B : Banks) (op : Fin Q → Control) (m : Memory w) (out H : ℕ)
    (fit : ∀j,(expression B (op j)).Fits w out) (room : out+Q*H<2^w) :
    let jobs:=passes B op out H;let done:=ProtocolRAM.result jobs m
    (ProtocolRAM.program w jobs).Exec m done (ProtocolRAM.clock jobs) ∧
    (∀(j:Fin Q)(h:Fin H),done (out+j.val*H+h.val)=(expression B (op j)).eval m (h.val:Word w)) ∧
    (∀u,u<out ∨ out+Q*H≤u→done u=m u) ∧ CheapCode (ProtocolRAM.program w jobs) := by
  let es:=List.ofFn (fun j=>expression B (op j))
  have fs:∀e∈es,e.Fits w out:=by intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;apply fit
  have len:es.length=Q:=List.length_ofFn
  refine ⟨ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es le_rfl fs (by simpa only [len] using room)),?_,?_,@ProtocolRAM.program_cheap _ _⟩
  · intro j h
    simpa [passes,es] using ProbeStage.Native.columns_read (base:=out) es m le_rfl fs j.val (j.isLt.trans_eq len.symm) h
  · intro z hz
    exact ProbeStage.Native.columns_frame es m (by simpa [len] using hz)

end
end Hierarchy.DescentActorRaster.Headers

end OAI
