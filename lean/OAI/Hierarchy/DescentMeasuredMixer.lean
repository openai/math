import OAI.Hierarchy.DescentNativeEstimatorWork
import OAI.Hierarchy.DescentGLPhysicalHardware

namespace OAI
/-! # One physical optimizer from the prior load words to the chosen invertible map -/

namespace Hierarchy.DescentMeasuredMixer
open DescentGL DescentGLScoreRAM DescentNativeColumns DescentIntegerScale DescentWeightColumnRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- Depth and coefficient pointers in the old header. The correlation
pointer of slot i is always computed by the physical first pass. -/
structure Header where
  payload : ℕ
  depth : ℕ
  gain : ℕ

def row {N : ℕ} (k base : ℕ) (table : Fin N→Header) (i : Fin N) : Row :=
  ⟨address k base i.val,(table i).depth,(table i).gain⟩

def keyBase (k base N : ℕ) := address k base N

def mixerBase (k base N : ℕ) := address k (keyBase k base N) (k+1)

def loadCode {N : ℕ} (w k base p : ℕ) (table : Fin N→Header) : Procedure w :=
  code w k base (fun j=>DescentCorrelationRAM.machine w k
    (if hj : j<N then (table ⟨j,hj⟩).payload else 0) (address k base j) p) N

def weightCode {N : ℕ} (w k base p : ℕ) (table : Fin N→Header) : Procedure w :=
  code w k (keyBase k base N) (fun j=>pass k w (address k (keyBase k base N) j) j p (row k base table)) (k+1)

def stages {N : ℕ} (w k base bits gainBits : ℕ) (table : Fin N→Header) : Procedure w :=
  ((loadCode w k base bits table).seq (weightCode w k base gainBits table)).seq
    (PhysicalTrajectory.program w k (mixerBase k base N) (address k (keyBase k base N)))

def measuredTime {N : ℕ} (w k base bits gainBits : ℕ) (tab : Fin N→Header) :=
  cost (fun j=>4+2^k*(2*(DescentCorrelationRAM.term w k
    (if hj : j<N then (tab ⟨j,hj⟩).payload else 0) (address k base j) bits).binds+4)) N+
  cost (fun j=>4+2^k*(2*(vector k w (address k (keyBase k base N) j) j gainBits (row k base tab)).binds+4)) (k+1)+
    (PhysicalTrajectory.time k (mixerBase k base N) (address k (keyBase k base N)) k+
      DescentGLPermutationRAM.clock k)

theorem result {w k base bits gainBits scoreBits q N : ℕ} (m : Memory w) (tab : Fin N→Header)
    (load : Fin N→DescentGL.Bits k→ℕ) (depth gain : Fin N→ℕ) (initial : Layout k)
    (room : PhysicalTrajectory.Room w k (mixerBase k base N) (address k (keyBase k base N)))
    (word : 3*k+scoreBits+2≤w) (normal : 0<q) (width : bits≤w ∧ gainBits≤w)
    (layout : ∀i,(Bank.mk (tab i).payload k).Fits w base ∧ (tab i).depth<base ∧ (tab i).gain<base)
    (head : ∀i,m (tab i).depth=(depth i:Word w) ∧ m (tab i).gain=(gain i:Word w))
    (input : ∀i (z : Fin (2^k)),m ((tab i).payload+z.val)=(load i (vec z):Word w))
    (bounds : ∀i,depth i<2^w ∧ gain i<2^gainBits ∧ ∀x,load i x<2^bits)
    (caps : ∀j : Fin (k+1),∀d,money j.val depth gain (fun i=>natCorrelation (load i)) d≤2^scoreBits) :
    let W := fun j : Fin (k+1)=>money j.val depth gain (fun i=>natCorrelation (load i))
    let outcome := allDepthCollisionCost (PhysicalTrajectory.Weights W q)
    ∃ (out : Memory w) (μ : Layout k),
      (stages w k base bits gainBits tab).Exec m out (measuredTime w k base bits gainBits tab) ∧
      outcome μ ≤ (∑L,outcome L)/Fintype.card (Layout k) ∧
      (∀i : Fin k,out (PhysicalTrajectory.pointer k (mixerBase k base N) i.val)=
        ((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
      (∀z : Fin (2^k),out (PhysicalTrajectory.outputBase k (mixerBase k base N)+z.val)=
        ((finFunctionFinEquiv (μ (vec z))).val:Word w)) ∧ ∀a<base,out a=m a := by
  let B := keyBase k base N
  let M := mixerBase k base N
  let src := fun i : ℕ=> if hi : i<N then (tab ⟨i,hi⟩).payload else 0
  let data (i : ℕ) : DescentGL.Bits k→ℕ := if hi : i<N then load ⟨i,hi⟩ else fun _=>0
  let cv (i : ℕ) (j : Fin (2^k)) : Word w := natCorrelation (data i) (vec j)
  let m₁ := accumulated k base cv m N
  have start : base≤B := Nat.le_add_right ..
  have mid : B≤ M := Nat.le_add_right ..
  have Msmall : M<2^w := by
    have first : M ≤ M+k*(3*2^k+1) := Nat.le_add_right ..
    have output : M ≤ PhysicalTrajectory.outputBase k M :=
      first.trans (Nat.le_add_right _ (2^k))
    exact (output.trans (Nat.le_add_right _ (2^k))).trans_lt room.last
  have c := correlations (N:=N) m src data (show address k base N<2^w from mid.trans_lt Msmall)
    width.1 (fun i hi=>by simpa [src,hi] using (layout ⟨i,hi⟩).1)
    (fun i hi j=>by simpa [src,data,hi] using input ⟨i,hi⟩ j)
    (fun i hi x=>by simpa [data,hi] using (bounds ⟨i,hi⟩).2.2 x)
  have prior : ∀a<base,m₁ a=m a := untouched k base cv m N
  let rows := row k base tab
  let corr i := natCorrelation (load i)
  have outputBound := room.last
  have wh := Nat.lt_two_pow_self (n:=k)
  have wpos : 2^k<2^w := by
    have e := room.tables (0:Fin (k+1))
    change B+0*2^k+2^k≤ M at e
    omega
  have safe (i : Fin N) : Fits w B k (rows i) := by
    have before := Nat.mul_le_mul_right (2^k) (show i.val+1≤N from i.isLt)
    rw [Nat.succ_mul] at before
    exact ⟨⟨Nat.two_pow_pos _,wpos,by dsimp [rows,row,address,B,keyBase,Bank.size];omega⟩,
      ((layout i).2.1.trans_le start),((layout i).2.2.trans_le start)⟩
  have e := estimates m₁ rows depth gain corr Msmall width.2 safe (by omega)
    (fun i=>⟨(bounds i).1,(bounds i).2.1⟩)
    (fun i=>⟨(prior _ (layout i).2.1).trans (head i).1,(prior _ (layout i).2.2).trans (head i).2⟩)
    (fun i j=>by simpa [rows,row,cv,data,corr,m₁] using c.2 i.val i.isLt j)
  let val (l : ℕ) (i : Fin (2^k)) : Word w := money l depth gain corr (vec i)
  let m₂ := accumulated k B val m₁ (k+1)
  obtain ⟨gl,μ,price,pointers,permutation,kept⟩ :=
    PhysicalTrajectory.mixing (address k B) (fun j : Fin (k+1)=>money j.val depth gain corr)
      initial m₂ room normal word caps e.2
  refine ⟨PhysicalTrajectory.finalMemory k M (address k B) m₂,μ,?_,price,pointers,permutation,?_⟩
  · exact Procedure.Exec.then (Procedure.Exec.then c.1 e.1) gl
  intro a ha
  exact (kept a ((ha.trans_le start).trans_le mid)).trans
    ((untouched k B val m₁ (k+1) a (ha.trans_le start)).trans (prior a ha))

end
end Hierarchy.DescentMeasuredMixer

end OAI
