import OAI.Hierarchy.DescentWeightColumnRAM
import OAI.Hierarchy.DescentGLGeometryRAM

namespace OAI
/-! # Chronological construction of the physical GL input columns -/

namespace Hierarchy.DescentNativeColumns
open DescentGL DescentGLScoreRAM ProtocolRAM DescentIntegerScale
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped BigOperators Fin.CommRing Classical
noncomputable section

def address (k base j : ℕ) := base+j*2^k

private theorem end_address (k base j : ℕ) :
    address k base (j+1)=address k base j+2^k := by simp [address,Nat.succ_mul,Nat.add_assoc]

/-- Use one actual four-tick empty scan for the empty family. Subsequent calls write
contiguous fresh columns, so every original header and earlier result remains readable. -/
def code (w k base : ℕ) (cpu : ℕ→Procedure w) : ℕ→Procedure w
  | 0=>scan w base 0 (.lit 0)
  | j+1=>(code w k base cpu j).seq (cpu j)

def cost (timer : ℕ→ℕ) : ℕ→ℕ
  | 0=>4
  | j+1=>cost timer j+timer j

def accumulated {w : ℕ} (k base : ℕ) (val : ℕ→Fin (2^k)→Word w) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | j+1=>fillSegment (address k base j) (2^k)
      (fun a=>val j ⟨(a-address k base j)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (accumulated k base val m j)

theorem untouched {w : ℕ} (k base : ℕ) (val : ℕ→Fin (2^k)→Word w) (m : Memory w) (j l : ℕ) (lo : l<base) :
    accumulated k base val m j l=m l := by
  induction j with
  | zero=>rfl
  | succ j ih=>simpa [accumulated,fillSegment,address,show ¬base+j*2^k≤l by omega] using ih

theorem read {w : ℕ} (k base : ℕ) (val : ℕ→Fin (2^k)→Word w) (m : Memory w)
    (j l : ℕ) (h : l<j) (i : Fin (2^k)) :
    accumulated k base val m j (address k base l+i.val)=val l i := by
  induction j with
  | zero=>omega
  | succ j ih=>
    by_cases last : l=j
    · subst l
      simp [accumulated,fillSegment,Nat.add_lt_add_left i.isLt,Nat.mod_eq_of_lt i.isLt]
    · have order := Nat.mul_le_mul_right (2^k) (show l+1≤j by omega)
      rw [Nat.succ_mul] at order
      have low : address k base l+i.val<address k base j := by unfold address;omega
      simpa [accumulated,fillSegment,low.not_ge] using ih (by omega)

theorem execute {w : ℕ} (k base : ℕ) (cpu : ℕ→Procedure w) (timer : ℕ→ℕ)
    (N : ℕ) (m : Memory w) (val : ℕ→Fin (2^k)→Word w) (room : base<2^w)
    (step : ∀j<N,∀m' : Memory w,(∀a<base,m' a=m a) →
      (cpu j).Exec m' (fillSegment (address k base j) (2^k)
        (fun a=>val j ⟨(a-address k base j)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩) m') (timer j)) :
    (code w k base cpu N).Exec m (accumulated k base val m N) (cost timer N) := by
  induction N with
  | zero =>
    have empty : ProtocolRAM.image base 0 (.lit 0) m = m := by
      funext a
      simp [ProtocolRAM.image, fillSegment]
    have run : (scan w base 0 (.lit 0)).Exec m (ProtocolRAM.image base 0 (.lit 0) m) 4 := by
      intro programs registers slots
      exact @scan_exec w base 0 (.lit 0) m trivial (by omega) programs registers slots
    rw [empty] at run
    exact @run
  | succ j ih =>
    exact Procedure.Exec.then (ih (fun i hi=>step i (by omega)))
      (step j (by omega) _ (untouched k base val m j))

/-- All correlation columns originate in the same original memory. They are numbered
once in public code and written in that order by real cheap product kernels. -/
theorem correlations {w k base bits N : ℕ} (m : Memory w) (src : ℕ→ℕ)
    (x : ℕ→DescentGL.Bits k→ℕ) (endFit : address k base N<2^w)
    (measured : bits≤w) (input : ∀j<N,(Bank.mk (src j) k).Fits w base)
    (values : ∀j<N,∀i : Fin (2^k),m (src j+i.val)=(x j (vec i):Word w))
    (bounded : ∀j<N,∀i,x j i<2^bits) :
    let cpu := fun j=>DescentCorrelationRAM.machine w k (src j) (address k base j) bits
    let timer := fun j=>4+2^k*(2*(DescentCorrelationRAM.term w k (src j) (address k base j) bits).binds+4)
    let val := fun j (i : Fin (2^k))=>(natCorrelation (x j) (vec i):Word w)
    (code w k base cpu N).Exec m (accumulated k base val m N) (cost timer N) ∧
      ∀j<N,∀i : Fin (2^k),accumulated k base val m N (address k base j+i.val)=val j i := by
  refine ⟨execute k base _ _ N m _ (by unfold address at endFit;omega) ?_,read k base _ m N⟩
  intro j hj mem orig
  have fit := input j hj
  have reach := Nat.mul_le_mul_right (2^k) (show j+1≤N by omega)
  rw [Nat.succ_mul] at reach
  intro programs registers slots
  exact @DescentCorrelationRAM.run w k (src j) (address k base j) bits mem (x j) ⟨fit.1,fit.2.1,fit.2.2.trans (Nat.le_add_right ..)⟩
    (by unfold address at *;omega) measured (fun i=>
      (orig _ (by have hold:=fit.2.2;change src j+2^k≤base at hold;omega)).trans (values j hj i)) (bounded j hj) programs registers slots

/-- At stage l, read all *measured* row headers and the actual earlier correlation
columns. None of these addresses overlaps the growing bank for depth scores. -/
theorem estimates {w k base precision N : ℕ} (m : Memory w) (rows : Fin N→DescentWeightColumnRAM.Row)
    (level gain : Fin N→ℕ) (corr : Fin N→DescentGL.Bits k→ℕ) (endFit : address k base (k+1)<2^w)
    (precisionFits : precision≤w) (fit : ∀i,DescentWeightColumnRAM.Fits w base k (rows i))
    (depthFits : k<2^w) (bounded : ∀i,level i<2^w ∧ gain i<2^precision)
    (headers : ∀i,m (rows i).depth=(level i:Word w) ∧ m (rows i).factor=(gain i:Word w))
    (tables : ∀i (j : Fin (2^k)),m ((rows i).correlation+j.val)=(corr i (vec j):Word w)) :
    let cpu := fun l=>DescentWeightColumnRAM.pass k w (address k base l) l precision rows
    let ticks := fun l=>4+2^k*(2*(DescentWeightColumnRAM.vector k w (address k base l) l precision rows).binds+4)
    let val := fun l (j : Fin (2^k))=>(DescentWeightColumnRAM.money l level gain corr (vec j):Word w)
    (code w k base cpu (k+1)).Exec m (accumulated k base val m (k+1)) (cost ticks (k+1)) ∧
      ∀l : Fin (k+1),∀j : Fin (2^k),accumulated k base val m (k+1) (address k base l.val+j.val)=val l.val j := by
  refine ⟨execute k base _ _ _ m _ (by unfold address at endFit;omega) ?_,fun l=>read k base _ m _ _ l.isLt⟩
  intro l hl mem old
  have reach := Nat.mul_le_mul_right (2^k) (show l+1≤k+1 by omega)
  rw [Nat.succ_mul] at reach
  have start : base≤address k base l := Nat.le_add_right ..
  intro programs registers slots
  exact @DescentWeightColumnRAM.run w k N (address k base l) l precision mem rows level gain corr (by unfold address at *;omega)
    (by omega) precisionFits (fun i=>⟨⟨(fit i).table.1,(fit i).table.2.1,(fit i).table.2.2.trans start⟩,
      (fit i).depth.trans_le start,(fit i).factor.trans_le start⟩) bounded
    (fun i=>⟨(old _ (fit i).depth).trans (headers i).1,(old _ (fit i).factor).trans (headers i).2⟩)
    (fun i j=>(old _ (by have bound := (fit i).table.2.2;change (rows i).correlation+2^k≤base at bound;omega)).trans (tables i j)) programs registers slots

end
end Hierarchy.DescentNativeColumns

end OAI
