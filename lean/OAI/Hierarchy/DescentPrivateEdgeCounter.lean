import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Count absorbed width from the actual raw endpoint columns -/

namespace Hierarchy.DescentPrivateEdgeCounter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorScan DescriptorExpr
open ProtocolRAM
open scoped Fin.CommRing

structure Banks where
  leftID : Bank
  rightID : Bank
  width : Bank
  oldTotal : ℕ
  flags : ℕ
  starts : ℕ
  out : ℕ

def cell (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)

theorem cell_read {w : ℕ} (a : ℕ) (m : Memory w) (row : Word w) :
    (cell a).eval m row=m a := by simp [cell,Expr.eval,Bank.read,Bank.size]

def weighted (S : Banks) : Expr :=
  .branch .eq (.lookup S.leftID .row) (.lookup S.rightID .row) (.lookup S.width .row) (.lit 0)

def plus (S : Banks) (n : ℕ) : Expr := .op .add (cell S.oldTotal) (cell (S.starts+n))

def program (S : Banks) (w n : ℕ) :=
  ((scan w S.flags n (weighted S)).seq (ProtocolRAMEndpointPrefix.exclusive w S.flags S.starts n)).seq
    (scan w S.out 1 (plus S n))

structure Room (S : Banks) (w n : ℕ) : Prop where
  src : S.leftID.Fits w S.flags
  dst : S.rightID.Fits w S.flags
  widths : S.width.Fits w S.flags
  held : S.oldTotal<S.flags
  flagsFit : S.flags+n≤S.starts
  sumFit : S.starts+n+1≤S.out
  finish : S.out+1<2^w

/-- The two names are the final coalescence owners of the same physical edge.
A padded row has width zero and can use either endpoint convention. -/
structure Loaded {w n : ℕ} (S : Banks) (m : Memory w) (internal : Fin n→Prop)
    (width : Fin n→ℕ) : Prop where
  internal_iff : ∀i, S.leftID.read m (i.val:Word w)=S.rightID.read m (i.val:Word w) ↔ internal i
  bits : ∀i, S.width.read m (i.val:Word w)=(width i:Word w)

variable {w n : ℕ}
def total (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ) (t : ℕ) :=
  ∑ j∈Finset.range t, if hj : j<n then if internal ⟨j,hj⟩ then width ⟨j,hj⟩ else 0 else 0

theorem total_rows (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ) :
    total internal width n=∑i,if internal i then width i else 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

def summed (S : Banks) (m : Memory w) (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ) :=
  ProtocolRAMEndpointPrefix.image S.starts (total internal width) (ProtocolRAM.image S.flags n (weighted S) m) n

def result (S : Banks) (m : Memory w) (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ) :=
  ProtocolRAM.image S.out 1 (plus S n) (summed S m internal width)

def cost (S : Banks) (n : ℕ) :=
  (4+n*(2*(weighted S).work+4)+(10+(3+12*n)))+(4+1*(2*(plus S n).work+4))

theorem cost_eq (S : Banks) (n : ℕ) : cost S n=51+62*n := by
  simp [cost,weighted,plus,cell,Expr.work]
  omega

theorem run (S : Banks) (m : Memory w) (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ)
    (space : Room S w n) (source : Loaded S m internal width) :
    (program S w n).Exec m (result S m internal width) (cost S n) := by
  let f:=ProtocolRAM.image S.flags n (weighted S) m
  have out:=space.finish
  have sep:=space.flagsFit
  have lower:=space.sumFit
  have old:=space.held
  have first : (scan w S.flags n (weighted S)).Exec m f (4+n*(2*(weighted S).work+4)) := scan_exec S.flags n (weighted S) m
    (show (weighted S).Fits w S.flags from ⟨⟨space.src,trivial⟩,⟨space.dst,trivial⟩,⟨space.widths,trivial⟩,trivial⟩) (by omega)
  have next : (ProtocolRAMEndpointPrefix.exclusive w S.flags S.starts n).Exec f (summed S m internal width)
      (10+(3+12*n)) := by
    apply ProtocolRAMEndpointPrefix.run
    · exact sep
    · omega
    · simp [total]
    · intro i hi
      have flag:=ProtocolRAMGeneratedWrite.read_image S.flags n (weighted S) m ⟨i,hi⟩
      rw [show f (S.flags+i)=(weighted S).eval m (i:Word w) from flag]
      simp only [total,Finset.sum_range_succ,dite_eq_left hi,Nat.cast_add]
      have owners:=source.internal_iff ⟨i,hi⟩
      have payload:=source.bits ⟨i,hi⟩
      by_cases inside : internal ⟨i,hi⟩
      · have eq:=owners.mpr inside
        simpa [weighted,Expr.eval,Comparison.test,eq,inside] using
          (congrArg (fun v : Word w=>(total internal width i:Word w)+v) payload.symm)
      · have neq:=fun h=>inside (owners.mp h)
        simp [weighted,Expr.eval,Comparison.test,inside]
        exact fun same=>False.elim (neq same)
  have cf (a : ℕ) (ha : a+1≤S.out) : (cell a).Fits w S.out :=
    ⟨⟨by simp [Bank.size],by simpa [Bank.size] using (show 1<2^w by omega),by simpa [Bank.size] using ha⟩,trivial⟩
  have finalStep : (scan w S.out 1 (plus S n)).Exec (summed S m internal width) (result S m internal width) (4+1*(2*(plus S n).work+4)) := scan_exec S.out 1 (plus S n) (summed S m internal width)
    (show (plus S n).Fits w S.out from ⟨cf _ (by omega),cf _ lower⟩) out
  intro P R C M pc reg pub exit rom advice cfg raw enter equal
  exact Procedure.Exec.then (Procedure.Exec.then first next) finalStep M pc reg pub exit rom advice cfg raw enter equal

theorem read (S : Banks) (m : Memory w) (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ)
    (space : Room S w n) : result S m internal width S.out =
      m S.oldTotal+(∑i,if internal i then width i else 0 : ℕ) := by
  have held:=space.held
  have sep:=space.flagsFit
  have v:=ProtocolRAMGeneratedWrite.read_image S.out 1 (plus S n) (summed S m internal width) (0:Fin 1)
  rw [show result S m internal width S.out=(plus S n).eval (summed S m internal width) 0 by simpa [result] using v]
  simp only [plus,Expr.eval,RowOp.opcode,BinaryOp.eval,cell_read]
  rw [summed,ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by omega)),
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl held),ProtocolRAMEndpointPrefix.read _ _ _ _ _ le_rfl,
    total_rows]

theorem frame (S : Banks) (m : Memory w) (internal : Fin n→Prop) [DecidablePred internal] (width : Fin n→ℕ)
    (space : Room S w n) (a : ℕ) (away : a<S.flags ∨ S.out+1≤a) :
    result S m internal width a=m a := by
  have h:=space.flagsFit
  have g:=space.sumFit
  rw [result,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega),summed,
    ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (by omega),ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)]

end Hierarchy.DescentPrivateEdgeCounter

end OAI
