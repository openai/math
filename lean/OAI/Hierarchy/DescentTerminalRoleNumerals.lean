import OAI.Hierarchy.DescentTerminalRoleLookup

namespace OAI
/-! The original packed register and both scalar-lookup outputs at a native RAM row. -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {U : Type} {n A G p R N M wb slots : ℕ} (old : Codec U n)
local notation "sz" => width n A G p R
local notation "srcType" => Sources n A G p R N M
local notation "mux" => ∏j:Fin 6,2^(sz j*N*M)
def observed (s:Shelf) (m:Memory wb) (i:Word wb) : srcType := fun f=>((s.input f).read m i).val

theorem collect_node (x : srcType) : collect (node x)=x := by
  funext f
  simp only [collect,node,Equiv.apply_symm_apply]

/-- This is the exact doubly packed digit issued at the reached chronological node,
as in the actual retained/inserted scalar-book programs. -/
theorem observed_digit (s:Shelf) (m:Memory wb) (i:Word wb) (f:Fin 6) (g:Fin M) (v:Fin N) :
    (node (observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) s m i) g v f).val=
      digit (sz f) v.val (digit (sz f*N) g.val ((s.input f).read m i).val) := by
  let x:srcType:=observed s m i
  have group:=digit_encode ((encode (sz f*N) M).symm (x f)) g
  have member:=digit_encode ((encode (sz f) N).symm (((encode (sz f*N) M).symm (x f)) g)) v
  rw [Equiv.apply_symm_apply] at group member
  calc
    _ = digit (sz f) v.val (((encode (sz f*N) M).symm (x f)) g).val := member.symm
    _ = digit (sz f) v.val (digit (sz f*N) g.val (x f).val) := congrArg (digit (sz f) v.val) group.symm
    _ = _ := congrArg (digit (sz f) v.val) (digit_clip (sz f*N) ((s.input f).read m i).val g)

theorem observed_key (s:Shelf) (m:Memory wb) (i:Word wb)
    (radix:∀f,(s.shift f).bits=sz f*N*M)
    (shift:∀f,∀j:Fin (2^(sz f*N*M)),m ((s.shift f).base+j.val)=
      (scaleWords (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) f)[j]) :
    (sumExpr (term s) (List.finRange 6)).eval m i=
      ((finPiFinEquiv (observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) s m i)).val:Word wb) := by
  let x:srcType:=observed s m i
  let amount:=fun f:Fin 6=>(x f).val*scale (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) f
  have digits (f:Fin 6) : (term s f).eval m i=(amount f:Word wb) := by
    change m ((s.shift f).base+((s.input f).read m i).val%(s.shift f).size)=_
    simpa [Bank.size,radix,scaleWords,amount,x,observed,mul_comm] using shift f (x f)
  have index : ((List.finRange 6).map amount).sum=(finPiFinEquiv x).val := by
    rw [finPiFinEquiv_apply];change (List.ofFn amount).sum=_;rw [List.sum_ofFn];rfl
  rw [sum_read _ _ _ _ digits,index]

theorem observed_emit (s:Shelf) (m:Memory wb) (ready : Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) old s m) (i:Word wb) :
    (emit s).eval m i=((rolePanel old (observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) s m i)).val:Word wb) := by
  let x:srcType:=observed s m i
  have entry:=ready.dictionary (finPiFinEquiv x)
  have small:=(finPiFinEquiv x).isLt
  simp only [emit,Expr.eval,observed_key s m i ready.radix ready.shift,Bank.read,Fin.val_cast_of_lt (small.trans_le ready.key),
    Nat.mod_eq_of_lt (small.trans_le ready.slots),entry,menuWords,Fin.getElem_fin,Vector.getElem_ofFn,x]
  change ((rolePanel old (finPiFinEquiv.symm (finPiFinEquiv x))).val:Word wb)=_
  rw [Equiv.symm_apply_apply]

theorem count_eval (s:Shelf) (m:Memory wb)
    (ready:CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) slots s m) (i:Word wb) :
    (emit s).eval m i=((countPanel slots (observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) s m i)).val:Word wb) := by
  let x:srcType:=observed s m i
  have entry:=ready.table (finPiFinEquiv x)
  have small:=(finPiFinEquiv x).isLt
  simp only [emit,Expr.eval,observed_key s m i ready.radix ready.shift,Bank.read,Fin.val_cast_of_lt (small.trans_le ready.key),
    Nat.mod_eq_of_lt (small.trans_le ready.capacity),entry,countWords,Fin.getElem_fin,Vector.getElem_ofFn,x]
  change ((countPanel slots (finPiFinEquiv.symm (finPiFinEquiv x))).val:Word wb)=_
  rw [Equiv.symm_apply_apply]

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
