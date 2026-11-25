import OAI.Hierarchy.DescentTerminalRoleNumerals

namespace OAI
/-! # One pair of measured primitive-row outputs, with both results in the same RAM state -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup DescentBundleHistory
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {wb : ℕ}

private theorem before_eval (e:Expr) (a:ℕ) (m m':Memory wb) (i:Word wb)
    (low:e.Fits wb a) (same:∀j<a,m' j=m j) : e.eval m' i=e.eval m i := by
  induction e with
  | row=>rfl
  | lit=>rfl
  | lookup b idx ih=>
    change b.read m' (idx.eval m' i)=b.read m (idx.eval m i)
    rw [ih low.2]
    apply same
    have rem:=Nat.mod_lt (idx.eval m i).val low.1.1
    have bound:=low.1.2.2
    omega
  | op tag x y hx hy=>simp only [Expr.eval,hx low.1,hy low.2]
  | branch tag x y yes no hx hy hyes hno=>simp only [Expr.eval,hx low.1,hy low.2.1,hyes low.2.2.1,hno low.2.2.2]

def paired (first second:Shelf) (out rows:ℕ) :=
  (scan wb out rows (emit first)).seq (scan wb (out+rows) rows (emit second))
def memory (first second:Shelf) (out rows:ℕ) (m:Memory wb) :=
  image (out+rows) rows (emit second) (image out rows (emit first) m)

variable {U:Type} {n A G p R N M slots:ℕ} (old:Codec U n)
local notation "x" => observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M)

theorem both (first second:Shelf) (out rows:ℕ) (m:Memory wb)
    (r0:(emit first).Fits wb out) (r1:(emit second).Fits wb out) (r1':(emit second).Fits wb (out+rows))
    (limit:out+rows+rows<2^wb) (role:Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) old first m)
    (count:CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) slots second m)
    (same:second.input=first.input) :
    (paired (wb:=wb) first second out rows).Exec m (memory first second out rows m) (steps rows+steps rows) ∧
    CheapCode (paired (wb:=wb) first second out rows) ∧
    ∀i:Fin rows,let src:=x first m (i.val:Word wb)
      memory first second out rows m (out+i.val)=((rolePanel old src).val:Word wb) ∧
      memory first second out rows m (out+rows+i.val)=((countPanel slots src).val:Word wb) := by
  have alive:out+rows<2^wb:=by omega
  have one:=run first m out rows r0 alive
  have two:=run second (image out rows (emit first) m) (out+rows) rows r1' limit
  let a:=scan wb out rows (emit first)
  let b:=scan wb (out+rows) rows (emit second)
  refine ⟨@Procedure.Exec.then wb a b m (image out rows (emit first) m)
    (memory first second out rows m) (steps rows) (steps rows) one.1 two.1,
    @cheap_seq wb a b one.2 two.2,?_⟩
  intro i
  have ss:x second m (i.val:Word wb)=x first m (i.val:Word wb):=by funext f;simp only [observed,same]
  constructor
  · rw [memory,DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),DescentTerminalDenseHeaderRAM.at_image]
    exact observed_emit old first m role _
  · rw [memory,DescentTerminalDenseHeaderRAM.at_image,before_eval (emit second) out m _ _ r1
      (fun j hj=>DescentTerminalChipRuntime.image_low _ _ _ _ hj),count_eval second m count,ss]

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
