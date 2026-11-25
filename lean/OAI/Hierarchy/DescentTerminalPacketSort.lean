import OAI.Hierarchy.DescentTerminalStableSortRAM
import OAI.Hierarchy.DescentTerminalExteriorPackets
import OAI.Hierarchy.DescentTerminalPublicWordRAM

namespace OAI
/-! # End-to-end native publication of aggregate exterior rows after the basis remix -/
namespace Hierarchy.DescentTerminalExteriorPackets
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalPublicWordRAM DescentTerminalDenseGraphRead DescentTerminalDenseWindow Computability.BorderVNP.FragmentBucket
open scoped Classical Fin.CommRing
noncomputable section
variable {w n H Q p : ℕ} {P : Type} [Fintype P]

variable (H n : ℕ)

/-- Instantiate the existing seven physical row lookup columns with the
native inverse stable permutation and an identity index into the final flight.
All auxiliary columns read one fixed zero or a literal identity word. -/
theorem issued (T : Tapes) (outBase:ℕ) (m:Memory w) (keys:Fin n→Fin H)
    (raw:Fin n→Word (Q*p)) (rows:P≃Fin n×Fin Q) (outer:P→Fin p→Bool)
    (read:∀z k,Computability.VPVNP.RAMSerialization.wordBits (Q*p) (raw (rows z).1) (finProdFinEquiv ((rows z).2,k))=outer z k)
    (span:n<2^w) (perm:∀u:Fin n,T.portAt.read m (u.val:Word w)=(((dest keys).symm u).val:Word w))
    (zero:∀u:Fin n,T.lowAt.read m (u.val:Word w)=0)
    (slab:∀u:Fin n,T.slab.read m (u.val:Word w)=0)
    (base0:T.slabBase.read m 0=0)
    (hi:∀u:Fin n,T.high.read m (u.val:Word w)=(u.val:Word w))
    (ids:∀u:Fin n,T.highBase.read m (u.val:Word w)=(u.val:Word w))
    (source:∀i:Fin n,T.phase.read m (i.val:Word w)=((raw i).val:Word w)) (u:Fin n) :
    image outBase (n+2) (row T n) m (outBase+u.val) =
      ((dense (Q*p) (publicStream (code rows keys) outer) u.val).val:Word w) := by
  rw [dense_value rows keys outer raw read]
  have less:(u.val:Word w)<(n:Word w):=by
    simp [Fin.lt_def,Fin.val_cast_of_lt span,Fin.val_cast_of_lt (u.isLt.trans span),u.isLt]
  simp [image,fillSegment,show outBase+u.val<outBase+(n+2) by have:=u.isLt;omega,row,Expr.eval,DescriptorExpr.Comparison.test,
    RowOp.opcode,BinaryOp.eval,less,perm,zero,slab,base0,hi,ids,source]

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
