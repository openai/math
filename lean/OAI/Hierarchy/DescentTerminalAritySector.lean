import OAI.Hierarchy.DescentTerminalRoleSector

namespace OAI
/-! # Issuing true flattened block-reference arities from the six reached primitive banks -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup DescentBundleHistory DescentKernelHistory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {U:Type} {n A G p R N M wb q H slots blocks shops:ℕ} (old:Codec U n)
local notation "rowFields" => fields (n:=n) (A:=A) (G:=G) (p:=p) (R:=R)
local notation "rowNode" => node (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M)
local notation "readSources" => observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M)
local notation "srcType" => Sources n A G p R N M
local notation "sz" => width n A G p R
local notation "cap" => DescentBundleTagKeys.capacity n A G p R
local notation "outBits" => Nat.clog 2 (slots+1)
local notation "dataAt" => measured (q:=q) (t:=cap) (H:=H) (N:=N) (A:=slots) (w:=p) (groups:=M)
local notation "mux" => ∏f:Fin 6,2^(sz f*N*M)

theorem count_shape {B:Type} {widthAt:B→ℕ} {r:BitRecipe U B widthAt} (hp:0<p) (shape:Shape p r)
    (u:r.Node) (x:Arrays n A G p R) (fit:(shape.recipe hp).arity u≤ slots)
    (given:Printed old (rowFields x) (r.tag u) (shape.sliceFields u)) :
    (localCount slots x).val=(shape.recipe hp).arity u := by
  have sum:tally (shape.sliceFields u)=(shape.recipe hp).arity u := by
    rw [Shape.recipe_refs]
    simp [tally,Shape.sliceFields,Slice.code,List.map_ofFn,List.sum_ofFn]
  have fitsWord:(shape.recipe hp).arity u<2^(Nat.clog 2 (slots+1)):=
    (Nat.lt_succ_of_le fit).trans_le (Nat.le_pow_clog (by decide) _)
  rw [localCount,ite_eq_right (by rw [given.primitive];omega),metadata_read old _ _ _ given,sum,Fin.val_cast_of_lt fitsWord]

theorem reached_arity {B:Type} {widthAt:B→ℕ} {r:BitRecipe U B widthAt} (hp:0<p) (shape:Shape p r) (u:r.Node)
    (writer:Shelf) (machine:MaskedShelf blocks) (before:Memory wb) (out:ℕ)
    (i:Fin shops) (b:Fin blocks) (g:Fin M) (slot:Fin N)
    (bounds:outBits*N*M≤wb) (hostRoom:shops≤2^wb) (fit:(shape.recipe hp).arity u≤ slots)
    (ready:CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) slots writer before)
    (atBase:(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).base=out+b.val*shops)
    (size:shops≤(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).size)
    (given:Printed old (rowFields (rowNode (readSources writer before ((finProdFinEquiv (b,i)).val:Computability.VPVNP.BurstRAM.Word wb)) g slot))
      (r.tag u) (shape.sliceFields u)) :
    venueField (cellAt (dataAt machine (image out (blocks*shops) (emit writer) before) i) (finProdFinEquiv (g,b))) (nodeArity slot)=
      (shape.recipe hp).arity u := by
  let addr:Computability.VPVNP.BurstRAM.Word wb:=(finProdFinEquiv (b,i)).val
  let x:srcType:=readSources writer before addr
  have stored:(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).read (image out (blocks*shops) (emit writer) before)
      (i.val:Computability.VPVNP.BurstRAM.Word wb)=((countPanel slots x).val:Computability.VPVNP.BurstRAM.Word wb) := by
    rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le hostRoom),Nat.mod_eq_of_lt (i.isLt.trans_le size),atBase]
    have ha:out+b.val*shops+i.val=out+(finProdFinEquiv (b,i)).val := by change _=out+(i.val+shops*b.val);ring
    rw [ha,DescentTerminalDenseHeaderRAM.at_image]
    exact count_eval writer before ready addr
  rw [venue_digit]
  change digit outBits slot.val ((cellAt (dataAt machine _ i) (finProdFinEquiv (g,b))) 6).val=_
  rw [cell_digit,measured_channel]
  change digit outBits slot.val (digit (N*outBits) g.val (_ % 2^(N*outBits*M)))=_
  rw [Nat.mul_comm N outBits,stored,Fin.val_cast_of_lt ((countPanel slots x).isLt.trans_le (Nat.pow_le_pow_right (by decide) bounds)),
    Nat.mod_eq_of_lt (countPanel slots x).isLt,countPanel,digit_encode,digit_encode]
  exact count_shape old hp shape u _ fit given

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
