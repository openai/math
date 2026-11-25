import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentTerminalCellFrames
import OAI.Hierarchy.DescentTerminalAritySector

namespace OAI
/-! # Reached role and arity fields in the final memory of the paired six-column scan -/
namespace Hierarchy.DescentTerminalRolePairFields
open DescentTerminalCombinedRole DescentTerminalVertexFields DescentSIMDLookup DescentBundleHistory DescentKernelHistory
open DescentEpochTagKeys DescentTerminalPrimitiveFrames
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {U B:Type} {n A G p R N groups wb q hid slots blocks shops:ℕ} {widthAt:B→ℕ} {r:BitRecipe U B widthAt}
    (old:Codec U n) (hp:0<p) (shape:Shape p r) (u:r.Node)
    (first second:Shelf) (out:ℕ) (machine:MaskedShelf blocks) (m:Memory wb)
local notation "rowFields" => fields (n:=n) (A:=A) (G:=G) (p:=p) (R:=R)
local notation "rowNode" => node (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups)
local notation "rows" => blocks*shops
local notation "cap" => DescentBundleTagKeys.capacity n A G p R
local notation "meas" => measured (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (w:=p) (groups:=groups) machine
local notation "finalMem" => memory first second out rows m
local notation "src" => observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups)
variable (fitRole:(emit first).Fits wb out) (fitCount:(emit second).Fits wb out) (limit:out+blocks*shops+blocks*shops<2^wb)
    (roles:Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old first m)
    (arity:CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) slots second m)
    (same:second.input=first.input)
    (fitsRole:output n A G p R*N*groups≤wb) (fitsCount:Nat.clog 2 (slots+1)*N*groups≤wb)
    (i:Fin shops) (b:Fin blocks) (g:Fin groups) (slot:Fin N)
local notation "bank" => fun f:Fin 8=>machine.channel (finProdFinEquiv (b,f.succ))
local notation "idx" => (finProdFinEquiv (b,i)).val
local notation "position" => finProdFinEquiv (g,b)
variable (roleBase:(machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).base=out+b.val*shops)
    (roleSize:shops≤(machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).size)
    (countBase:(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).base=out+blocks*shops+b.val*shops)
    (countSize:shops≤(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).size)
    (roleFit:old.fits (r.tag u)) (arityFit:(shape.recipe hp).arity u≤ slots)

private theorem paired_cheap (wb : ℕ) (first second : Shelf) (out countRows : ℕ) :
    CheapCode (paired (wb:=wb) first second out countRows) :=
  @cheap_seq wb (scan wb out countRows (emit first)) (scan wb (out+countRows) countRows (emit second))
    (@scan_cheap wb out countRows (emit first)) (@scan_cheap wb (out+countRows) countRows (emit second))

private theorem bank_read_at {bw : ℕ} (col : Bank) (left right : Memory bw) (j : ℕ)
    (fitsBus : j<2^bw) (fitsColumn : j<col.size) (sameWord : left (col.base+j) = right (col.base+j)) :
    col.read left (j : Computability.VPVNP.BurstRAM.Word bw) = col.read right (j : Computability.VPVNP.BurstRAM.Word bw) := by
  simpa only [Bank.read,Fin.val_cast_of_lt fitsBus,Nat.mod_eq_of_lt fitsColumn] using sameWord

include fitRole fitCount limit roles arity same fitsRole fitsCount roleBase roleSize countBase countSize roleFit arityFit in
theorem paired_fields (given:Printed old (rowFields (rowNode (src first m (idx:Computability.VPVNP.BurstRAM.Word wb)) g slot)) (r.tag u) (shape.sliceFields u)) :
    (paired (wb:=wb) first second out rows).Exec m finalMem (steps rows+steps rows) ∧
    CheapCode (paired (wb:=wb) first second out rows) ∧
    venueField (cellAt (meas finalMem i) position) (nodeRole slot)=
      ((DescentBundleTagKeys.codec old A G p R).store ((shape.recipe hp).tag u)).val+1 ∧
    venueField (cellAt (meas finalMem i) position) (nodeArity slot)=(shape.recipe hp).arity u ∧
    ∀j,j<out→finalMem j=m j := by
  have later: (emit second).Fits wb (out+rows):=ProtocolRAMGeneratedWrite.fits_mono (w:=wb) (a:=out) (b:=out+rows) (emit second) (Nat.le_add_right out rows) fitCount
  have pair:=both (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) (slots:=slots) old first second out rows m fitRole fitCount later limit roles arity same
  have hosts:shops≤blocks*shops:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have hroom:shops≤2^wb:=by omega
  have index:=i.isLt.trans_le hroom
  have address (a:ℕ):a+b.val*shops+i.val=a+idx := by
    change _=a+(i.val+shops*b.val)
    ring
  have observedSame:src second m (idx:Computability.VPVNP.BurstRAM.Word wb)=src first m (idx:Computability.VPVNP.BurstRAM.Word wb):=by
    funext f
    simp only [observed,same]
  have secondGiven:Printed old (rowFields (rowNode (src second m (idx:Computability.VPVNP.BurstRAM.Word wb)) g slot)) (r.tag u) (shape.sliceFields u):=by
    rw [observedSame]
    exact given
  have localRole:=reached_role (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) (q:=q) (H:=hid) (slots:=slots) old hp shape u first machine m out
    i b g slot fitsRole hroom roles roleBase roleSize roleFit given
  have localArity:=reached_arity (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) (q:=q) (H:=hid) old hp shape u second machine m (out+rows)
    i b g slot fitsCount hroom arityFit arity countBase countSize secondGiven
  let firstOnly:=image out rows (emit first) m
  let secondOnly:=image (out+rows) rows (emit second) m
  let row : Fin rows := finProdFinEquiv (b,i)
  have fieldsAt:=pair.2.2 row
  have firstRead := (DescentTerminalDenseHeaderRAM.at_image out (emit first) m row).trans
    (observed_emit old first m roles (row.val : Computability.VPVNP.BurstRAM.Word wb))
  have secondRead := (DescentTerminalDenseHeaderRAM.at_image (out+rows) (emit second) m row).trans
    (count_eval second m arity (row.val : Computability.VPVNP.BurstRAM.Word wb))
  have roleAddress : (bank 5).base+i.val = out+idx :=
    (congrArg (fun loc => loc+i.val) roleBase).trans (address out)
  have arityAddress : (bank 6).base+i.val = out+rows+idx :=
    (congrArg (fun loc => loc+i.val) countBase).trans (address (out+rows))
  have roleWord : finalMem (out+idx) = firstOnly (out+idx) :=
    fieldsAt.1.trans firstRead.symm
  have srcRow : src second m (row.val : Computability.VPVNP.BurstRAM.Word wb) =
      src first m (row.val : Computability.VPVNP.BurstRAM.Word wb) := observedSame
  have arityWord : finalMem (out+rows+idx) = secondOnly (out+rows+idx) := by
    rw [srcRow] at secondRead
    exact fieldsAt.2.trans secondRead.symm
  have bankRole := bank_read_at (bank 5) finalMem firstOnly i.val index (i.isLt.trans_le roleSize)
    ((congrArg finalMem roleAddress).trans (roleWord.trans (congrArg firstOnly roleAddress.symm)))
  have bankArity := bank_read_at (bank 6) finalMem secondOnly i.val index (i.isLt.trans_le countSize)
    ((congrArg finalMem arityAddress).trans (arityWord.trans (congrArg secondOnly arityAddress.symm)))
  have roleField := field_at (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (p:=p)
    machine firstOnly finalMem b i g (nodeRole slot) bankRole
  have arityField := field_at (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (p:=p)
    machine secondOnly finalMem b i g (nodeArity slot) bankArity
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact pair.1
  · exact @paired_cheap wb first second out rows
  · exact roleField.trans localRole
  · exact arityField.trans localArity
  · exact paired_below first second out rows m

end
end Hierarchy.DescentTerminalRolePairFields

end OAI
