import OAI.Hierarchy.DescentTerminalRoleNumerals
import OAI.Hierarchy.DescentTerminalRoleShape
import OAI.Hierarchy.DescentTerminalRoleChannelRead

namespace OAI
/-! # Joining the six actual issued scalar strips, even when inactive native digits are unspecified -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup DescentBundleHistory DescentKernelHistory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {U:Type} {n A G p R N M wb q H slots blocks shops:ℕ} (old:Codec U n)
local notation "rowFields" => fields (n:=n) (A:=A) (G:=G) (p:=p) (R:=R)
local notation "rowNode" => node (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M)
local notation "readSources" => observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M)
local notation "sz" => width n A G p R
local notation "cap" => DescentBundleTagKeys.capacity n A G p R
local notation "outWidth" => output n A G p R
local notation "srcType" => Sources n A G p R N M
local notation "dataAt" => measured (q:=q) (t:=cap) (H:=H) (N:=N) (A:=slots) (w:=p) (groups:=M)

/-- The role consumed by the scalar key lookup is obtained by scanning the six banks.
Assumptions on inherited data are the active primitive/slice digits only. -/
theorem reached_role {B : Type} {widthAt : B→ℕ} {r : BitRecipe U B widthAt} (hp:0<p)
    (shape : Shape p r) (u:r.Node)
    (writer:Shelf) (machine:MaskedShelf blocks) (before:Memory wb) (out:ℕ)
    (i:Fin shops) (b:Fin blocks) (g:Fin M) (slot:Fin N)
    (bounds:outWidth*N*M≤wb) (hostRoom:shops≤2^wb)
    (ready:Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) old writer before)
    (atBase : (machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).base=out+b.val*shops)
    (size : shops≤(machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).size)
    (roleFit : old.fits (r.tag u)) (issued : Printed old (rowFields (rowNode (readSources writer before ((finProdFinEquiv (b,i)).val:Computability.VPVNP.BurstRAM.Word wb)) g slot))
      (r.tag u) (shape.sliceFields u)) :
    venueField (cellAt (dataAt machine (image out (blocks*shops) (emit writer) before) i) (finProdFinEquiv (g,b))) (nodeRole slot)=
      ((DescentBundleTagKeys.codec old A G p R).store ((shape.recipe hp).tag u)).val+1 := by
  let address:Computability.VPVNP.BurstRAM.Word wb:=(finProdFinEquiv (b,i)).val
  let src:srcType:=readSources writer before address
  have stored : (machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).read (image out (blocks*shops) (emit writer) before) (i.val:Computability.VPVNP.BurstRAM.Word wb)=
      ((rolePanel old (collect (rowNode src))).val:Computability.VPVNP.BurstRAM.Word wb) := by
    rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le hostRoom),Nat.mod_eq_of_lt (i.isLt.trans_le size),atBase]
    have addr : out+b.val*shops+i.val=out+(finProdFinEquiv (b,i)).val := by change _=out+(i.val+shops*b.val);ring
    rw [addr,DescentTerminalDenseHeaderRAM.at_image,collect_node]
    exact observed_emit old writer before ready address
  exact (role_channel old machine _ b i (rowNode src) bounds stored g slot).trans (shape_role hp shape u old _ roleFit issued)

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
