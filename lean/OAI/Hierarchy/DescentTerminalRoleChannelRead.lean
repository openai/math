import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalRoleLookup
import OAI.Hierarchy.DescentTerminalRecordFields

namespace OAI
/-! # Reading the role written to the measured terminal channel -/
namespace Hierarchy.DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing

theorem measured_channel {q t H N A w blocks groups shops wb : ℕ}
    (machine : MaskedShelf blocks) (m : Memory wb) (i : Fin shops) (b : Fin blocks) (f : Fin 8) :
    (measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) machine m i
      (finProdFinEquiv (b,f.succ))).val =
      ((machine.channel (finProdFinEquiv (b,f.succ))).read m (i.val : Word wb)).val %
        2^(familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) f * groups) := by
  change _ % 2^(channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
    (groups:=groups) (finProdFinEquiv (b,f.succ))) = _
  simp only [channelSize,Equiv.symm_apply_apply,primitiveSize,Fin.cases_succ]

end Hierarchy.DescentTerminalVertexFields

namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical Fin.CommRing
noncomputable section
variable {U:Type} {n A G p R N H slots q groups blocks wb shops : ℕ} (old:Codec U n)
local notation "roles" => DescentBundleTagKeys.capacity n A G p R
local notation "roleBits" => output n A G p R
local notation "dataAt" => measured (q:=q) (t:=roles) (H:=H) (N:=N) (A:=slots) (w:=p) (groups:=groups)

theorem role_channel (machine:MaskedShelf blocks) (m:Memory wb) (b:Fin blocks) (i:Fin shops)
    (x:Fin groups→Fin N→Arrays n A G p R) (room : roleBits*N*groups≤wb)
    (held : (machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).read m (i.val:Word wb)=((rolePanel old (collect x)).val:Word wb))
    (g:Fin groups) (u:Fin N) :
    venueField (cellAt (dataAt machine m i) (finProdFinEquiv (g,b))) (nodeRole u)=(localRole old (x g u)).val := by
  rw [venue_digit]
  change digit roleBits u.val ((cellAt (dataAt machine m i) (finProdFinEquiv (g,b))) 5).val=_
  rw [cell_digit,measured_channel]
  change digit roleBits u.val (digit (N*roleBits) g.val
    (((machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).read m (i.val:Word wb)).val%2^(N*roleBits*groups)))=_
  rw [held,Nat.mul_comm N roleBits,Fin.val_cast_of_lt ((rolePanel old (collect x)).isLt.trans_le (Nat.pow_le_pow_right (by decide) room)),
    Nat.mod_eq_of_lt (rolePanel old (collect x)).isLt,rolePanel_read]

/-- Family five is placed at the genuine block-major, host-minor interval of the
writer's one contiguous native scan. The next reader observes the actual written memory. -/
theorem output_channel (writer:Shelf) (machine:MaskedShelf blocks) (before:Memory wb) (out:ℕ) (b:Fin blocks) (i:Fin shops)
    (x:Fin groups→Fin N→Arrays n A G p R) (room : roleBits*N*groups≤wb)
    (ready:Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old writer before)
    (cols:∀j,(writer.input j).read before ((finProdFinEquiv (b,i)).val:Word wb)=((collect x j).val:Word wb))
    (atBase : (machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).base=out+b.val*shops)
    (size : shops≤(machine.channel (finProdFinEquiv (b,(5:Fin 8).succ))).size)
    (hostRoom : shops≤2^wb) (g:Fin groups) (u:Fin N) :
    venueField (cellAt (dataAt machine (image out (blocks*shops) (emit writer) before) i) (finProdFinEquiv (g,b))) (nodeRole u)=
      (localRole old (x g u)).val := by
  apply role_channel old machine _ b i x room _ g u
  rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le hostRoom),Nat.mod_eq_of_lt (i.isLt.trans_le size),atBase]
  have addr : out+b.val*shops+i.val=out+(finProdFinEquiv (b,i)).val := by
    change _=out+(i.val+shops*b.val);ring
  rw [addr,printed old writer before out (blocks*shops) _ ready x cols]

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
