import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalRolePairProgram

namespace OAI
/-! # Terminal field reads after the two native role and arity writes -/
namespace Hierarchy.DescentTerminalPrimitiveFrames
open DescentTerminalVertexFields DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {q t H N A p groups blocks shops wb:ℕ}
    (machine:MaskedShelf blocks) (before after:Memory wb) (b:Fin blocks) (i:Fin shops) (g:Fin groups)
local notation "dataAt" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)
local notation "whereAt" => finProdFinEquiv (g,b)
local notation "valAt" => fun m k=>venueField (cellAt (dataAt machine m i) whereAt) k
local notation "bank" => fun f:Fin 8=>machine.channel (finProdFinEquiv (b,f.succ))

theorem field_at (k:Key H N A) (readback:(bank (group k)).read after (i.val:Word wb)=(bank (group k)).read before (i.val:Word wb)) :
    valAt after k=valAt before k := by
  simp only [venue_digit,cell_digit,measured,Fin.val_natCast,readback]

open DescentTerminalCombinedRole
theorem paired_below (first second:Shelf) (out rows:ℕ) (m:Memory wb) (j:ℕ) (hj:j<out) :
    memory first second out rows m j=m j := by
  rw [memory,DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),DescentTerminalChipRuntime.image_low _ _ _ _ hj]

end
end Hierarchy.DescentTerminalPrimitiveFrames

end OAI
