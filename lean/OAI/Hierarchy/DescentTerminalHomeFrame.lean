import OAI.Hierarchy.DescentTerminalHomeAny
import OAI.Hierarchy.DescentTerminalHomeAllocation

namespace OAI
/-! # Write support of the physical home counter on arbitrary input, including malformed shifts -/
namespace Hierarchy.DescentTerminalVertexFields.PrivateCounter
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A p groups blocks homes bw : ℕ} (C : Banks (blocks:=blocks))
set_option quotPrecheck false
local notation "capacity" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "starts" => (C.base+capacity)+homes
local notation "raw" => rawFinal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C

theorem rawFinal_frame (O : DescentPrivateExponentRAM.Banks) (m : Memory bw) (a : ℕ)
    (old : a < C.base ∨ starts+homes < a) (tmp : a≠O.usedBits) (dst : a≠O.deadBits) :
    raw O m a=m a := by
  unfold rawFinal
  rw [O.frame _ _ _ _ tmp dst,rawPrefix,ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (by omega),output,
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)]
  exact DescentStaticWordColumn.frame _ _ _ _ _ (by omega)

theorem rawFinal_low (header : ℕ) (m : Memory bw) (a : ℕ) (low : a < C.base) :
    raw (registers C header homes capacity) m a=m a := by
  apply rawFinal_frame C _ m a (.inl low) <;> dsimp [registers] <;> omega

end
end Hierarchy.DescentTerminalVertexFields.PrivateCounter

end OAI
