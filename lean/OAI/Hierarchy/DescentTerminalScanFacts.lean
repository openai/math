import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Native lookup and frame facts for an arbitrary terminal scan -/
namespace Hierarchy.DescentTerminalChipRuntime
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w : ℕ}

theorem bankMono {w a b : ℕ} {z : Bank} (fit : z.Fits w a) (h : a≤b) : z.Fits w b :=
  ⟨fit.1,fit.2.1,fit.2.2.trans h⟩

theorem image_at (mem : Memory w) (base n : ℕ) (e : Expr) (i : Fin n) :
    image base n e mem (base+i.val)=e.eval mem (i.val:Word w) := by
  simp [image,fillSegment,i.isLt,Nat.cast_add]
theorem image_low (mem : Memory w) (base n : ℕ) (e : Expr) {j : ℕ} (hj:j<base) :
    image base n e mem j=mem j := by simp [image,fillSegment,not_le.mpr hj]

end Hierarchy.DescentTerminalChipRuntime

end OAI
