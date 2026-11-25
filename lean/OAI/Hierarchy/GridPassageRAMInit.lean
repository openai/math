import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Clearing the counter table before a rail-passage scan -/

namespace Hierarchy.GridPassageRAMInit
open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

def procedure (w base bins : ℕ) : PhysicalProcedure.Procedure w :=
  ProtocolRAM.scan w base bins (.lit 0)

def clear {w : ℕ} (base bins : ℕ) (m : Memory w) : Memory w :=
  ProtocolRAM.image base bins (.lit 0) m

theorem clear_in {w : ℕ} (base bins : ℕ) (m : Memory w)
    {i : ℕ} (hi : i<bins) : clear base bins m (base+i) = 0 := by
  apply Fin.ext
  simp [clear,ProtocolRAM.image,ProtocolRAM.Expr.eval,fillSegment,hi]

theorem clear_out {w : ℕ} (base bins : ℕ) (m : Memory w)
    {a : ℕ} (ha : a<base ∨ base+bins≤a) : clear base bins m a = m a := by
  have h : ¬(base≤a ∧ a<base+bins) := by omega
  simp [clear,ProtocolRAM.image,fillSegment,h]

theorem exec {w : ℕ} (base bins : ℕ) (m : Memory w) (room : base+bins<2^w) :
    (procedure w base bins).Exec m (clear base bins m) (4+bins*6) := by
  exact ProtocolRAM.scan_exec base bins (.lit 0) m trivial room

end Hierarchy.GridPassageRAMInit

end OAI
