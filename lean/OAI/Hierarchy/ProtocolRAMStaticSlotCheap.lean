import OAI.Hierarchy.ProtocolRAMStaticPorts
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Allowed word instructions for the fixed slot and lane multiplier -/

namespace Hierarchy.ProtocolRAMStaticPortCheap

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.DescriptorExpr
open ProtocolRAM

theorem scale (w bits k : ℕ) : admissible (ProtocolRAMPortScale.scale w bits k) := by
  induction bits generalizing k with
  | zero => exact ⟨trivial,trivial⟩
  | succ bits ih =>
    apply (admissible_let _ _).mpr
    refine ⟨ih _,?_⟩
    cases h : (k%2==1) <;> simp [ProtocolRAMPortScale.digit,admissible,opAllowed,allowed]

theorem base (w out n lanes : ℕ) (port : Expr) :
    CheapCode (ProtocolRAMStaticPorts.program w out n lanes port) := by
  apply writing_cheap
  exact (admissible_let _ _).mpr ⟨good_compile ..,(admissible_rename _ _).mpr (scale ..)⟩

end Hierarchy.ProtocolRAMStaticPortCheap

end OAI
