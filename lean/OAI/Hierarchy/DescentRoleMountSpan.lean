import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # The one terminal lookup-table installation before exterior replay -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM
structure RoleMount (w base roof : ℕ) where
  phase : NativePhase w
  run : ∀m,phase.Runs m
  frame : ∀m j,j< base ∨ roof≤ j→phase.image m j=m j
  placed : base≤ roof
end Hierarchy.DescentSixParty.Chronology

end OAI
