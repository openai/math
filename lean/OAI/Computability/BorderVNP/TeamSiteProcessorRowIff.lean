import OAI.Computability.BorderVNP.TeamSiteProcessorRowSupply
import OAI.Computability.BorderVNP.TeamSiteProcessorRowReadout

/-! # Native certificates for the complete signed physical processor

At a clock covering the measured row costs, an actual accepting leaf has exactly the
native bit spelling and weight. The unmasked physical consistency check also certifies
zero-weight native paths, after validating every proposed handoff and sorting bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape TeamSiteEvents TeamContraction.Replay

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}
variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

/-- Every accepting leaf of the signed raw input is exactly a native guarded row
with the supplied incident frame, consistent memory records and the same sign. -/
theorem Context.row_iff (fuel clock : ℕ)
    (bound : ∀ j vs, vs.length ≤ X.cap.val → (lib j).bounded fuel (vs : List (Word w)))
    (time : ∀ es out, EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out →
      X.cost (nativeCost w m g fuel es) es ≤ clock) (bits : List Bool) (negativeBit : Bool) :
    (bits,negativeBit) ∈ leaves (code P lib) negative clock start (StackCompiler.labeledInput Layout.input X.raw) ↔
      X.certified fuel bits (some negativeBit) :=
  X.leaf_iff_of_models (envelope := fun es => X.cost (nativeCost w m g fuel es) es) (X.forward fuel)
    (X.supply fuel bound) time bits negativeBit

/-- The terminal consistency witness includes paths whose private sign is zero.
It always reaches the actual unmasked successful sorter row. -/
theorem Context.checked_row_iff (fuel clock : ℕ)
    (bound : ∀ j vs, vs.length ≤ X.cap.val → (lib j).bounded fuel (vs : List (Word w)))
    (time : ∀ es out, EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out →
      X.cost (nativeCost w m g fuel es) es ≤ clock) (bits : List Bool) (sg : Option Bool) :
    X.checkedRun clock bits sg ↔ X.certified fuel bits sg :=
  X.checked_iff_of_models (envelope := fun es => X.cost (nativeCost w m g fuel es) es) (X.forward fuel)
    (X.supply fuel bound) time bits sg

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
