import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved

/-! # Applying an issued prefix on the positive run that owns its first-stage state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA

/-- The issued local continuation has been built on a particular physical
ownership return. It may now be read on the original processor that reaches
that same public register bank, event sequence and memory. -/
structure RegisteredOriginalPrefix {w : ℕ}
    (active issued : (Arg → Word w) × List (TeamRAM.Event w) × Bank w × Memory w) (result : Prop) : Prop where
  /-- Read the prepared result on the named original prefix once the decoder
      has identified its complete return with the issued one. -/
  atSource : active=issued → result

end TeamContraction

end BorderVNP
end Computability
end OAI
