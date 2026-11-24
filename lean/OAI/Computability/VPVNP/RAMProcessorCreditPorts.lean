import OAI.Computability.VPVNP.RAMTapeCharges

/-!
# Ports for the private interpreter's call credits and probe timestamps

The public unary tallies are copied anew for each call. The global cap and
remaining allowance stay binary. The saved start cost and the ordinal are
the two per-call words needed for a chronological probe record.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CallCredit

open BurstRAM

/-- Stack names for public and remaining credits, the binary global cap, probe timestamps and
scratch space for copying and arithmetic. -/
inductive Port where
  | budget (p : Charges.Port)
  | publicH | publicFuel | globalCap | savedStart | ordinal
  | copyA | copyB | arithA | arithB
  deriving DecidableEq, Fintype

/-- The six-port charge routine is installed at the budget ports. -/
theorem budget_injective : Function.Injective Port.budget := fun _ _ => Port.budget.inj

/-- Encode the current credit state in its stacks, with unary public allowances, binary cap and
the saved start and ordinal bit strings. -/
def bank {w : ℕ} (H fuelCap fuel call site : ℕ) (cap g c : Word w)
    (saved ordinal : List Bool) : Stacks Port
  | .budget p => Charges.bank fuel call site g c p
  | .publicH => List.replicate H true
  | .publicFuel => List.replicate fuelCap true
  | .globalCap => wordBits cap
  | .savedStart => saved
  | .ordinal => ordinal
  | _ => []

/-- The charge routine affects only the six installed counters and scratch.
The public tallies, saved start and ordinal are kept in the caller's frame. -/
theorem install_budget_bank {w : ℕ} (H fuelCap fuel call site fuel' call' site' : ℕ)
    (cap g c g' c' : Word w) (saved ord : List Bool) :
    installStacks Port.budget (bank H fuelCap fuel call site cap g c saved ord)
      (Charges.bank fuel' call' site' g' c') =
      bank H fuelCap fuel' call' site' cap g' c' saved ord := by
  funext p
  cases p with
  | budget p => exact installStacks_at budget_injective ..
  | publicH | publicFuel | globalCap | savedStart | ordinal | copyA | copyB | arithA | arithB =>
    exact installStacks_outside _ _ (by simp)

end RAMTape.CallCredit

end VPVNP
end Computability
end OAI
