import OAI.Computability.BorderVNP.DiagonalNativeRouteWindow
import OAI.Computability.BorderVNP.DiagonalNativeSignedWindow

/-! # Phase charges on the actual signed evaluator after a positive common tag -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator
open BorderVNP.Cube BorderVNP.Cube.Tally

variable {dim box lanes selectors symbols w k : ℕ}
variable (id : TableEntry dim box lanes selectors symbols → ℕ)
variable (pub : Arg → Word w) (routines : TeamOpcode.Macros w 8) (gen : Fragment IO) (n : ℕ)
variable (s : Bank w) (m : Memory w)
variable (pins : (Fin k → Bool) ≃ Pins.Return pub (install gen n routines) s m)

local notation "mac" => install gen n routines
local notation "groups" => scheduleGroups dim (selectorWidth dim selectors lanes)
local notation "args" => signedInputs id (TeamRows.ownedGroups dim box lanes selectors symbols)

/-- Construct the residual window when the authenticating profile already includes the
charged startup and pins. This permits one measured bound for the initial geometry,
published directory, group scheduler and actual routing passes together. -/
def SignedStageWindow.ofJoinedCharges (used limit core beforeTicks argumentsCalls tallyTicks readerTicks : ℕ)
    (fits : core+beforeTicks+argumentsCalls+tallyTicks+readerTicks ≤ limit)
    (routeFit : ∀ b : Fin k → Bool,
      ∀ p : Returns (beforeRoute epochPlacement groups) pub mac (pins b).val.2.1 (pins b).val.2.2,
      ∀ z : Returns route pub mac p.val.2.1 p.val.2.2,
        used+traceCost (pins b).val.1+traceCost p.val.1+traceCost z.val.1 ≤ core+beforeTicks)
    (arguments : ∀ b : Fin k → Bool,
      ∀ p : Returns (beforeRoute epochPlacement groups) pub mac (pins b).val.2.1 (pins b).val.2.2,
      ∀ z : Returns route pub mac p.val.2.1 p.val.2.2,
      ∀ a : Returns args pub mac z.val.2.1 z.val.2.2,
        traceCost a.val.1+privateDirectoryTicks pub a.val.2.2 ≤ argumentsCalls)
    (tally : ∀ b (p : SignedPreps id pub routines gen n s m pins b)
      (c : Returns callOwnedCells pub mac p.val.2.1 p.val.2.2)
      (z : Returns (finishExpansion signedOccurrences) pub mac c.val.2.1 c.val.2.2),
        traceCost z.val.1 ≤ tallyTicks)
    (reader : ∀ b (x : SignedExpansions id pub routines gen n s m pins b)
      (z : Returns leadEntry pub mac x.val.2.1 x.val.2.2), traceCost z.val.1 ≤ readerTicks) :
    SignedStageWindow id pub routines gen n s m pins used limit where
  tallyTicks := tallyTicks
  readerTicks := readerTicks
  tally := tally
  reader := reader
  fitted := by
    intro b p
    obtain ⟨pre,z,a,output,measured⟩ := preparation_charges epochPlacement groups args p
    rw [output,measured]
    have hz := routeFit b pre z
    have ha := arguments b pre z a
    omega

/-- Construct the actual residual window from measured before-route, core, argument/call,
tally and reader allowances. Each dependent state is the output of the preceding native
code. A prepared prefix still contributes to the finite prefix domain when a later test fails. -/
def SignedStageWindow.ofCharges (used limit core beforeTicks argumentsCalls tallyTicks readerTicks : ℕ)
    (fits : core+beforeTicks+argumentsCalls+tallyTicks+readerTicks ≤ limit)
    (before : ∀ b : Fin k → Bool,
      ∀ p : Returns (beforeRoute epochPlacement groups) pub mac (pins b).val.2.1 (pins b).val.2.2,
        traceCost p.val.1 ≤ beforeTicks)
    (coreFit : ∀ b : Fin k → Bool,
      ∀ p : Returns (beforeRoute epochPlacement groups) pub mac (pins b).val.2.1 (pins b).val.2.2,
      ∀ z : Returns route pub mac p.val.2.1 p.val.2.2,
        used+traceCost (pins b).val.1+traceCost z.val.1 ≤ core)
    (arguments : ∀ b : Fin k → Bool,
      ∀ p : Returns (beforeRoute epochPlacement groups) pub mac (pins b).val.2.1 (pins b).val.2.2,
      ∀ z : Returns route pub mac p.val.2.1 p.val.2.2,
      ∀ a : Returns args pub mac z.val.2.1 z.val.2.2,
        traceCost a.val.1+privateDirectoryTicks pub a.val.2.2 ≤ argumentsCalls)
    (tally : ∀ b (p : SignedPreps id pub routines gen n s m pins b)
      (c : Returns callOwnedCells pub mac p.val.2.1 p.val.2.2)
      (z : Returns (finishExpansion signedOccurrences) pub mac c.val.2.1 c.val.2.2),
        traceCost z.val.1 ≤ tallyTicks)
    (reader : ∀ b (x : SignedExpansions id pub routines gen n s m pins b)
      (z : Returns leadEntry pub mac x.val.2.1 x.val.2.2), traceCost z.val.1 ≤ readerTicks) :
    SignedStageWindow id pub routines gen n s m pins used limit :=
  SignedStageWindow.ofJoinedCharges id pub routines gen n s m pins used limit core beforeTicks argumentsCalls tallyTicks readerTicks
    fits (fun b p z => by have hp := before b p; have hz := coreFit b p z; omega) arguments tally reader

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
