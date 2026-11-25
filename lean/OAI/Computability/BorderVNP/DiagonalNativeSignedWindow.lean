import OAI.Computability.BorderVNP.DiagonalNativePhaseLimits
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags

/-! # The residual clock of the actual signed evaluator

Preparation, the physical cell directory, tally completion and the matrix reader
are charged on their own returned traces. Their finite enumerations therefore retain
the real private spellings after the startup and common-tag ticks have been spent.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator
open BorderVNP.Cube BorderVNP.Cube.Tally
open scoped BigOperators Classical
variable {w dim box lanes selectors symbols : ℕ}
variable (id : TableEntry dim box lanes selectors symbols → ℕ)
variable (pub : Arg → Word w) (routines : TeamOpcode.Macros w 8) (gen : Fragment IO) (n : ℕ)
variable (s : Bank w) (m : Memory w)
local notation "mac" => install gen n routines
local notation "groups" => scheduleGroups dim (selectorWidth dim selectors lanes)
local notation "args" => signedInputs id (TeamRows.ownedGroups dim box lanes selectors symbols)
local notation "prepare" => prepareExpansion epochPlacement groups args
local notation "expand" => expansionBody epochPlacement groups args signedOccurrences
local notation "finish" => finishExpansion signedOccurrences
variable {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub (install gen n routines) s m)
/-- Returning public and private-input preparation for one actual guessed column. -/
abbrev SignedPreps (b : Fin k → Bool) := Returns prepare pub mac (pins b).val.2.1 (pins b).val.2.2
local notation "preps" => SignedPreps id pub routines gen n s m pins
/-- Returning preparation, owned private cells and checked tally for one guessed column. -/
abbrev SignedExpansions (b : Fin k → Bool) := Returns expand pub mac (pins b).val.2.1 (pins b).val.2.2
local notation "expansions" => SignedExpansions id pub routines gen n s m pins

/-- Actual tick charges needed by the public preparation, the native cell calls, the occurrence
scan and the final reader. The cell charge is determined by its physical directory. -/
structure SignedStageWindow (used limit : ℕ) where
  /-- The physical allowance for all post-cell occurrence and tally scans. -/
  tallyTicks : ℕ
  /-- The physical allowance for the final team's reader, including its guard. -/
  readerTicks : ℕ
  /-- Startup and all ordinary and private phases fit the available logical clock. -/
  fitted : ∀ b (p : preps b), used+traceCost (pins b).val.1+traceCost p.val.1+
    privateDirectoryTicks pub p.val.2.2+tallyTicks+readerTicks ≤ limit
  /-- Charge of a returning actual tally stage on a true post-call image. -/
  tally : ∀ b (p : preps b) (c : Returns callOwnedCells pub mac p.val.2.1 p.val.2.2)
    (t : Returns finish pub mac c.val.2.1 c.val.2.2), traceCost t.val.1 ≤ tallyTicks
  /-- Charge of a returning actual lead/nonlead reader after the true expansion. -/
  reader : ∀ b (x : expansions b) (y : Returns leadEntry pub mac x.val.2.1 x.val.2.2),
    traceCost y.val.1 ≤ readerTicks

variable {used limit : ℕ} (A : SignedStageWindow id pub routines gen n s m pins used limit)

include A in
/-- The finite enumeration of true preparing prefixes includes those whose later checks reject. -/
theorem SignedStageWindow.preparationFinite (b : Fin k → Bool) : Finite (preps b) := by
  apply finiteReturns_of_within _ _ _ _ _ limit 0 1
  intro z
  have cost := A.fitted b z
  exact (z.property.nativeOnly_limits (signedPrepare_nativeOnly id)).mono (by omega) le_rfl le_rfl

/-- At the actual residual clock the signed evaluation program factors into the independently
guessed column, genuine packed owned cells and the checked residue reader. The bounded sum
itself supplies the finite indexing, without a global termination hypothesis on the program. -/
theorem signedBody_bounded_product (hn : 1 ≤ n) (burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst)
    (hf : (pub 0).val+15 < 2^w) (room : ∀ b (p : preps b), let f := Frame.ofMemory pub p.val.2.2
      f.base+3*f.count ≤ 2^w)
    (C : ∀ b (p : preps b), GeneratedCells gen n pub p.val.2.2) :
    let (b : Fin k → Bool) := @Fintype.ofFinite (preps b) (A.preparationFinite id pub routines gen n s m pins b)
    boundedValue (signedBody id) pub mac s m (limit-used) burst (n^25) =
      ∑ b : Fin k → Bool, ∑ p : preps b, pathWeight p.val.1 *
        ((C b p).product * tallyValue pub mac (cellBank pub mac p.val.2.1 p.val.2.2) p.val.2.2
          signedOccurrences signedOccurrences_deterministic) := by
  let (b : Fin k → Bool) := @Fintype.ofFinite (preps b) (A.preparationFinite id pub routines gen n s m pins b)
  have calls b (p : preps b) : Finite (Returns callOwnedCells pub mac p.val.2.1 p.val.2.2) :=
    Finite.of_equiv _ (cellHistoriesEquiv pub mac _ _ (mem_choices gen n routines) hf (room b p)).symm
  have tail b (p : preps b) (c : Returns callOwnedCells pub mac p.val.2.1 p.val.2.2) :
      Finite (Returns finish pub mac c.val.2.1 c.val.2.2) :=
    finiteReturns_of_within _ _ _ _ _ A.tallyTicks 0 1 fun z =>
      (z.property.nativeOnly_limits (by decide)).mono (A.tally b p c z) le_rfl le_rfl
  let (b : Fin k → Bool) := @Fintype.ofFinite (expansions b)
    (Finite.of_equiv _ (expansionReturnEquiv pub mac _ _ epochPlacement groups args signedOccurrences))
  let (b : Fin k → Bool) (x : expansions b) := @Fintype.ofFinite (Returns leadEntry pub mac x.val.2.1 x.val.2.2)
    (finiteReturns_of_within _ _ _ _ _ A.readerTicks 0 1 fun z =>
      (z.property.nativeOnly_limits (by decide)).mono (A.reader b x z) le_rfl le_rfl)
  let e := evaluateReturnEquiv pub mac epochPlacement groups args signedOccurrences s m pins
  let : Fintype (Returns (evaluate epochPlacement groups args signedOccurrences) pub mac s m) := Fintype.ofEquiv _ e
  have clock : 1 ≤ n^25 := Nat.one_le_pow _ _ hn
  have budget (z : Returns (signedBody id) pub mac s m) : Within (limit-used) burst (n^25) z.val.1 := by
    obtain ⟨⟨b,x,y⟩,rfl⟩ := e.surjective z
    change Within _ _ _ ((pins b).val.1 ++ (x.val.1 ++ y.val.1))
    have yr := (y.property.nativeOnly_limits (by decide)).mono (A.reader b x y) (Nat.zero_le burst) clock
    obtain ⟨⟨p,c,z⟩,rfl⟩ := (expansionReturnEquiv pub mac (pins b).val.2.1 (pins b).val.2.2
      epochPlacement groups args signedOccurrences).surjective x
    have pr := (p.property.nativeOnly_limits (signedPrepare_nativeOnly id)).mono le_rfl (Nat.zero_le burst) clock
    have cr := ((C b p).within routines hf (room b p) c).mono le_rfl cap le_rfl
    have zr := (z.property.nativeOnly_limits (by decide)).mono (A.tally b p c z) (Nat.zero_le burst) clock
    have pin := ((pins b).property.nativeOnly_limits (by decide)).mono le_rfl (Nat.zero_le burst) clock
    have fit := A.fitted b p
    exact (pin.append ((pr.append (cr.append zr)).append yr)).mono (by omega) le_rfl le_rfl
  exact (boundedValue_eq_sum (evaluate epochPlacement groups args signedOccurrences) pub mac s m (limit-used) burst (n^25) budget).trans (evaluate_packed_product pub routines s m gen n
    epochPlacement groups args signedOccurrences pins signedOccurrences_deterministic hf room C)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
