import OAI.Computability.BorderVNP.DiagonalTallyBits
import OAI.Computability.BorderVNP.DiagonalTallyRAMTotals
import OAI.Computability.BorderVNP.RoutingISANatural

/-!
# The tally stage of the common team evaluator

The frame at public argument zero supplies the ten words in slots 32–41. The
routine first accumulates its verified local record stream, then decodes the
common bit broadcast, verifies the team's row, and writes all global totals.
The same finite table runs at every width and on every team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

/-- Slots 32–35 give the local tally base, dimension, record base and record count. -/
def scatterSetup : Code := .block [
  readFrame 48 60 61 32, readFrame 49 60 61 33, readFrame 50 60 61 34,
  readFrame 52 60 61 35, .binary .add 51 52 52, .binary .add 51 50 51,
  .constant 63 1]

/-- Slots 36–38,40 give the input bit address, decoded base, team count, and bit width. -/
def packSetup : Code := .block [
  readFrame 50 60 61 36, readFrame 53 60 61 37, readFrame 51 60 61 38,
  readFrame 54 60 61 33, .binary .mul 51 51 54, readFrame 52 60 61 40, .constant 63 1]

/-- Compute the beginning of the current team's row using its public number in slot 39. -/
def verifySetup : Code := .block [
  readFrame 48 60 61 32, readFrame 49 60 61 33, readFrame 50 60 61 37,
  readFrame 54 60 61 39, .binary .mul 54 54 49, .binary .add 50 50 54,
  .binary .add 49 48 49, .constant 63 1]

/-- Start the column scan at coordinate zero. The final output bank is in slot 41. -/
def aggregateSetup : Code := .block [
  readFrame 49 60 61 33, readFrame 50 60 61 38, readFrame 58 60 61 41,
  readFrame 59 60 61 37, .constant 56 0, .constant 63 1]

/-- The complete fixed native subprogram for the two subtotal vectors. -/
def stage : Code := .block [
  scatterSetup, DiagonalTallyScatter.scatter, packSetup, DiagonalTallyBits.pack,
  verifySetup, verifyRow, aggregateSetup, aggregate]

/-- All tally instructions are deterministic. -/
theorem stage_deterministic : stage.deterministic = true := by decide

/-- Each successful path returns to its caller, where the Fourier reader can use the
computed coordinates. No internal instruction accepts early. -/
theorem stage_withoutAccept : stage.withoutAccept = true := by decide

/-- Distinct RAM histories never multiply the contribution of a valid subtotal row. -/
theorem stage_unique {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s t u : Bank w} {m mt mu : Memory w} {es fs}
    (a : Runs pub macros stage s m es t mt) (b : Runs pub macros stage s m fs u mu) :
    es = fs ∧ t = u ∧ mt = mu := a.unique_of_deterministic stage_deterministic b

/-- A run of the assembled table has exactly its recorded choice tape and trace. -/
theorem stage_execute_iff {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s t : Bank w} {m mt : Memory w} {es} (h : Runs pub macros stage s m es t mt)
    (bits : List (List Bool)) (fs : List (TeamRAM.Event w)) :
    TeamRAM.execute (stage.program.fetch pub macros) ⟨0,s⟩ m bits = some fs ↔
      fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  rw [Code.execute_iff_runs (c := stage) stage_withoutAccept]
  constructor
  · rintro ⟨⟨z,mz,run⟩,rfl⟩
    obtain ⟨rfl,_,_⟩ := stage_unique h run
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨t,mt,h⟩,rfl⟩

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
