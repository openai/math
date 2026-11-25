import OAI.Computability.BorderVNP.DiagonalNativeExpansionValue

/-! # The full native evaluation sum in terms of owned sparse cells

Each fresh substituted index gives one initial pin preparation. Every subsequent
successful argument preparation determines the true cell directory in memory.
Its signed contribution is the owned sparse product times the checked tally
and matrix-entry continuation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator Pins
open scoped BigOperators Classical

variable {w d h n : ℕ}

/-- Actual sparse inputs for the private directory after argument materialization.
Each owned burst contains the canonical serialized statement and meets its two clocks. -/
structure PreparedCells (d h n : ℕ) (pub : Arg → Word w) (m : Memory w) where
  /-- Local sparse statement and boundary bits per physical row. -/
  cell : ℕ → CellInput
  /-- The burst's end address fits in the machine address space. -/
  span : ∀ i < (CellDispatch.Frame.ofMemory pub m).count,
    (m ((CellDispatch.Frame.ofMemory pub m).address i)).val = (CellDispatch.Frame.ofMemory pub m).team →
    (m ((CellDispatch.Frame.ofMemory pub m).address i+1)).val+(m ((CellDispatch.Frame.ofMemory pub m).address i+2)).val ≤ 2^w
  /-- The burst fits the team's square-root allowance. -/
  cap : ∀ i < (CellDispatch.Frame.ofMemory pub m).count,
    (m ((CellDispatch.Frame.ofMemory pub m).address i)).val = (CellDispatch.Frame.ofMemory pub m).team →
    (m ((CellDispatch.Frame.ofMemory pub m).address i+2)).val ≤ TeamScales.width n (1/2)
  /-- The actual words fetched by each owned call decode to the stated local sparse input. -/
  words : ∀ i < (CellDispatch.Frame.ofMemory pub m).count,
    (m ((CellDispatch.Frame.ofMemory pub m).address i)).val = (CellDispatch.Frame.ofMemory pub m).team →
    TeamRAM.previous m ((CellDispatch.Frame.ofMemory pub m).burst m i) = CompactFrame.pack w (serialized d (cell i).stmt)
  /-- The compiled cell statement fits the fixed generator's stack depth. -/
  depth : ∀ i < (CellDispatch.Frame.ofMemory pub m).count,
    (m ((CellDispatch.Frame.ofMemory pub m).address i)).val = (CellDispatch.Frame.ofMemory pub m).team →
    ((cell i).directory.program (cell i).privateWires).FitsDepth d h
  /-- The complete private tape generator and validator fit the allowed private steps. -/
  clock : ∀ i < (CellDispatch.Frame.ofMemory pub m).count,
    (m ((CellDispatch.Frame.ofMemory pub m).address i)).val = (CellDispatch.Frame.ofMemory pub m).team →
    2*(cell i).allowance w d ≤ n^25

/-- Integer product of the actual sparse directories' private signed sums on this team. -/
noncomputable def PreparedCells.product {pub : Arg → Word w} {m : Memory w} (C : PreparedCells d h n pub m) : ℤ :=
  let f := CellDispatch.Frame.ofMemory pub m
  ((f.ownedRows m 0 f.count).map (fun i => (C.cell i).weight)).prod

/-- The finite private native outcomes on the prepared physical argument banks have
the same signed sum as their exact sparse cell product. -/
theorem PreparedCells.histories {pub : Arg → Word w} {m : Memory w} (C : PreparedCells d h n pub m) (hw : 0 < w) :
    (∑ es ∈ (CellDispatch.Frame.ofMemory pub m).histories pub m (choices (generate d h) n), pathWeight es) = C.product :=
  sparse_directory_sum pub C.cell hw C.span C.cap C.words C.depth C.clock

variable (pub : Arg → Word w) (routines : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (d h n : ℕ) (epochs groups arguments occurrences : Code)

local notation "mac" => install (generate d h) n routines

/-- Exact end-to-end evaluation-branch sum. The local clocks and addressing hypotheses
concern the physical cell inputs, and no assertion about the final polynomial is needed. -/
theorem evaluate_owned_product {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub mac s m)
    (hd : occurrences.deterministic = true) (hw : 0 < w) (hf : (pub 0).val+15 < 2^w)
    (room : ∀ (b : Fin k → Bool) (p : Returns (prepareExpansion epochs groups arguments) pub mac
      (pins b).val.2.1 (pins b).val.2.2),
      let f := CellDispatch.Frame.ofMemory pub p.val.2.2
      f.base+3*f.count ≤ 2^w)
    (C : ∀ (b : Fin k → Bool) (p : Returns (prepareExpansion epochs groups arguments) pub mac
      (pins b).val.2.1 (pins b).val.2.2), PreparedCells d h n pub p.val.2.2)
    [Fintype (Returns (evaluate epochs groups arguments occurrences) pub mac s m)]
    [∀ b : Fin k → Bool, Fintype (Returns (prepareExpansion epochs groups arguments) pub mac (pins b).val.2.1 (pins b).val.2.2)]
    [∀ b : Fin k → Bool, Fintype (Returns (expansionBody epochs groups arguments occurrences) pub mac (pins b).val.2.1 (pins b).val.2.2)]
    [∀ (b : Fin k → Bool) (z : Returns (expansionBody epochs groups arguments occurrences) pub mac
      (pins b).val.2.1 (pins b).val.2.2), Fintype (Returns leadEntry pub mac z.val.2.1 z.val.2.2)] :
    (∑ z : Returns (evaluate epochs groups arguments occurrences) pub mac s m, pathWeight z.val.1) =
    ∑ b : Fin k → Bool, ∑ p : Returns (prepareExpansion epochs groups arguments) pub mac (pins b).val.2.1 (pins b).val.2.2,
      pathWeight p.val.1 * ((C b p).product * tallyValue pub mac
        (cellBank pub mac p.val.2.1 p.val.2.2) p.val.2.2 occurrences hd) := by
  rw [evaluate_sum pub mac epochs groups arguments occurrences s m pins]
  apply Finset.sum_congr rfl
  intro b _
  rw [expansion_signed_sum pub mac _ _ epochs groups arguments occurrences hd (choices (generate d h) n)
    (mem_choices (generate d h) n routines) hf (room b)]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only
  rw [(C b p).histories hw]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
