import OAI.Computability.BorderVNP.DiagonalNativeOwnedProduct

/-! # Evaluation with the actual typed cell translator

The generator in the private routine slot is arbitrary here. Its physical packed-row
contract supplies a genuine bounded private execution for each owned cell. This
allows the evaluator to run the concrete typed translator over delivered packet bytes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator

variable {w : ℕ}

/-- The local cell inputs and the argument words of an installed finite private generator.
The verified generator produces the sparse statement on the exact fetched bytes. -/
structure GeneratedCells (gen : Fragment IO) (n : ℕ) (pub : Arg → Word w) (m : Memory w) where
  /-- The finite sparse input at each actual row of the native directory. -/
  cell : ℕ → CellInput
  /-- Typed payload bits serialized at the actual burst location. -/
  payload : ℕ → List Bool
  /-- The fitted true burst, canonical bytes and private generator execution. -/
  packed : PackedRows (Frame.ofMemory pub m) m gen n payload (fun i => (cell i).stmt.expand [])

/-- The product of all independent private choices on the team's owned rows. -/
noncomputable def GeneratedCells.product {gen : Fragment IO} {n : ℕ} {pub : Arg → Word w} {m : Memory w}
    (C : GeneratedCells gen n pub m) : ℤ :=
  let f := Frame.ofMemory pub m
  ((f.ownedRows m 0 f.count).map (fun i => (C.cell i).weight)).prod

/-- Product formula from the native private machine's true row-generation runs. -/
theorem GeneratedCells.histories {gen : Fragment IO} {n : ℕ} {pub : Arg → Word w} {m : Memory w}
    (C : GeneratedCells gen n pub m) :
    (∑ es ∈ (Frame.ofMemory pub m).histories pub m (choices gen n), pathWeight es) = C.product := by
  unfold pathWeight
  rw [sum_directory pub gen n C.packed]
  unfold product
  congr 1
  apply List.map_congr_left
  intro i _
  exact value_external_directory ..

variable (pub : Arg → Word w) (routines : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (gen : Fragment IO) (n : ℕ) (epochs groups arguments occurrences : Code)

local notation "mac" => install gen n routines

/-- The native evaluator sum with the physically installed private machine, including
the concrete translator that reads compressed typed cell packets. The sparse product
counts only choices that its actual bounded native runs admit. -/
theorem evaluate_packed_product {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub mac s m)
    (hd : occurrences.deterministic = true) (hf : (pub 0).val+15 < 2^w)
    (room : ∀ (b : Fin k → Bool) (p : Returns (prepareExpansion epochs groups arguments) pub mac
      (pins b).val.2.1 (pins b).val.2.2),
      let f := Frame.ofMemory pub p.val.2.2
      f.base+3*f.count ≤ 2^w)
    (C : ∀ (b : Fin k → Bool) (p : Returns (prepareExpansion epochs groups arguments) pub mac
      (pins b).val.2.1 (pins b).val.2.2), GeneratedCells gen n pub p.val.2.2)
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
  rw [expansion_signed_sum pub mac _ _ epochs groups arguments occurrences hd (choices gen n)
    (mem_choices gen n routines) hf (room b)]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only
  rw [(C b p).histories]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
