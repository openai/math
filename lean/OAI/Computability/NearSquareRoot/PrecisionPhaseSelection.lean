import OAI.Computability.IntegerMultiplication.Brief.Signed

/-! # Tape selection from a table of generated local coefficients -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Carry

/-- Read one record from a finite table produced on the setup tapes. The index
may depend on the header. Both the list scan and unary index conversion are
charged to the original regime. -/
theorem selectTable {J X : Type} [Codec X] [Inhabited X] {r : Regime J} {n : J → ℕ}
    (entries : (j : J) → Fin (n j) → X)
    (built : r.Has (fun j ↦ List.ofFn (entries j)))
    (index : (j : J) → Fin (n j)) (known : Figure r (fun j ↦ (index j).val))
    (budget : Dom r.scale n) : r.Has (fun j ↦ entries j (index j)) := by
  have unary : Realizes r (fun j ↦ (index j).val) := known.pay (budget.mono (fun j ↦ (index j).isLt.le))
  have inputs : r.Has (fun j ↦ (List.ofFn (entries j), tally (index j).val)) :=
    Regime.Has.pair built unary
  have result := inputs.ez (Iter.facile (default : X))
  simpa only [Iter.entry] using result

/-- A six-entry Walsh pair table only requires the index in binary. -/
theorem selectSix {J X : Type} [Codec X] [Inhabited X] {r : Regime J}
    (entries : J → Fin 6 → X)
    (built : r.Has (fun j ↦ List.ofFn (entries j)))
    (index : J → Fin 6) (known : Figure r (fun j ↦ (index j).val)) :
    r.Has (fun j ↦ entries j (index j)) := selectTable entries built index known (.const _ 6)

/-- A fixed finite table of signed constants can be fetched with a binary
index. In particular this prepares the six eighth-root exponents of an idle
Walsh pair from its slot number. -/
theorem signedLookup {J : Type} {s : Regime J} {n : ℕ}
    (f : Fin n → ℤ) (index : J → Fin n) (known : Figure s (fun j ↦ (index j).val)) :
    Brief.Signed s (fun j ↦ f (index j)) := by
  let entry (i : Fin n) : Grid.S := (decide (f i < 0), Carry.born (f i).natAbs)
  have ready : s.Has (fun _ ↦ List.ofFn entry) := Regime.fixed _
  refine ⟨_, selectTable (fun _ ↦ entry) ready index known (.const _ n), fun j ↦ ?_⟩
  simp only [entry, Grid.whole, Carry.birthValue]
  by_cases hn : f (index j) < 0
  · simp [hn, Grid.tag, abs_of_neg hn]
  · simp [hn, Grid.tag, abs_of_nonneg (le_of_not_gt hn)]

end PhaseTable

end NearSquareRoot
end Computability
end OAI
