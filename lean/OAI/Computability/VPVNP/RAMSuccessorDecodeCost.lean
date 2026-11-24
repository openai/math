import OAI.Computability.VPVNP.RAMSortDecodeCost

/-!
# Word work to decode a successor message

The successor field of Lemma 10.1 comprises three control words and a five-word
record. The validator scans each word into a register once. It returns the parsed
successor together with a flag for equality with the canonical eight registers.
This separates parsing from rejection, including when the input is a clamped field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSerialization

open BurstRAM RAMSort

variable {w cap : ℕ}

private def scanFieldWord (b : Fin (8 * w) → Bool) (i : Fin 8) : Word w × ℕ :=
  scanWord fun j ↦ b (finProdFinEquiv (i, j))

private theorem scanFieldWord_value (b : Fin (8 * w) → Bool) (i : Fin 8) :
    (scanFieldWord b i).1 = (arrayBits 8 w).symm b i := by
  rw [scanFieldWord, scanWord_eq]
  apply (wordBits w).injective
  funext j
  rw [Equiv.apply_symm_apply, ← arrayBits_at, Equiv.apply_symm_apply]

/-- Each scan returns its word and operation count. The eight register writes are
charged once when saving the results. -/
private def scanEight (b : Fin (8 * w) → Bool) : (Fin 8 → Word w) × ℕ :=
  let f₀ := scanFieldWord b 0
  let f₁ := scanFieldWord b 1
  let f₂ := scanFieldWord b 2
  let f₃ := scanFieldWord b 3
  let f₄ := scanFieldWord b 4
  let f₅ := scanFieldWord b 5
  let f₆ := scanFieldWord b 6
  let f₇ := scanFieldWord b 7
  (![f₀.1, f₁.1, f₂.1, f₃.1, f₄.1, f₅.1, f₆.1, f₇.1],
    f₀.2 + f₁.2 + f₂.2 + f₃.2 + f₄.2 + f₅.2 + f₆.2 + f₇.2 + 8)

private theorem scanEight_value (b : Fin (8 * w) → Bool) :
    (scanEight b).1 = (arrayBits 8 w).symm b := by
  funext i
  fin_cases i <;> apply scanFieldWord_value

private def checkEight (a c : Fin 8 → Word w) : Bool :=
  (List.finRange 8).all fun i ↦ decide (a i = c i)

private theorem checkEight_valid (a c : Fin 8 → Word w) :
    checkEight a c = true ↔ a = c := by
  simp [checkEight, funext_iff]

/-- Parse the saved control and record fields and compare with the canonical words.
Allow 24 operations for dispatch (status, cost cap and up to three record tags)
and copying the payload. Allow 24 for forming the canonical control and record
words. Comparing eight registers costs at most six operations per register
(loop test, advance, two loads, equality and branch) plus the final test.
Returning the successor and flag costs two more writes. -/
def scanSuccessor (hw : 2 ≤ w) (hc : cap < 2 ^ w) (b : Fin (8 * w) → Bool) :
    (Successor w cap × Bool) × ℕ :=
  let saved := scanEight b
  let f := successorFormat hw hc
  let parsed := f.parse saved.1
  ((parsed, checkEight saved.1 (f.words parsed)), saved.2 + 24 + 24 + (6 * 8 + 1) + 2)

theorem scanSuccessor_value (hw : 2 ≤ w) (hc : cap < 2 ^ w) (b : Fin (8 * w) → Bool) :
    (scanSuccessor hw hc b).1.1 = (successorFormat hw hc).parse ((arrayBits 8 w).symm b) := by
  simp only [scanSuccessor, scanEight_value]

theorem scanSuccessor_valid (hw : 2 ≤ w) (hc : cap < 2 ^ w) (b : Fin (8 * w) → Bool) :
    (scanSuccessor hw hc b).1.2 = true ↔
      b = (successorFormat hw hc).encode ((successorFormat hw hc).parse ((arrayBits 8 w).symm b)) := by
  simp only [scanSuccessor, scanEight_value, checkEight_valid, Format.encode]
  exact (arrayBits 8 w).symm_apply_eq

theorem scanSuccessor_cost (hw : 2 ≤ w) (hc : cap < 2 ^ w) (b : Fin (8 * w) → Bool) :
    (scanSuccessor hw hc b).2 ≤ 224 * (w + 1) := by
  simp only [scanSuccessor, scanEight, scanFieldWord, scanWord_steps]
  omega

end RAMSerialization

end VPVNP
end Computability
end OAI
