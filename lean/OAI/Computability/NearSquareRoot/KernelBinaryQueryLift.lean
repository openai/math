import OAI.Computability.NearSquareRoot.KernelBinaryQuerySigns
import OAI.Computability.NearSquareRoot.KernelPassFactors

/-! # Binary query products on packed column pairs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery
open OAI.LinearAlgebra.FiniteFourier KernelPass KernelNormalization Matrix Finset SynchronizedPadding
noncomputable section

/-- Pairing the physical digit columns turns the tensor of the ordinary
normalized one-column transforms into the rational matrix of the fixed pass. -/
theorem lift_walsh (A h : ℕ) :
    lift h (walshColumn A) = (Plan.walshMatrix A h).map (algebraMap ℚ ℂ) := by
  ext y x
  change (∏ t : Fin h × Fin 2, ∏ a : Fin A, SynchronizedPair.walsh (y t.1 a t.2) (x t.1 a t.2)) =
    algebraMap ℚ ℂ (∏ i : Fin h, ∏ a : Fin A, pairEntry (y i a) (x i a))
  rw [Fintype.prod_prod_type, map_prod]
  apply prod_congr rfl
  intro i _
  rw [prod_comm, map_prod]
  apply prod_congr rfl
  intro j _
  exact (pairEntry_complex (y i j) (x i j)).symm

/-- The signs at the endpoints and the exchange of the two halves all use zero
recursive calls. The result supplies the two outer passes around a repaired
product on any number of independent rows. -/
theorem outer_passes (m u : ℕ) :
    ∃ front back : Plan (Arity m u) 1 1,
      front.calls = 0 ∧ back.calls = 0 ∧ Implements front (chirp m u) ∧
      Implements back (pushAddress (swapHalves m u) * chirp m u) := by
  obtain ⟨swap, hc, hi⟩ := reindex_linear (swapHalves m u)
  let sign := signPass (phaseBit (m:=m) (u:=u))
  have correct : Implements sign (chirp m u) := implements_sign phaseBit
  exact ⟨sign, swap.seq sign, rfl, by change swap.calls + 0 = 0; omega, correct, hi.seq correct⟩

/-- Composing the product with the two outer passes gives the full normalized
target on every paired-column width without increasing the child count. -/
theorem assemble {m u : ℕ} (hm : m ≡ 1 [MOD 2]) (p : Plan (Arity m u) 1 1)
    (hp : Implements p (List.ofFn (query (m:=m) (u:=u))).prod) :
    ∃ out : Plan (Arity m u) 1 1, out.calls = p.calls ∧ Implements out (walshColumn (Arity m u)) := by
  obtain ⟨front, back, h₁, h₂, a, b⟩ := outer_passes m u
  refine ⟨(back.seq p).seq front, ?_, ?_⟩
  · change back.calls+p.calls+front.calls = _
    omega
  · rw [recover (u:=u) hm]
    exact (b.seq hp).seq a

/-- Normalized full-width spectral intertwining in the rational physical bank. -/
theorem packed_diagonalizes {m u : ℕ} (h : ℕ) (j : Fin m) :
    (Plan.walshMatrix (Arity m u) h).map (algebraMap ℚ ℂ) * lift h (query (u:=u) j) =
      lift h (Matrix.diagonal fun ω => character (exponent j (halves m u ω))) *
      (Plan.walshMatrix (Arity m u) h).map (algebraMap ℚ ℂ) := by
  rw [← lift_walsh, ← lift_mul, diagonalizes, lift_mul]

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI
