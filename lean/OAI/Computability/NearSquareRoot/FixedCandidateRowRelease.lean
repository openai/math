import OAI.Computability.NearSquareRoot.FixedCandidateTupleCalibration
import OAI.Computability.NearSquareRoot.ScheduleArithmeticRelease

/-! # The independent tape-machine specification from physical array kernels -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate
open IntegerMultiplication Code DigitPacking FixedPoint FixedLayer Filter

/-- The four physical kernel families are valid at every tuple. Good tuples,
which may be chosen non-effectively for each requested exponent, control the
speed and visited cells of a single scheduled machine on all positive inputs. -/
theorem uniformMultiplicationSpec_of_row_guesses {P : Type} [Primcodable P] [Inhabited P]
    (K : P → ℕ) (hK : Computable K) (hN : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (hd : ∀ p (i : LargeInput (K p)), 4 ≤ (box i.val.width).length)
    (hk : ∀ p (i : LargeInput (K p)), 1024 ≤ addressBits i.val.width)
    (A routeTick rowTick : P → ℕ → ℕ) (ha : ∀ p n, n ≤ A p n)
    (lin : ∀ p (i : LargeInput (K p)), A p i.val.width ≤ rowTick p i.val.width)
    (hl : ∀ p (i : LargeInput (K p)), phaseClock i.val.width ≤ rowTick p i.val.width)
    (crt : EffectiveCRTAt K A routeTick (fun p i => route (hv p i)))
    (undo : EffectiveCRTAt K A routeTick (fun p i => afterInverseCRT (hv p i)))
    (perm : ∀ dir : Bool, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => dir) hd A rowTick .permutation)
    (walsh : ∀ dir : Bool, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => dir) hd A rowTick .walsh)
    (good : ∀ j : ℕ, ∃ p : P, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (1:ℝ)/2+1/(j+2:ℝ) ∧
      (∃ L : ℕ, ∀ᶠ n in atTop, A p n ≤ L*(n+1)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (routeTick p n : ℝ) ≤ C*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))) ∧
      RowClock ρ (rowTick p)) : UniformMultiplicationSpec := by
  let e := decodeParameter P
  obtain ⟨files⟩ := arenaFiles_of_rows e (decodeParameter_primrec P).to_comp K hK hN hv hd hk
    A routeTick rowTick ha lin hl crt undo perm walsh
  exact files.uniformMultiplicationSpec
    (calibrated_of_row_guesses e (decodeParameter_surjective P) routeTick rowTick A good)

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
