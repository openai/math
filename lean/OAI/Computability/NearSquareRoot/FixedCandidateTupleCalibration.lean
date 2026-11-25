import OAI.Computability.NearSquareRoot.FixedCandidateTuples
import OAI.Computability.NearSquareRoot.ScheduleArithmeticClocks

/-! # Calibration witnesses for a computable enumeration of physical candidates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open Filter FixedLayer

/-- Every code parameter can be included in the enumeration, even for tuple
types with dependent numerical encodings. Illegal encodings use a fixed default. -/
def decodeParameter (P : Type) [Primcodable P] [Inhabited P] (n : ℕ) : P :=
  (Encodable.decode n).getD default

theorem decodeParameter_primrec (P : Type) [Primcodable P] [Inhabited P] : Primrec (decodeParameter P) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const _)

theorem decodeParameter_surjective (P : Type) [Primcodable P] [Inhabited P] :
    Function.Surjective (decodeParameter P) := fun p => ⟨Encodable.encode p,by simp [decodeParameter]⟩

/-- Proofs choose a good tuple separately for each reciprocal exponent. The
encoder used to run the programs enumerates every tuple in advance and need
not decide which resource estimates are good. -/
theorem calibrated_of_row_guesses {P : Type} (enum : ℕ → P) (surj : Function.Surjective enum)
    (routeTick rowTick arena : P → ℕ → ℕ)
    (good : ∀ j : ℕ, ∃ p : P, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (1:ℝ)/2+1/(j+2:ℝ) ∧
      (∃ L : ℕ, ∀ᶠ n in atTop, arena p n ≤ L*(n+1)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (routeTick p n : ℝ) ≤ C*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))) ∧
      RowClock ρ (rowTick p)) :
    Calibrated (fun i => clockAt (rowClocks (routeTick (enum i)) (rowTick (enum i))) (arena (enum i)))
      (fun i => arenaAt (arena (enum i))) := by
  intro j
  obtain ⟨p,ρ,hr,hγ,ha,hroute,hrow⟩ := good j
  obtain ⟨D,hD⟩ := (rowClocks_good hr hγ ha hroute hrow).1
  obtain ⟨C,hC,ht⟩ := (rowClocks_good hr hγ ha hroute hrow).2
  obtain ⟨i,rfl⟩ := surj p
  exact ⟨i,C,D,hC.le,ht,hD⟩

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
