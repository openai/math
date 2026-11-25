import OAI.Computability.NearSquareRoot.PhysicalWalshRectangleRouter
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStage

/-! # Jointly compiling the same supplied rectangle source at arbitrary position reserves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

noncomputable section

/-- The exponent is the first component. The other two digits are the literal low-
and high-end reserves of the selected rectangular position program. -/
abbrev RouteGuess := ℕ × ℕ × ℕ

def guessedRouter (rect : ℕ → Cmd) (z : RouteGuess) :=
  rectangleRouter z.2.1 z.2.2 (rect z.1)

theorem guessedRouter_effective {rect : ℕ → Cmd} (e : GeneratorSyntax.Effective ltr rect) :
    GeneratorSyntax.Effective ltr (guessedRouter rect) :=
  rectangleRouter_effective (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
    (e.comp Computable.fst)

theorem guessedRouter_within {rect : ℕ → Cmd} (R : ℕ) (bound : ∀ j, Within R (rect j)) :
    ∃ S, 0 < S ∧ ∀ z, Within S (guessedRouter rect z) := by
  obtain ⟨S,hS,reg⟩ := rectangleRouter_within R
  exact ⟨S,hS,fun z => reg _ _ _ (bound z.1)⟩

theorem guessedRouter_total {rect : ℕ → Cmd}
    (h : ∀ j, Controlled.Effective.rectContract (rect j) (Generator.midExponent j)) (z : RouteGuess) :
    PositionTotalAt (guessedRouter rect z) 0 :=
  rectangleRouter_total (rect := rect z.1) (ρ := Generator.midExponent z.1)
    (by unfold Generator.midExponent; positivity) (h z.1) z.2.1 z.2.2

/-- At each midpoint exponent the sufficiently large reserve guesses have the sharp
clock on every table. The rectangle source is supplied by the caller so that this
position pass and the recursive kernel use the identical native implementation. -/
theorem guessedRouter_runs {rect : ℕ → Cmd}
    (h : ∀ j, Controlled.Effective.rectContract (rect j) (Generator.midExponent j)) (j : ℕ) :
    ∃ d, ∀ a b, d ≤ a → d ≤ b →
      PositionRunsAt (guessedRouter rect (j,a,b)) (Generator.midExponent j) 0 :=
  rectangleRouter_runs (rect := rect j) (ρ := Generator.midExponent j)
    (by unfold Generator.midExponent; positivity) (h j)

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
