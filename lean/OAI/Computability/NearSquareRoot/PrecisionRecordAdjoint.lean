import OAI.Computability.IntegerMultiplication.Star.Stroke
import OAI.Computability.NearSquareRoot.PhaseProgramRelease

/-! # Boolean-controlled conjugation of a fixed-point phase record

P192 uses the odd modulus `2^(w+1)-1` for each component. The signed lift
is symmetric, including the two extreme representable values. Consequently
conjugation can keep the existing width and introduces no rounding error.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Dusk Grid Star Strip
open ComplexConjugate

def adjointValue (b : Bool) (z : ℂ) : ℂ := bif b then conj z else z

def adjointGrain {w : ℕ} (b : Bool) (x : Grain w) : Grain w :=
  bif b then ⟨x.re,-x.im⟩ else x

private theorem lift_neg {w : ℕ} (x : day w) : Grid.lift (-x) = -Grid.lift x := by
  have h : abs (-Grid.lift x) < (2 : ℤ)^w := by simpa only [abs_neg] using lift_limit x
  simpa only [Int.cast_neg, lift_congr] using send_lift h

/-- The stored record represents the conjugate even at the extreme signed
values of either word. -/
theorem meaning_adjointGrain (p w : ℕ) (b : Bool) (x : Grain w) :
    meaning p w (adjointGrain b x) = adjointValue b (meaning p w x) := by
  cases b with
  | false => rfl
  | true =>
    simp [adjointGrain, adjointValue, meaning, aspect, toC, lift_neg, map_ofNat]

def adjointWord (i : Bool × Dusk.Pair) : Dusk.Pair :=
  bif i.1 then (i.2.1, shade i.2.2) else i.2

/-- Concrete fixed program on two encoded words and an orientation bit. -/
theorem adjointWord_easy : Easy adjointWord := by
  unfold adjointWord
  exact Grid.easy_bool _ _ _ Easy.fst (by have := shade_easy; fun_prop) Easy.snd

theorem adjointWord_mark {w : ℕ} (b : Bool) (x : Grain w) :
    adjointWord (b, mark x) = mark (adjointGrain b x) := by
  cases b <;> simp [adjointWord, adjointGrain, mark, shaded]

/-- Apply conjugation to any previously computed record, using the supplied
orientation flag on the setup stacks. -/
theorem computeAdjoint {I : Type} {s : Regime I} {b : I → Bool} {w : I → ℕ}
    {B : (i : I) → Grain (w i)} (hb : s.Has b) (hB : Satisfactory w s B) :
    Satisfactory w s (fun i => adjointGrain (b i) (B i)) := by
  have h : s.Has (fun i => (b i, mark (B i))) := hb.pair hB
  have t := Regime.Has.ez (f := adjointWord) h adjointWord_easy
  simpa only [Function.comp_def, adjointWord_mark] using t

/-- A uniform error estimate for forward entries also applies to the
conjugated entries, with exactly the same error constant. -/
theorem adjoint_error (p w : ℕ) (b : Bool) (x : Grain w) (z : ℂ) :
    ‖meaning p w (adjointGrain b x) - adjointValue b z‖ = ‖meaning p w x - z‖ := by
  rw [meaning_adjointGrain]
  cases b with
  | false => rfl
  | true => simp [adjointValue, ← map_sub]

end PhaseTable

end NearSquareRoot
end Computability
end OAI
