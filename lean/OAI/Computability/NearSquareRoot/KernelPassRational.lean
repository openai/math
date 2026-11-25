import OAI.Computability.NearSquareRoot.KernelPassFactors

/-! # Rational width matrices of a realized column operator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

noncomputable section

/-- Retract the standard inclusion of rational matrix entries into ℂ. -/
def rationalPart : ℂ → ℚ := Function.invFun (algebraMap ℚ ℂ)

theorem rationalPart_cast (q : ℚ) : rationalPart (algebraMap ℚ ℂ q) = q :=
  Function.leftInverse_invFun (algebraMap ℚ ℂ).injective q

def rationalLift {A : ℕ} (h : ℕ) (M : Local A) := (lift h M).map rationalPart

theorem Implements.oneRow_eq {A : ℕ} {p : Plan A 1 1} {M : Local A}
    (hp : Implements p M) (h : ℕ) : oneRow (p.eval h) = rationalLift h M := by
  ext y x
  change _ = rationalPart (lift h M y x)
  rw [← hp h, Matrix.map_apply, rationalPart_cast]

theorem Implements.product_eq {A : ℕ} {p q r : Plan A 1 1} {M N O T : Local A}
    (hp : Implements p M) (hq : Implements q N) (hr : Implements r O) (he : M*N*O = T)
    (h : ℕ) : oneRow (p.eval h) * oneRow (q.eval h) * oneRow (r.eval h) = rationalLift h T := by
  have H := (hp.seq hq).seq hr
  rw [he] at H
  simpa only [Plan.eval, oneRow_mul] using H.oneRow_eq h

end
end KernelPass

end NearSquareRoot
end Computability
end OAI
