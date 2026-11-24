import OAI.Computability.VPVNP.SpectralLocalizationRational
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Tactic

/-!
# The rational cone used for strict spectral comparison

Appendix A.1 writes a positive element as a sum of differences over nonzero
tensor denominators. Addition can be done over a common tensor denominator,
so a single ordered difference suffices. The witnesses are kept in the
original semiring so they can later be used to recover a restriction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

/-- The order properties of restriction that enter the localization argument. -/
structure OrderBounds (S : Type*) [CommSemiring S] [Preorder S] : Prop where
  zero_le (a : S) : 0 ≤ a
  one_le {s : S} (hs : s ≠ 0) : 1 ≤ s
  bounded (a : S) : ∃ n : ℕ, a ≤ (n : S)
  add_mono {a b c d : S} : a ≤ b → c ≤ d → a + c ≤ b + d
  mul_mono (t : S) {a b : S} : a ≤ b → t * a ≤ t * b

variable {S A : Type*} [CommSemiring S] [Preorder S] [CommRing A]

/-- An ordered difference with a common nonzero denominator. -/
def FractionPositive (f : S →+* A) (x : A) : Prop :=
  ∃ a b s : S, b ≤ a ∧ s ≠ 0 ∧ x * f s = f a - f b

/-- Addition collects the two denominators and retains the numerator comparison. -/
theorem fractionPositive_add [NoZeroDivisors S] {f : S →+* A} (H : OrderBounds S) {x y : A}
    (hx : FractionPositive f x) (hy : FractionPositive f y) :
    FractionPositive f (x + y) := by
  obtain ⟨a,b,s,hab,hs,hx⟩ := hx
  obtain ⟨c,d,t,hcd,ht,hy⟩ := hy
  refine ⟨t*a+s*c, t*b+s*d, s*t, H.add_mono (H.mul_mono t hab) (H.mul_mono s hcd),
    mul_ne_zero hs ht, ?_⟩
  simp only [map_mul, map_add]
  linear_combination f t * hx + f s * hy

/-- Multiplication by a tensor fraction preserves the cone. -/
theorem fractionPositive_mul [NoZeroDivisors S] {f : S →+* A} (H : OrderBounds S) {x y : A}
    (hx : FractionPositive f x) (t u : S) (hu : u ≠ 0) (hy : y * f u = f t) :
    FractionPositive f (y * x) := by
  obtain ⟨a,b,s,hab,hs,hx⟩ := hx
  refine ⟨t*a, t*b, s*u, H.mul_mono t hab, mul_ne_zero hs hu, ?_⟩
  simp only [map_mul]
  calc
    _ = (y * f u) * (x * f s) := by ring
    _ = _ := by rw [hy, hx, mul_sub]

theorem fractionPositive_difference [Nontrivial S] {f : S →+* A} {a b : S} (hab : b ≤ a) :
    FractionPositive f (f a - f b) :=
  ⟨a, b, 1, hab, one_ne_zero, by simp⟩

theorem fractionPositive_one [Nontrivial S] (f : S →+* A) (H : OrderBounds S) :
    FractionPositive f 1 := by
  simpa using fractionPositive_difference (f := f) (H.zero_le 1)

theorem fractionPositive_bound (f : S →+* A) (H : OrderBounds S) (x : A)
    (hx : ∃ a b s : S, s ≠ 0 ∧ x * f s = f a - f b) :
    ∃ n : ℕ, FractionPositive f (n • (1 : A) + x) := by
  obtain ⟨a,b,s,hs,hx⟩ := hx
  obtain ⟨n,hn⟩ := H.bounded b
  have hn' : (n : S) ≤ (n : S)*s := by simpa using H.mul_mono (n : S) (H.one_le hs)
  refine ⟨n, (n : S)*s+a, b, s, ?_, hs, ?_⟩
  · exact (hn.trans hn').trans (by simpa using H.add_mono (le_refl ((n:S)*s)) (H.zero_le a))
  · simp only [nsmul_eq_mul, mul_one, map_add, map_mul, map_natCast, add_mul, hx]
    ring

variable [Nontrivial S] [NoZeroDivisors S] [CharZero S] [Algebra ℚ A]

/-- The order cone in the rational algebra. Positive rational multiples use
the positive denominator of the scalar and its nonnegative integer numerator. -/
def orderCone (f : S →+* A) (H : OrderBounds S) : PointedCone ℚ A where
  carrier := FractionPositive f
  zero_mem' := by
    change FractionPositive f 0
    simpa using fractionPositive_difference (f := f) (le_refl (0 : S))
  add_mem' := fractionPositive_add H
  smul_mem' q x hx := by
    obtain ⟨a,b,s,hab,hs,hx⟩ := hx
    let k := q.val.num.toNat
    have hden : (q.val.den : S) ≠ 0 := Nat.cast_ne_zero.mpr q.val.den_nz
    have hrat := den_mul_algebraMap_eq_num_toNat A q.val q.property
    refine ⟨(k:S)*a, (k:S)*b, (q.val.den:S)*s, H.mul_mono _ hab, mul_ne_zero hden hs, ?_⟩
    change (q.val • x) * _ = _
    simp only [Algebra.smul_def, map_mul, map_natCast]
    calc
      _ = ((q.val.den : A) * algebraMap ℚ A q.val) * (x * f s) := by ring
      _ = _ := by rw [hrat, hx, mul_sub]

@[simp] theorem mem_orderCone (f : S →+* A) (H : OrderBounds S) (x : A) :
    x ∈ orderCone f H ↔ FractionPositive f x := Iff.rfl

end Spectral

end VPVNP
end Computability
end OAI
