import OAI.Computability.VPVNP.SpectralLocalizationCone
import OAI.Computability.VPVNP.SpectralLocalizationRing

/-!
# Clearing spectral comparison in the tensor semiring

The denominators in Appendix A.1 are images of nonzero tensors, even if their
images in the group completion are zero divisors. Equality after localization
first supplies a multiplicative factor and then a common additive term. Both
are elements of the original semiring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

noncomputable section

/-- The multiplicative system in the ring of formal differences. For a tensor
semiring without zero divisors it is exactly the image of the nonzero tensors. -/
def denominators (S : Type*) [CommSemiring S] : Submonoid (G S) :=
  (nonZeroDivisors S).map toG.toMonoidHom

/-- Ring of formal differences localized at the images of the non-zero-divisors of the
semiring. -/
abbrev A (S : Type*) [CommSemiring S] := Localization (denominators S)

variable {S : Type*} [CommSemiring S]

/-- The canonical map to the ring in which every nonzero tensor is invertible. -/
def toA : S →+* A S := (algebraMap (G S) (A S)).comp toG

instance [Countable S] : Countable (A S) :=
  (IsLocalization.mk'_surjective (denominators S) (S := A S)).countable

variable [NoZeroDivisors S]

theorem toA_isUnit {s : S} (hs : s ≠ 0) : IsUnit (toA s) :=
  IsLocalization.map_units (M := denominators S) (A S)
    ⟨toG s, Submonoid.mem_map_of_mem toG.toMonoidHom (mem_nonZeroDivisors_of_ne_zero hs)⟩

instance [CharZero S] : Algebra ℚ (A S) :=
  ratAlgebraOfUnits _ fun n hn => by
    simpa only [map_natCast] using toA_isUnit (S := S) (Nat.cast_ne_zero.mpr hn)

/-- The inverse of the image of a nonzero tensor, chosen as the fraction with
numerator one. -/
def fractionInverse (s : S) (hs : s ≠ 0) : A S :=
  IsLocalization.mk' (A S) (1 : G S)
    (⟨toG s, Submonoid.mem_map_of_mem toG.toMonoidHom (mem_nonZeroDivisors_of_ne_zero hs)⟩ :
      denominators S)

theorem fraction_inverse_spec (s : S) (hs : s ≠ 0) :
    fractionInverse s hs * toA s = 1 := by
  unfold fractionInverse toA
  rw [RingHom.comp_apply]
  simpa only [map_one] using IsLocalization.mk'_spec (A S) (1 : G S)
    (⟨toG s, Submonoid.mem_map_of_mem toG.toMonoidHom (mem_nonZeroDivisors_of_ne_zero hs)⟩ :
      denominators S)

omit [NoZeroDivisors S] in
theorem one_add_ne_zero_of_rank (rank : S →+* ℕ) (s : S) : 1 + s ≠ 0 := by
  intro he
  have h := congrArg rank he
  simp only [map_add, map_one, map_zero] at h
  omega

variable [Nontrivial S]

/-- A localized element has one denominator and a difference of two original
semiring elements as numerator. -/
theorem exists_fraction (x : A S) :
    ∃ a b s : S, s ≠ 0 ∧ x * toA s = toA a - toA b := by
  obtain ⟨⟨g, ⟨m, hm⟩⟩, h⟩ := IsLocalization.surj (denominators S) x
  obtain ⟨s, hs, rfl⟩ : ∃ s : S, s ∈ nonZeroDivisors S ∧ toG s = m := hm
  obtain ⟨a,b,rfl⟩ := exists_sub g
  exact ⟨a,b,s, mem_nonZeroDivisors_iff_ne_zero.mp hs, by simpa only [toA, RingHom.comp_apply,
    map_sub] using h⟩

/-- Clearing an equality of images in the localized completion produces both
a common nonzero factor and a common summand in the original semiring. -/
theorem toA_eq_iff (a b : S) : toA a = toA b ↔
    ∃ c : S, c ≠ 0 ∧ ∃ w : S, c*a + w = c*b + w := by
  change algebraMap (G S) (A S) (toG a) = algebraMap (G S) (A S) (toG b) ↔ _
  rw [IsLocalization.eq_iff_exists (denominators S)]
  constructor
  · rintro ⟨⟨m, hm⟩, h⟩
    obtain ⟨c,hc,rfl⟩ : ∃ c : S, c ∈ nonZeroDivisors S ∧ toG c = m := hm
    refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp hc, (toG_eq_iff _ _).mp ?_⟩
    simpa only [map_mul] using h
  · rintro ⟨c,hc,w,hw⟩
    refine ⟨⟨toG c, Submonoid.mem_map_of_mem toG.toMonoidHom (mem_nonZeroDivisors_of_ne_zero hc)⟩, ?_⟩
    simpa only [map_mul] using (toG_eq_iff _ _).mpr ⟨w,hw⟩

variable [Preorder S]

/-- Membership of a difference in the order cone clears to a single
restriction with a multiplicative catalyst and a common additive term. -/
theorem clear_comparison (H : OrderBounds S) {x y : S}
    (h : FractionPositive toA (toA y - toA x)) :
    ∃ c : S, c ≠ 0 ∧ ∃ w : S, c*x+w ≤ c*y+w := by
  obtain ⟨a,b,s,hab,hs,h⟩ := h
  have he : toA (s*y + b) = toA (s*x + a) := by
    simp only [map_mul, map_add]
    linear_combination h
  obtain ⟨c,hc,w,hw⟩ := (toA_eq_iff _ _).mp he
  refine ⟨c*s, mul_ne_zero hc hs, c*b+w, ?_⟩
  calc
    _ = c*(s*x+b)+w := by ring
    _ ≤ c*(s*x+a)+w := H.add_mono (H.mul_mono c (H.add_mono (le_refl _) hab)) (le_refl _)
    _ = c*(s*y+b)+w := hw.symm
    _ = _ := by ring

variable [CharZero S]

theorem orderCone_bound (H : OrderBounds S) (x : A S) :
    ∃ n : ℕ, n • (1 : A S) + x ∈ orderCone toA H :=
  fractionPositive_bound toA H x (exists_fraction x)

theorem one_mem_orderCone (H : OrderBounds S) : (1 : A S) ∈ orderCone toA H :=
  fractionPositive_one toA H

/-- A monotone flattening rank excludes minus the unit from the order cone. -/
theorem neg_one_notMem_orderCone (H : OrderBounds S) (rank : S →+* ℕ)
    (hmono : Monotone rank) : (-1 : A S) ∉ orderCone toA H := by
  intro h
  have hp : FractionPositive toA (toA (0:S) - toA (1:S)) := by
    simpa only [map_zero, map_one, zero_sub, mem_orderCone] using h
  obtain ⟨c,hc,w,hw⟩ := clear_comparison H hp
  have hr := hmono hw
  have hrc := hmono (H.one_le hc)
  simp only [mul_zero, zero_add, mul_one, map_add, map_one] at hr hrc
  omega

/-- All tensor fractions, including the two multipliers in the extreme-state
argument, preserve the order cone. -/
theorem orderCone_mul_of_fraction (H : OrderBounds S) {x y : A S}
    (hx : x ∈ orderCone toA H) (t u : S) (hu : u ≠ 0) (hy : y * toA u = toA t) :
    y*x ∈ orderCone toA H :=
  fractionPositive_mul H hx t u hu hy

theorem orderCone_mul_tensor (H : OrderBounds S) (s : S) {x : A S}
    (hx : x ∈ orderCone toA H) : toA s * x ∈ orderCone toA H :=
  orderCone_mul_of_fraction H hx s 1 one_ne_zero (by simp)

theorem orderCone_mul_inv (H : OrderBounds S) (s : S) (hs : s ≠ 0) {x : A S}
    (hx : x ∈ orderCone toA H) : fractionInverse s hs * x ∈ orderCone toA H :=
  orderCone_mul_of_fraction H hx 1 s hs (by simpa using fraction_inverse_spec s hs)

end

end Spectral

end VPVNP
end Computability
end OAI
