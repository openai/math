import Mathlib

/-! # Rationals with protected denominators

For a finite family of primes, the protected ring consists of the rationals
whose reduced denominator is coprime to every member. It contains the dyadic
rationals when all protected primes are odd. A maximal ideal is determined by
the characteristic of its residue field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Rational numbers with reduced denominator coprime to each member of `L`. -/
def protectedRationals (L : Finset ℕ) : Subring ℚ where
  carrier := {q | ∀ p ∈ L, p.Coprime q.den}
  zero_mem' _ _ := by simp
  one_mem' _ _ := by simp
  neg_mem' h p hp := by simpa using h p hp
  add_mem' {a b} ha hb p hp :=
    ((ha p hp).mul_right (hb p hp)).coprime_dvd_right (Rat.add_den_dvd a b)
  mul_mem' {a b} ha hb p hp :=
    ((ha p hp).mul_right (hb p hp)).coprime_dvd_right (Rat.mul_den_dvd a b)

variable {L : Finset ℕ}

@[simp] theorem mem_protectedRationals {q : ℚ} :
    q ∈ protectedRationals L ↔ ∀ p ∈ L, p.Coprime q.den := Iff.rfl

/-- Inverting any allowed nonzero denominator stays in the protected ring. -/
theorem inv_natCast_mem_protectedRationals {d : ℕ} (hd : d ≠ 0) (hc : ∀ p ∈ L, p.Coprime d) :
    (d : ℚ)⁻¹ ∈ protectedRationals L := by
  intro p hp
  simpa [Rat.den_inv_of_ne_zero (by exact_mod_cast hd : (d : ℚ) ≠ 0)] using hc p hp

theorem isUnit_natCast_protectedRationals {d : ℕ} (hd : d ≠ 0) (hc : ∀ p ∈ L, p.Coprime d) :
    IsUnit (d : protectedRationals L) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(d : ℚ)⁻¹, inv_natCast_mem_protectedRationals hd hc⟩, Subtype.ext ?_⟩
  change (d : ℚ) * (d : ℚ)⁻¹ = 1
  exact mul_inv_cancel₀ (by exact_mod_cast hd)

/-- The subring `ℤ[1/2]` of the rationals. -/
def dyadicRationals : Subring ℚ := Subring.closure {(2 : ℚ)⁻¹}

/-- All dyadic rationals are allowed when the protected integers are odd. -/
theorem dyadicRationals_le_protectedRationals (hodd : ∀ p ∈ L, Odd p) :
    dyadicRationals ≤ protectedRationals L := by
  apply Subring.closure_le.mpr
  apply Set.singleton_subset_iff.mpr
  exact inv_natCast_mem_protectedRationals (d := 2) (by decide)
    (fun p hp => Nat.coprime_two_right.mpr (hodd p hp))

/-- The integer numerator determines membership in a maximal ideal. -/
theorem mem_maximalIdeal_protectedRationals (M : MaximalSpectrum (protectedRationals L))
    (x : protectedRationals L) :
    x ∈ M.asIdeal ↔ (ringChar ((protectedRationals L) ⧸ M.asIdeal) : ℤ) ∣ (x : ℚ).num := by
  let K := protectedRationals L ⧸ M.asIdeal
  let : Field K := Ideal.Quotient.field _
  let π := Ideal.Quotient.mk M.asIdeal
  have he : x * ((x : ℚ).den : protectedRationals L) = ((x : ℚ).num : protectedRationals L) :=
    Subtype.ext (Rat.mul_den_eq_num x.val)
  have hden : (π ((x : ℚ).den : protectedRationals L)) ≠ 0 :=
    ((isUnit_natCast_protectedRationals (Rat.den_ne_zero _) x.property).map π).ne_zero
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← CharP.intCast_eq_zero_iff K, ← map_intCast π,
    ← he, map_mul, mul_eq_zero, or_iff_left hden]

/-- The residue characteristic is zero or one of the protected primes. -/
theorem residueChar_mem_protectedRationals (hL : ∀ p ∈ L, Nat.Prime p)
    (M : MaximalSpectrum (protectedRationals L)) :
    ringChar (protectedRationals L ⧸ M.asIdeal) ∈ insert 0 L := by
  let K := protectedRationals L ⧸ M.asIdeal
  let : Field K := Ideal.Quotient.field _
  let p := ringChar K
  change p ∈ insert 0 L
  rcases CharP.char_is_prime_or_zero K p with hprime | hp
  · apply Finset.mem_insert_of_mem
    by_contra h
    have hu : IsUnit (p : protectedRationals L) :=
      isUnit_natCast_protectedRationals hprime.ne_zero fun q hq =>
        (Nat.coprime_primes (hL q hq) hprime).mpr (fun he => h (he ▸ hq))
    have hz := (hu.map (Ideal.Quotient.mk M.asIdeal)).ne_zero
    apply hz
    simp [p, K]
  · simp [hp]

/-- Distinct maximal ideals have distinct residue characteristics. -/
theorem residueChar_injective_protectedRationals :
    Function.Injective (fun M : MaximalSpectrum (protectedRationals L) =>
      ringChar (protectedRationals L ⧸ M.asIdeal)) := by
  intro M N hc
  apply MaximalSpectrum.ext
  ext x
  exact (mem_maximalIdeal_protectedRationals M x).trans
    ((congrArg (fun i : ℕ => (i : ℤ) ∣ (x : ℚ).num) hc).to_iff.trans
      (mem_maximalIdeal_protectedRationals N x).symm)

/-- The protected ring has finitely many maximal ideals, including for empty `L`. -/
theorem finite_maximalSpectrum_protectedRationals (hL : ∀ p ∈ L, Nat.Prime p) :
    Finite (MaximalSpectrum (protectedRationals L)) := by
  let f : MaximalSpectrum (protectedRationals L) → ↥(insert 0 L) :=
    fun M => ⟨_, residueChar_mem_protectedRationals hL M⟩
  exact Finite.of_injective f (fun _ _ h => residueChar_injective_protectedRationals
    (congrArg Subtype.val h))

/-- Every protected prime occurs as the characteristic of a residue field. -/
theorem exists_maximal_protectedRationals {p : ℕ} (hp : Nat.Prime p) (hmem : p ∈ L) :
    ∃ M : MaximalSpectrum (protectedRationals L), ringChar (protectedRationals L ⧸ M.asIdeal) = p := by
  have hnu : ¬ IsUnit (p : protectedRationals L) := by
    rintro hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    have he : (y : ℚ) = (p : ℚ)⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hy)
    have hy' := y.property p hmem
    rw [he, Rat.den_inv_of_ne_zero (by exact_mod_cast hp.ne_zero)] at hy'
    exact hp.ne_one (Nat.coprime_self p |>.mp (by simpa using hy'))
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : protectedRationals L)})
    (mt Ideal.span_singleton_eq_top.mp hnu)
  refine ⟨⟨M, hM⟩, CharP.ringChar_of_prime_eq_zero hp ?_⟩
  have hh : (p : protectedRationals L) ∈ M := hle (Ideal.subset_span (Set.mem_singleton _))
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hh

/-- For a nonempty protected prime set, every residue field has protected characteristic. -/
theorem residueChar_mem_of_nonempty_protectedRationals (hL : ∀ p ∈ L, Nat.Prime p) (h₀ : L.Nonempty)
    (M : MaximalSpectrum (protectedRationals L)) : ringChar (protectedRationals L ⧸ M.asIdeal) ∈ L := by
  rcases Finset.mem_insert.mp (residueChar_mem_protectedRationals hL M) with hz | h
  · obtain ⟨p, hp⟩ := h₀
    obtain ⟨N, hN⟩ := exists_maximal_protectedRationals (hL _ hp) hp
    have he : M = N := MaximalSpectrum.ext (M.isMaximal.eq_of_le N.isMaximal.ne_top (by
      intro x hx
      have hx' := (mem_maximalIdeal_protectedRationals M x).mp hx
      have hx₀ : x = 0 := Subtype.ext (Rat.num_eq_zero.mp (by simpa [hz] using hx'))
      exact hx₀ ▸ N.asIdeal.zero_mem))
    exact False.elim ((hL p hp).ne_zero ((he ▸ hz : ringChar (protectedRationals L ⧸ N.asIdeal) = 0) ▸ hN.symm))
  · exact h

/-- The maximal ideals of a nonempty protected prime set correspond to its primes. -/
noncomputable def protectedRationalsMaximalEquiv (hL : ∀ p ∈ L, Nat.Prime p) (h₀ : L.Nonempty) :
    MaximalSpectrum (protectedRationals L) ≃ ↥L :=
  Equiv.ofBijective (fun M => ⟨_, residueChar_mem_of_nonempty_protectedRationals hL h₀ M⟩)
    ⟨fun _ _ h => residueChar_injective_protectedRationals (congrArg Subtype.val h), fun p => by
      obtain ⟨M, hM⟩ := exists_maximal_protectedRationals (hL _ p.property) p.property
      exact ⟨M, Subtype.ext hM⟩⟩

end FiniteFourier
end LinearAlgebra
end OAI
