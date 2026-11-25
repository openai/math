import OAI.Computability.BorderVNP.ResidueCoefficientField
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LaurentSeries

/-! # The uniformizer expansion of a complete branch

Evaluating a power series modulo each power of the maximal ideal only reads
a finite truncation. The compatible evaluations assemble in the complete
ring. Successively subtracting the lift of each residue and dividing by the
uniformizer proves that every element has such an expansion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open scoped PowerSeries

variable {R k : Type*} [CommRing R] [CommRing k]
  (I : Ideal R) (σ : k →+* R) (s : R)

private theorem eval_congr (hs : s ∈ I) {n : ℕ} {a b : Polynomial k}
    (h : ∀ i < n, a.coeff i = b.coeff i) :
    Ideal.Quotient.mk (I ^ n) (a.eval₂ σ s) = Ideal.Quotient.mk (I ^ n) (b.eval₂ σ s) := by
  obtain ⟨c, hc⟩ : (Polynomial.X : Polynomial k) ^ n ∣ a - b :=
    Polynomial.X_pow_dvd_iff.mpr fun i hi => by rw [Polynomial.coeff_sub, h i hi, sub_self]
  apply Ideal.Quotient.eq.mpr
  rw [← Polynomial.eval₂_sub, hc, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  exact (I ^ n).mul_mem_right _ (Ideal.pow_mem_pow hs n)

private noncomputable def residueTrunc (hs : s ∈ I) (n : ℕ) : k⟦X⟧ →+* R ⧸ I ^ n where
  toFun f := Ideal.Quotient.mk (I ^ n) ((PowerSeries.trunc n f).eval₂ σ s)
  map_zero' := by simp
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk _), ← Polynomial.eval₂_one σ s]
    apply eval_congr I σ s hs
    intro i hi
    simp [PowerSeries.coeff_trunc, hi, PowerSeries.coeff_one, Polynomial.coeff_one]
  map_add' f g := by simp
  map_mul' f g := by
    rw [← map_mul, ← Polynomial.eval₂_mul]
    apply eval_congr I σ s hs
    intro i hi
    rw [PowerSeries.coeff_trunc, ite_eq_left hi]
    simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hi

private theorem compatibleTrunc (hs : s ∈ I) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (residueTrunc I σ s hs n) =
      residueTrunc I σ s hs m := by
  ext f
  change Ideal.Quotient.mk (I ^ m) ((PowerSeries.trunc n f).eval₂ σ s) = _
  apply eval_congr I σ s hs
  intro i hi
  simp [PowerSeries.coeff_trunc, hi, hi.trans_le hmn]

/-- Evaluate a series by evaluating its compatible truncations in the adically complete ring. -/
noncomputable def uniformizerEval [IsAdicComplete I R] (hs : s ∈ I) : k⟦X⟧ →+* R :=
  IsAdicComplete.liftRingHom I (residueTrunc I σ s hs) (compatibleTrunc I σ s hs)

/-- Reduction modulo a power of the uniformizer reads the corresponding finite polynomial. -/
theorem uniformizerEval_mod [IsAdicComplete I R] (hs : s ∈ I) (n : ℕ) (f : k⟦X⟧) :
    Ideal.Quotient.mk (I ^ n) (uniformizerEval I σ s hs f) =
      Ideal.Quotient.mk (I ^ n) ((f.trunc n).eval₂ σ s) :=
  IsAdicComplete.mk_liftRingHom I _ _ n f

/-- Uniformizer evaluation extends ordinary evaluation of polynomials. -/
theorem uniformizerEval_polynomial [IsAdicComplete I R] (hs : s ∈ I) (f : Polynomial k) :
    uniformizerEval I σ s hs (f : k⟦X⟧) = f.eval₂ σ s := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  have h : Ideal.Quotient.mk (I ^ n) (uniformizerEval I σ s hs (f : k⟦X⟧)) =
      Ideal.Quotient.mk (I ^ n) (f.eval₂ σ s) := by
    rw [uniformizerEval_mod]
    apply eval_congr I σ s hs
    intro i hi
    simp [PowerSeries.coeff_trunc, hi]
  simpa using! h

/-- The series variable evaluates to the prescribed uniformizer. -/
theorem uniformizerEval_X [IsAdicComplete I R] (hs : s ∈ I) :
    uniformizerEval I σ s hs PowerSeries.X = s := by
  simpa using uniformizerEval_polynomial I σ s hs (Polynomial.X : Polynomial k)

section CoefficientField

variable (rep : (R ⧸ I) →+* R) (hrep : ∀ a, Ideal.Quotient.mk I (rep a) = a)

include hrep

private theorem existsTail (hsI : I = Ideal.span {s}) (x : R) :
    ∃ y, x = rep (Ideal.Quotient.mk I x) + s * y := by
  have hx : x - rep (Ideal.Quotient.mk I x) ∈ I := Ideal.Quotient.eq.mp (hrep _).symm
  have hd : s ∣ x - rep (Ideal.Quotient.mk I x) :=
    Ideal.mem_span_singleton.mp (Eq.mp (congrArg (fun J : Ideal R => _ ∈ J) hsI) hx)
  obtain ⟨y, hy⟩ := hd
  exact ⟨y, by rw [← hy]; abel⟩

private noncomputable def tail (hsI : I = Ideal.span {s}) (x : R) : R :=
  (existsTail I s rep hrep hsI x).choose

private theorem tail_step (hsI : I = Ideal.span {s}) (x : R) :
    x = rep (Ideal.Quotient.mk I x) + s * tail I s rep hrep hsI x :=
  (existsTail I s rep hrep hsI x).choose_spec

/-- Reading a residue and dividing the remainder by the uniformizer yields every coefficient. -/
theorem uniformizerEval_surjective [IsAdicComplete I R] (hs : s ∈ I)
    (hsI : I = Ideal.span {s}) : Function.Surjective (uniformizerEval I rep s hs) := by
  intro x
  let peel := tail I s rep hrep hsI
  let f : (R ⧸ I)⟦X⟧ := PowerSeries.mk fun i => Ideal.Quotient.mk I (peel^[i] x)
  have expand (n : ℕ) : x = (f.trunc n).eval₂ rep s + s ^ n * peel^[n] x := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        x = (f.trunc n).eval₂ rep s + s ^ n * peel^[n] x := ih
        _ = (f.trunc n).eval₂ rep s + s ^ n *
              (rep (Ideal.Quotient.mk I (peel^[n] x)) + s * peel (peel^[n] x)) :=
          congrArg (fun z => (f.trunc n).eval₂ rep s + s ^ n * z) (tail_step I s rep hrep hsI _)
        _ = _ := by simp [PowerSeries.trunc_succ, f, Function.iterate_succ_apply', pow_succ]; ring
  refine ⟨f, (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n => ?_⟩
  have h : Ideal.Quotient.mk (I ^ n) (uniformizerEval I rep s hs f) = Ideal.Quotient.mk (I ^ n) x := by
    rw [uniformizerEval_mod]
    apply Ideal.Quotient.eq.mpr
    have hx : (f.trunc n).eval₂ rep s - x = -(s ^ n * peel^[n] x) := by
      linear_combination -(expand n)
    rw [hx]
    exact (I ^ n).neg_mem ((I ^ n).mul_mem_right _ (Ideal.pow_mem_pow hs n))
  simpa using! h

/-- In a domain with nonzero uniformizer, the first nonzero coefficient survives evaluation. -/
theorem uniformizerEval_injective [IsAdicComplete I R] [IsDomain R] (hs : s ∈ I)
    (hs0 : s ≠ 0) : Function.Injective (uniformizerEval I rep s hs) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  by_contra h
  have hx := congrArg (uniformizerEval I rep s hs) (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
  rw [map_mul, map_pow, uniformizerEval_X, hf] at hx
  have hz := (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ hs0)
  have h0 := uniformizerEval_mod I rep s hs 1 (PowerSeries.divXPowOrder f)
  simp only [hz, map_zero, PowerSeries.trunc_one_left, Polynomial.eval₂_C] at h0
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h0.symm
  rw [pow_one] at hm
  have hr := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [hrep] at hr
  apply h
  apply PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hr

/-- A complete equal-characteristic ring with principal maximal ideal has the
power series presentation used for the completed branch. -/
noncomputable def uniformizerSeriesEquiv [IsAdicComplete I R] [IsDomain R] (hs : s ∈ I)
    (hs0 : s ≠ 0) (hsI : I = Ideal.span {s}) : (R ⧸ I)⟦X⟧ ≃+* R :=
  RingEquiv.ofBijective (uniformizerEval I rep s hs)
    ⟨uniformizerEval_injective I s rep hrep hs hs0, uniformizerEval_surjective I s rep hrep hs hsI⟩

end CoefficientField

section Branch

open IsLocalRing

variable [IsDomain R] [IsDiscreteValuationRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP (ResidueField R) p] [Fintype (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]

/-- A choice of uniformizer identifies the complete valuation ring of the
branch with power series over its residue field. -/
noncomputable def completedBranchSeries (π : R) (hπ : Irreducible π) :
    (ResidueField R)⟦X⟧ ≃+* R := by
  letI : CharP (R ⧸ maximalIdeal R) p := inferInstanceAs (CharP (ResidueField R) p)
  letI : PerfectRing (R ⧸ maximalIdeal R) p := inferInstanceAs (PerfectRing (ResidueField R) p)
  exact uniformizerSeriesEquiv (maximalIdeal R) π (coefficientSection (maximalIdeal R) p)
    (reduction_coefficientSection (maximalIdeal R) p) hπ.not_isUnit hπ.ne_zero hπ.maximalIdeal_eq

/-- The fraction field of the completed branch is the Laurent series field κ((s)). -/
noncomputable def completedBranchLaurent (L : Type*) [Field L] [Algebra R L] [IsFractionRing R L]
    (π : R) (hπ : Irreducible π) : LaurentSeries (ResidueField R) ≃+* L :=
  IsFractionRing.ringEquivOfRingEquiv (completedBranchSeries p π hπ)

/-- The Laurent variable corresponds to the selected uniformizer. -/
theorem completedBranchLaurent_uniformizer (L : Type*) [Field L] [Algebra R L] [IsFractionRing R L]
    (π : R) (hπ : Irreducible π) :
    completedBranchLaurent p L π hπ (algebraMap _ _ (PowerSeries.X : (ResidueField R)⟦X⟧)) =
      algebraMap R L π := by
  change IsFractionRing.ringEquivOfRingEquiv _ _ = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  apply congrArg (algebraMap R L)
  exact uniformizerEval_X (maximalIdeal R) _ _ _

end Branch

end Residue

end BorderVNP
end Computability
end OAI
