import OAI.Computability.BorderVNP.BranchSpecializationConstants
import OAI.LinearAlgebra.SpectralBooks.WireMetricBaseChange

namespace OAI
/-! # Good reduction of tensor restriction inequalities on integral tensors -/

namespace Hierarchy.IntegralRestriction

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open Filter MvPolynomial

variable {J : Type} [Fintype J] [Nonempty J]

private theorem same_univ {A : Type*} (a b : Fintype A) :
    @Finset.univ A a = @Finset.univ A b :=
  congrArg (fun t : Fintype A => @Finset.univ A t) (Subsingleton.elim a b)

/-- Every comparison between integral tensors that holds in characteristic zero
holds in a finite extension of every sufficiently large prime field. -/
theorem good_reduction (K : Type*) [Field K] [CharZero K] (X Y : TensorClass.{0} J ℤ)
    (r : mapScalars (Int.castRingHom K) X ≤ mapScalars (Int.castRingHom K) Y) :
    ∃ N : ℕ, ∀ p ≥ N, p.Prime → ∃ (E : Type) (_ : Field E) (_ : CharP E p),
      mapScalars (Int.castRingHom E) X ≤ mapScalars (Int.castRingHom E) Y := by
  classical
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y =>
      obtain ⟨M,hM⟩ := r
      let ι := (i : J) × X.Leg i × Y.Leg i
      let v (i : ι) : K := M i.1 i.2.1 i.2.2
      obtain ⟨d,k,hd,red⟩ := Computability.BorderVNP.Specialization.exists_fixed_constants_reduction K v ∅ (by simp)
      refine ⟨d.natAbs+1,fun p hp prime => ?_⟩
      have hpd : ¬ (p : ℤ) ∣ d := by
        intro w
        have wd : p ∣ d.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr w
        have := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) wd
        omega
      obtain ⟨E,_,_,_,v',_,hr,_⟩ := red p prime hpd
      refine ⟨E,inferInstance,inferInstance,fun i x y => v' ⟨i,x,y⟩,fun x => ?_⟩
      let pol : MvPolynomial ι ℤ := C (X.coeff x) - ∑ a : (∀ i, Y.Leg i),
        C (Y.coeff a) * ∏ i : J, MvPolynomial.X ⟨i,x i,a i⟩
      have h : eval₂Hom (Int.castRingHom K) v pol = 0 := by
        simp only [pol, map_sub, map_sum, map_mul, map_prod, eval₂Hom_C, eval₂Hom_X',
          sub_eq_zero, v]
        refine (hM x).trans (Finset.sum_congr (same_univ _ _) ?_)
        intro a _
        rfl
      have hh := hr pol h
      simp only [pol, map_sub, map_sum, map_mul, map_prod, eval₂Hom_C, eval₂Hom_X',
        sub_eq_zero] at hh
      refine hh.trans (Finset.sum_congr (same_univ _ _) ?_)
      intro a _
      rfl

private theorem integral_tower {P E : Type*} [Field P] [Field E] [Algebra P E]
    (x : TensorClass.{0} J ℤ) :
    mapScalars (algebraMap P E) (mapScalars (Int.castRingHom P) x) =
      mapScalars (Int.castRingHom E) x := by
  induction x using Quotient.inductionOn with
  | _ X =>
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent
      (X := (X.mapScalars (Int.castRingHom P)).mapScalars (algebraMap P E))
      (Y := X.mapScalars (Int.castRingHom E)) (fun _ => Equiv.refl _)
    intro a
    change algebraMap P E ((X.coeff a : ℤ) : P) = ((X.coeff a : ℤ) : E)
    exact map_intCast _ _

/-- A normalized prime-field spectral evaluation respects a fixed
characteristic-zero comparison at every sufficiently large prime. -/
theorem eventually_mono (K : Type*) [Field K] [CharZero K] (X Y : TensorClass.{0} J ℤ)
    (r : mapScalars (Int.castRingHom K) X ≤ mapScalars (Int.castRingHom K) Y) :
    ∃ N : ℕ, ∀ p ≥ N, ∀ [Fact p.Prime]
      (φ : normalizedSpectrum (S := TensorClass.{0} J (ZMod p)) (· ≤ ·)),
      (pullbackSpectrum (Int.castRingHom (ZMod p)) φ).val X ≤
        (pullbackSpectrum (Int.castRingHom (ZMod p)) φ).val Y := by
  obtain ⟨N,hr⟩ := good_reduction K X Y r
  refine ⟨N,fun p hp _ φ => ?_⟩
  obtain ⟨E,_,_,hle⟩ := hr p hp Fact.out
  let : Algebra (ZMod p) E := ZMod.algebra _ _
  obtain ⟨ψ,hψ⟩ := exists_spectrum_mapScalars (K := E) φ
  change φ.val _ ≤ φ.val _
  rw [← hψ, ← hψ, integral_tower, integral_tower]
  exact ψ.property.2.2.2.2 _ _ hle


end Hierarchy.IntegralRestriction

end OAI
