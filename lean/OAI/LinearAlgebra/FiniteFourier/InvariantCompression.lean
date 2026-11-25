import OAI.LinearAlgebra.FiniteFourier.CyclicAnnihilator
import OAI.LinearAlgebra.FiniteFourier.KrylovCut
import Mathlib

/-! # Compression by cutting independent Krylov chains

A cut extends a nilpotent invariant subspace by exactly `b` dimensions at the cost of
one rank. The quotient left after the last cut has minimal polynomial of degree at most
`b`. Multiplying it by `X^b` kills the whole space.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
private theorem quotient_pow (C : End K V) (U : Submodule K V) (hU : U ≤ U.comap C)
    (i : ℕ) (x : V) : ((U.mapQ U C hU) ^ i) (U.mkQ x) = U.mkQ ((C ^ i) x) := by
  rw [← U.mapQ_pow hU i]
  rfl

private theorem finish_cut (C : End K V) (U : Submodule K V) (hU : U ≤ U.comap C)
    (hC : Function.Injective (1 - C : End K V)) (b : ℕ)
    (hz : ∀ x ∈ U, (C ^ b) x = 0)
    (h : ∀ x : V, ¬LinearIndependent K (fun i : Fin (b+1) ↦ U.mkQ ((C ^ (i:ℕ)) x))) :
    ∃ g : K[X], g.natDegree ≤ 2 * b ∧ g.eval 1 ≠ 0 ∧ aeval C g = 0 := by
  classical
  let A := U.mapQ U C hU
  have hq (x : V ⧸ U) : ¬LinearIndependent K (fun i : Fin (b+1) ↦ (A ^ (i:ℕ)) x) := by
    obtain ⟨x, rfl⟩ := U.mkQ_surjective x
    simpa only [A, quotient_pow] using h x
  obtain ⟨p, hp, hpb, hpA⟩ := exists_aeval_zero_of_forall_krylov_dependent A b hq
  let m := minpoly K A
  have hm : m.natDegree ≤ b := (natDegree_le_of_dvd (minpoly.dvd K A hpA) hp).trans hpb
  have hI : Function.Injective (1 - A : End K (V ⧸ U)) := by
    apply LinearMap.injective_iff_surjective.mpr
    intro y
    obtain ⟨v, rfl⟩ := U.mkQ_surjective y
    obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hC v
    exact ⟨U.mkQ x, by simpa [A, LinearMap.sub_apply] using congrArg U.mkQ hx⟩
  have hm1 : m.eval 1 ≠ 0 := by
    intro h1
    obtain ⟨w, hw, hne⟩ := (Module.End.hasEigenvalue_of_isRoot
      (f := A) (μ := (1:K)) h1).exists_hasEigenvector
    apply hne
    apply hI
    simpa [LinearMap.sub_apply, sub_eq_zero] using (Module.End.mem_eigenspace_iff.mp hw).symm
  refine ⟨X ^ b * m, (natDegree_mul_le.trans ?_), by simpa using hm1, ?_⟩
  · rw [natDegree_X_pow]; omega
  · rw [map_mul, map_pow, aeval_X]
    ext x
    apply hz
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ ((aeval C m) x) = 0
    have hx : (aeval A m) (U.mkQ x) = 0 := by rw [minpoly.aeval]; rfl
    simpa only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, A, quotient_pow] using hx

/-- The dimension and nilpotence gained from a single cut. -/
private theorem grow_cut (C C' : End K V) (U : Submodule K V) (hU : U ≤ U.comap C)
    (b : ℕ) (hb : 0 < b) (x : V)
    (hli : LinearIndependent K (fun i : Fin (b+1) ↦ U.mkQ ((C ^ (i:ℕ)) x)))
    (hz : ∀ u ∈ U, (C ^ b) u = 0) (heq : ∀ u ∈ U, C' u = C u)
    (hs : ∀ i : ℕ, i + 1 < b → C' ((C ^ i) x) = (C ^ (i+1)) x)
    (ht : C' ((C ^ (b-1)) x) = 0) :
    ∃ U' : Submodule K V, U' ≤ U'.comap C' ∧
      (∀ u ∈ U', (C' ^ b) u = 0) ∧ finrank K U' = finrank K U + b := by
  let v : Fin b → V := fun i ↦ (C ^ (i:ℕ)) x
  let P := span K (Set.range v)
  have hli' : LinearIndependent K (U.mkQ ∘ v) := hli.comp Fin.castSucc (Fin.castSucc_injective b)
  have hd : Disjoint P U := by simpa [P] using range_ker_disjoint hli'
  have hdim : finrank K P = b := by simpa [P] using finrank_span_eq_card (hli'.of_comp U.mkQ)
  have hi (i : ℕ) (hi : i < b) : (C' ^ i) x = (C ^ i) x := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih (by omega), hs _ hi]
  have hx0 : (C' ^ b) x = 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    rw [pow_succ', Module.End.mul_apply, hi n (by omega)]
    exact ht
  refine ⟨U ⊔ P, ?_, ?_, ?_⟩
  · apply sup_le
    · intro u hu
      change C' u ∈ U ⊔ P
      rw [heq u hu]
      exact (show U ≤ U ⊔ P from le_sup_left) (hU hu)
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      change C' ((C ^ (i:ℕ)) x) ∈ U ⊔ P
      by_cases h : (i:ℕ)+1 < b
      · rw [hs _ h]
        exact (show P ≤ U ⊔ P from le_sup_right) (subset_span ⟨(⟨(i:ℕ)+1, h⟩ : Fin b), rfl⟩)
      · have he : (i:ℕ) = b-1 := by omega
        rw [he, ht]
        exact zero_mem _
  · have he' (j : ℕ) (u : V) (hu : u ∈ U) : (C' ^ j) u = (C ^ j) u := by
      induction j generalizing u with
      | zero => rfl
      | succ j ih =>
        simp only [pow_succ, Module.End.mul_apply, heq u hu, ih (C u) (hU hu)]
    change U ⊔ P ≤ LinearMap.ker (C'^b)
    apply sup_le
    · intro u hu
      exact (he' b u hu).trans (hz u hu)
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      change (C' ^ b) ((C ^ (i:ℕ)) x) = 0
      rw [← hi _ i.isLt, ← Module.End.mul_apply, ← pow_add, Nat.add_comm, pow_add,
        Module.End.mul_apply, hx0, map_zero]
  · have h := finrank_sup_add_finrank_inf_eq U P
    rw [hd.symm.eq_bot, finrank_bot, add_zero, hdim] at h
    exact h

private theorem perturbation_rank (C₁ C₂ C₃ : End K V) :
    finrank K (LinearMap.range (C₁-C₃)) ≤
      finrank K (LinearMap.range (C₁-C₂)) + finrank K (LinearMap.range (C₂-C₃)) := by
  let f := C₁-C₂
  let g := C₂-C₃
  have eq : C₁-C₃ = f + g := by dsimp [f,g]; abel
  rw [eq]
  exact (Submodule.finrank_mono (LinearMap.range_add_le f g)).trans
    (by change finrank K ↥(f.range ⊔ g.range) ≤ finrank K f.range + finrank K g.range
        have := finrank_sup_add_finrank_inf_eq f.range g.range
        omega)

private theorem compress_from_subspace (T : End K V) (b : ℕ) (hb : 0 < b)
    (C : End K V) (U : Submodule K V) (hU : U ≤ U.comap C)
    (hC : Function.Injective (1-C : End K V)) (hz : ∀ u ∈ U, (C ^ b) u = 0)
    (hr : finrank K (LinearMap.range (T - C)) * b ≤ finrank K U) :
    ∃ C₀ : End K V, ∃ g : K[X], g.natDegree ≤ 2 * b ∧ g.eval 1 ≠ 0 ∧
      aeval C₀ g = 0 ∧ finrank K (LinearMap.range (T-C₀)) * b ≤ finrank K V := by
  classical
  by_cases h : ∃ x : V, LinearIndependent K (fun i : Fin (b+1) ↦ U.mkQ ((C ^ (i:ℕ)) x))
  · obtain ⟨x, hx⟩ := h
    obtain ⟨C', hagree, hs, ht, hr', hinj⟩ := exists_krylov_cut C U (fun _ hu ↦ hU hu) hC b hb x hx
    obtain ⟨U', hU', hzero, hdim⟩ := grow_cut C C' U hU b hb x hx hz hagree hs ht
    have hcost : finrank K (LinearMap.range (T-C')) * b ≤ finrank K U' := calc
      _ ≤ (finrank K (LinearMap.range (T-C)) + finrank K (LinearMap.range (C-C'))) * b :=
        Nat.mul_le_mul_right b (perturbation_rank T C C')
      _ ≤ (finrank K (LinearMap.range (T-C)) + 1) * b := by gcongr
      _ ≤ _ := by rw [Nat.add_mul, one_mul, hdim]; omega
    exact compress_from_subspace T b hb C' U' hU' hinj hzero hcost
  · obtain ⟨g, hg, h1, hzero⟩ := finish_cut C U hU hC b hz (not_exists.mp h)
    exact ⟨C,g,hg,h1,hzero,hr.trans U.finrank_le⟩
termination_by finrank K V - finrank K U
decreasing_by
  have := U'.finrank_le
  omega

/-- A rank perturbation of cost at most `dim(V)/b` yields an annihilator of degree at most
`2b` which is nonzero at one. -/
theorem exists_compressed_end (C : End K V) (hC : Function.Injective (1-C : End K V))
    (b : ℕ) (hb : 0 < b) :
    ∃ C₀ : End K V, ∃ g : K[X], g.natDegree ≤ 2*b ∧ g.eval 1 ≠ 0 ∧
      aeval C₀ g = 0 ∧ finrank K (LinearMap.range (C-C₀))*b ≤ finrank K V := by
  exact compress_from_subspace C b hb C ⊥ bot_le hC (by simp) (by simp)

/-- State compression before forming the transfer matrix. The rank bound counts one change
for every full independent chain of length `b`. -/
theorem exists_compressed_state {S : Type*} [Fintype S] [DecidableEq S]
    (C : Matrix S S K) (hC : IsUnit (1-C).det) (b : ℕ) (hb : 0 < b) :
    ∃ C₀ : Matrix S S K, ∃ g : K[X], g.natDegree ≤ 2*b ∧ g.eval 1 ≠ 0 ∧
      aeval C₀ g = 0 ∧ (C-C₀).rank*b ≤ Fintype.card S := by
  let e : Matrix S S K ≃ₐ[K] End K (S → K) := Matrix.toLinAlgEquiv'
  have hu := ((Matrix.isUnit_iff_isUnit_det _).mpr hC).map e
  rw [map_sub, map_one] at hu
  obtain ⟨A, g, hd, h1, hA, hr⟩ := exists_compressed_end (e C)
    (LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)) b hb
  refine ⟨e.symm A, g, hd, h1, by rw [aeval_algHom_apply, hA, map_zero], ?_⟩
  change finrank K (LinearMap.range (e (C-e.symm A))) * b ≤ Fintype.card S
  rw [map_sub, AlgEquiv.apply_symm_apply]
  simpa only [finrank_pi] using hr

end FiniteFourier
end LinearAlgebra
end OAI
