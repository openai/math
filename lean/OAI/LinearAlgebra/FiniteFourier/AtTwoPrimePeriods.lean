import OAI.LinearAlgebra.FiniteFourier.AtTwoPrimeFourierBasis
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisUnit

/-! # The invariant periods on a prime axis at two

The two period sums at frequency zero add to minus one. Inversion
exchanges them. This gives a basis of the invariant eigenspace by one
and the square period, and identifies its inversion invariants with the
base ring, including in residue characteristic two.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {m : ℕ} [NeZero m]

private theorem atTwoPeriod_expansion (b : Basis (Bool × Fin m) R A)
    {x : A} (hx : x ∈ Submodule.span R (Set.range fun c => b (c, 0))) :
    ∃ a d : R, x = a • b (false, 0) + d • b (true, 0) := by
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  exact ⟨f false, f true, by simpa [add_comm] using hf.symm⟩

private theorem atTwoPeriod_one (b : Basis (Bool × Fin m) R A)
    (hsum : b (false, 0) + b (true, 0) = -1) : (1 : A) = -b (false, 0) - b (true, 0) := by
  linear_combination hsum

/-- A basis of the fixed eigenspace by one and the square period. -/
theorem exists_atTwoPrimePeriod_basis (b : Basis (Bool × Fin m) R A) (σ : A ≃ₐ[R] A)
    (hspan : Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1 =
      Submodule.span R (Set.range fun c => b (c, 0)))
    (hsum : b (false, 0) + b (true, 0) = -1) :
    ∃ e : Basis (Fin 2) R (Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1),
      (e 0 : A) = 1 ∧ (e 1 : A) = b (false, 0) := by
  classical
  let E := Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1
  let a : E := ⟨1, Module.End.mem_eigenspace_iff.mpr (by simp)⟩
  let u : E := ⟨b (false,0), by dsimp [E]; rw [hspan]; exact Submodule.subset_span ⟨false,rfl⟩⟩
  let v : Fin 2 → E := ![a,u]
  have hv : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    have hh := congrArg (fun z : E => (z : A)) hf
    change (↑(∑ j, f j • v j) : A) = 0 at hh
    simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower] at hh
    change f 0 • (1 : A) + f 1 • b (false,0) = 0 at hh
    rw [atTwoPeriod_one b hsum, smul_sub, smul_neg] at hh
    have ht := congrArg (b.coord (true,0)) hh
    have hf₀ : f 0 = 0 := by simpa [Basis.coord_apply] using ht
    have hf' := congrArg (b.coord (false,0)) hh
    have hf₁ : f 1 = 0 := by simpa [hf₀, Basis.coord_apply] using hf'
    fin_cases i <;> assumption
  have hgen : ⊤ ≤ Submodule.span R (Set.range v) := by
    rintro x -
    obtain ⟨s,t,ht⟩ := atTwoPeriod_expansion b (x := x.val) (by rw [← hspan]; exact x.property)
    apply (Submodule.mem_span_range_iff_exists_fun R).mpr
    refine ⟨![-t,s-t], Subtype.ext ?_⟩
    simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower]
    change (-t) • (1 : A) + (s-t) • b (false,0) = x.val
    rw [ht, atTwoPeriod_one b hsum, smul_sub, smul_neg, neg_smul, neg_smul, sub_smul]
    abel
  exact ⟨Basis.mk hv hgen, by rw [Basis.mk_apply]; rfl, by rw [Basis.mk_apply]; rfl⟩

/-- An inversion-fixed element of the invariant eigenspace is scalar.
Inversion interchanges the coefficients of the two periods, so a fixed
element has equal coefficients. -/
theorem exists_atTwoPrimePeriod_scalar (b : Basis (Bool × Fin m) R A)
    (σ τ : A ≃ₐ[R] A)
    (hspan : Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1 =
      Submodule.span R (Set.range fun c => b (c, 0)))
    (hsum : b (false, 0) + b (true, 0) = -1)
    (hswap : ∀ c : Bool, τ (b (c,0)) = b (!c,0))
    {x : A} (hx : σ x = x) (ht : τ x = x) :
    ∃ r : R, x = algebraMap R A r := by
  have hmem : x ∈ Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1 :=
    Module.End.mem_eigenspace_iff.mpr (by simpa using hx)
  obtain ⟨a,d,he⟩ := atTwoPeriod_expansion b (hspan ▸ hmem)
  rw [he, map_add, map_smul, map_smul, hswap, hswap] at ht
  have hc := congrArg (b.coord (false, 0)) ht
  have hda : d = a := by simpa [Basis.coord_apply] using hc
  refine ⟨-a, ?_⟩
  rw [he, hda, ← smul_add, hsum, smul_neg, Algebra.smul_def, mul_one, map_neg]

/-- The sum of the frequency-one vectors has scalar m-th power. -/
theorem exists_atTwoPrimePeriod_sum_pow (b : Basis (Bool × Fin m) R A)
    (σ τ : A ≃ₐ[R] A) (u : R) (hu : u^m = 1)
    (hspan : Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1 =
      Submodule.span R (Set.range fun c => b (c, 0)))
    (hsum : b (false, 0) + b (true, 0) = -1)
    (hswap : ∀ (c : Bool) (j : Fin m), τ (b (c,j)) = b (!c,j))
    (j : Fin m) (heig : ∀ c : Bool, σ (b (c,j)) = u • b (c,j)) :
    ∃ β : R, (b (false,j) + b (true,j))^m = algebraMap R A β := by
  apply exists_atTwoPrimePeriod_scalar b σ τ hspan hsum (fun c => hswap c 0)
  · rw [map_pow, map_add, heig, heig, ← smul_add, smul_pow, hu, one_smul]
  · simp [hswap, add_comm]


section PrimeAxis

open Polynomial

variable (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] (C : PrimeAxisCosets p)
local notation "mₚ" => (p-1)/2
local notation "Aₚ" => AdjoinRoot (cyclotomic p R)
local notation "σₚ" => primeAxisAction R p C.generator
local notation "τₚ" => primeAxisAction R p (-1)

/-- The concrete square period and frequency-one generator in the prime
cyclotomic algebra. The scalar binomial parameter and its root are both
units over the coefficient ring and the cyclotomic algebra, respectively. -/
theorem exists_atTwoPrimePeriod_data (u : Rˣ) (hp : p % 4 = 3) (hp7 : 7 ≤ p)
    (hpR : IsUnit (p : R)) (hm : IsUnit ((mₚ : ℕ) : R)) (hu : u^mₚ = 1)
    (hs : ∀ i j : Fin mₚ, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ∃ (β : Rˣ) (Y : (Aₚ)ˣ) (e : Basis (Fin 2) R (Module.End.eigenspace (σₚ).toLinearMap 1)),
      (e 0 : Aₚ) = 1 ∧ (e 1 : Aₚ) = quadraticPeriod (primeAxisCharacter R p) 1 ∧
      (Y : Aₚ) = atTwoPrimeFourier R C u false ⟨1,by omega⟩ +
        atTwoPrimeFourier R C u true ⟨1,by omega⟩ ∧
      σₚ (Y : Aₚ) = (u:R) • (Y:Aₚ) ∧ τₚ (Y:Aₚ) = (Y:Aₚ) ∧
      (Y:Aₚ)^mₚ = algebraMap R Aₚ β := by
  have hmpos : 0 < mₚ := by omega
  let : NeZero mₚ := ⟨hmpos.ne'⟩
  let j : Fin mₚ := ⟨1, by omega⟩
  obtain ⟨b, hb⟩ := exists_atTwoPrimeFourier_basis R C u hmpos hm hu hs
  have hspan : Module.End.eigenspace (σₚ).toLinearEquiv.toLinearMap 1 =
      Submodule.span R (Set.range (fun c => b (c,0))) := by
    simpa [hb] using atTwoPrimeFourier_eigenspace R C u hmpos hm hu hs (0 : Fin mₚ)
  have hu₀ : b (false,0) = quadraticPeriod (primeAxisCharacter R p) 1 := by
    rw [hb]; exact atTwoPrimeFourier_false_zero R C u hmpos
  have hd₀ : b (true,0) = quadraticPeriod (primeAxisCharacter R p) (-1) := by
    rw [hb]; exact atTwoPrimeFourier_true_zero R C u hp hmpos
  have hsum : b (false,0) + b (true,0) = -1 := by
    rw [hu₀, hd₀]
    exact quadraticPeriod_add _ (primeAxisCharacter_sum R p)
  have hswap (c : Bool) (k : Fin mₚ) : τₚ (b (c,k)) = b (!c,k) := by
    simp only [hb, atTwoPrimeFourier_swap]
  have heig (c : Bool) : σₚ (b (c,j)) = (u : R) • b (c,j) := by
    simp [hb, atTwoPrimeFourier_eigen R C u hu, j]
  obtain ⟨e, he₀, he₁⟩ := exists_atTwoPrimePeriod_basis b σₚ hspan hsum
  have hu' : (u : R)^mₚ = 1 := by simpa using congrArg Units.val hu
  obtain ⟨β, hβ⟩ := exists_atTwoPrimePeriod_sum_pow b σₚ τₚ (u : R) hu' hspan
    hsum hswap j heig
  obtain ⟨hβu, hY⟩ := primeAxis_sum_basis_isUnit hpR b
    (by simp : (false,j) ≠ (true,j)) hmpos hβ
  refine ⟨hβu.unit, hY.unit, e, he₀, he₁.trans hu₀, ?_, ?_, ?_, ?_⟩
  · rw [hY.unit_spec, hb, hb]
  · rw [hY.unit_spec, map_add, heig, heig, smul_add]
  · rw [hY.unit_spec, map_add, hswap, hswap]; exact add_comm ..
  · simpa only [hY.unit_spec, hβu.unit_spec] using hβ

end PrimeAxis

end FiniteFourier
end LinearAlgebra
end OAI
