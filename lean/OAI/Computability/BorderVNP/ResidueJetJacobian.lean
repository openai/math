import OAI.Computability.BorderVNP.ResidueJetRingLinear
import OAI.Computability.BorderVNP.ResidueSocle
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # The Jacobian of the chart equations in the parameter jet

The time variable is evaluated in the coefficient ring, while each parameter
coordinate is its branch value plus an independent nilpotent increment. The
linear row of each translated equation is its evaluated Jacobian row. Their
product to the top power has just the expected determinant coefficient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue.JetRing

open MvPolynomial Matrix
open scoped Classical

variable {ι E B F : Type*} [CommRing E] [CommRing B]

/-- The coefficient algebra embeds in every truncated box, including the empty box. -/
theorem algebraMap_injective (d : ℕ) : Function.Injective (algebraMap B (Carrier ι B d)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  change mk d (C b : MvPolynomial ι B) = 0 at hb
  by_contra h
  obtain ⟨i, hi⟩ := (mem_truncIdeal d (C b : MvPolynomial ι B)).mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hb) 0 (mem_support_iff.mpr (by simpa using h))
  simp at hi

private noncomputable def shiftedValue (a : Option ι → B) : Option ι → MvPolynomial ι B
  | none => C (a none)
  | some i => C (a (some i)) + X i

/-- Evaluate the time variable and translate all parameter variables by their branch values. -/
noncomputable def shiftChart (φ : E →+* B) (a : Option ι → B) :
    MvPolynomial (Option ι) E →+* MvPolynomial ι B :=
  eval₂Hom (C.comp φ) (shiftedValue a)

/-- Evaluating at zero increments recovers the original evaluation. -/
theorem shiftChart_constant (φ : E →+* B) (a : Option ι → B) (f : MvPolynomial (Option ι) E) :
    constantCoeff (shiftChart φ a f) = eval₂Hom φ a f := by
  have h : (constantCoeff : MvPolynomial ι B →+* B).comp (shiftChart φ a) = eval₂Hom φ a := by
    apply ringHom_ext
    · intro c
      simp [shiftChart]
    · rintro (_ | i) <;> simp [shiftChart, shiftedValue]
  exact DFunLike.congr_fun h f

private theorem shiftChart_pderiv (φ : E →+* B) (a : Option ι → B) (i : ι)
    (f : MvPolynomial (Option ι) E) :
    pderiv i (shiftChart φ a f) = shiftChart φ a (pderiv (some i) f) := by
  have hx (j : Option ι) :
      pderiv i (shiftChart φ a (X j)) = shiftChart φ a (pderiv (some i) (X j)) := by
    rcases j with _ | j
    · simp [shiftChart, shiftedValue]
    · by_cases h : j = i
      · subst j
        simp [shiftChart, shiftedValue]
      · simp [shiftChart, shiftedValue, h]
  induction f using MvPolynomial.induction_on with
  | C c => simp [shiftChart]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf => simp only [map_mul, pderiv_mul, hf, hx, map_add]

/-- The coefficient of an individual parameter increment is the evaluated partial derivative. -/
theorem shiftChart_linear_coeff (φ : E →+* B) (a : Option ι → B)
    (f : MvPolynomial (Option ι) E) (i : ι) :
    (shiftChart φ a f).coeff (Finsupp.single i 1) = eval₂Hom φ a (pderiv (some i) f) := by
  rw [← shiftChart_constant, ← shiftChart_pderiv, constantCoeff_eq, coeff_pderiv]
  simp

variable [Fintype ι] [DecidableEq ι] [Field F]

/-- The matrix of the parameter derivatives, evaluated at a branch point. -/
noncomputable def chartJacobian (φ : E →+* F) (a : Option ι → F)
    (g : ι → MvPolynomial (Option ι) E) : Matrix ι ι F :=
  fun i j => eval₂Hom φ a (pderiv (some j) (g i))

/-- The top-power product of the chart equations in the parameter jet is their
Jacobian determinant to that power times the socle monomial. The coefficient
map ψ may itself be a Taylor homomorphism into a ring with nilpotents. -/
theorem shiftChart_product (p u : ℕ) [ExpChar B p] (φ : E →+* F) (ψ : F →+* B)
    (a : Option ι → F) (g : ι → MvPolynomial (Option ι) E) (hg : ∀ i, eval₂Hom φ a (g i) = 0) :
    ∏ i, mk (p ^ u - 1) (shiftChart (ψ.comp φ) (ψ ∘ a) (g i)) ^ (p ^ u - 1) =
      algebraMap B _ (ψ ((chartJacobian φ a g).det ^ (p ^ u - 1))) *
        socle (ι := ι) (B := B) (p ^ u - 1) := by
  let d := p ^ u - 1
  let G (i : ι) := shiftChart (ψ.comp φ) (ψ ∘ a) (g i)
  have hG (i : ι) : constantCoeff (G i) = 0 := by
    dsimp only [G]
    rw [shiftChart_constant]
    exact (map_eval₂Hom φ a ψ (g i)).symm.trans ((congrArg ψ (hg i)).trans ψ.map_zero)
  have hcoeff (i j : ι) : (G i).coeff (Finsupp.single j 1) = ψ (chartJacobian φ a g i j) := by
    dsimp only [G]
    rw [shiftChart_linear_coeff]
    exact (map_eval₂Hom φ a ψ (pderiv (some j) (g i))).symm
  let Q := Carrier ι B d
  let ρ : F →+* Q := (algebraMap B Q).comp ψ
  let : Algebra F Q := ρ.toAlgebra
  have : ExpChar Q p := expChar_of_injective_ringHom (algebraMap_injective d) p
  have hx (i : ι) : (coord d i : Q) ^ p ^ u = 0 := by
    simpa only [d, Nat.sub_add_cancel (expChar_pow_pos B p u)] using coord_pow (B := B) d i
  change ∏ i, mk d (G i) ^ d = _
  rw [prod_pow_eq_linear d G hG]
  simp only [mk_linearPart, hcoeff]
  exact socle_determinant p u (chartJacobian φ a g) (fun i => (coord d i : Q)) hx

/-- A further test polynomial contributes its constant term to the Jacobian coefficient. -/
theorem top_shiftChart_product (p u : ℕ) [ExpChar B p] (φ : E →+* F) (ψ : F →+* B)
    (a : Option ι → F) (g : ι → MvPolynomial (Option ι) E) (hg : ∀ i, eval₂Hom φ a (g i) = 0)
    (f : MvPolynomial ι B) :
    top (p ^ u - 1) ((∏ i, mk (p ^ u - 1) (shiftChart (ψ.comp φ) (ψ ∘ a) (g i)) ^
      (p ^ u - 1)) * mk (p ^ u - 1) f) =
      ψ ((chartJacobian φ a g).det ^ (p ^ u - 1)) * constantCoeff f := by
  rw [shiftChart_product p u φ ψ a g hg, mul_assoc, mul_comm (socle _), mul_socle,
    ← Algebra.smul_def, map_smul, ← Algebra.smul_def, map_smul]
  simp [socle, top_monomial]

end Residue.JetRing

end BorderVNP
end Computability
end OAI
