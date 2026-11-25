import OAI.Computability.BorderVNP.ResidueCoordinateJets
import OAI.Computability.BorderVNP.ResidueChartMap
import OAI.Computability.BorderVNP.ResidueCartierIteration

/-!
# The complete-intersection Cartier formula

Lemma 10.2 computes the Cartier extraction at a branch from the chart equations
and the parameter Jacobian. The equations vanish on the branch, but the
individual chart parameters may have poles. The calculation uses finite jets
over the Laurent completion, so only the time coordinate is required to be a
unit and its derivative nonzero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open BranchJet CoordinateJets JetRing ResidueBox
open scoped BranchJet Classical

variable {E κ σ : Type*} [Field E] [Field κ] [Fintype σ] [DecidableEq σ]
  (p : ℕ) [Fact p.Prime] [CharP E p] [PerfectRing E p] [CharP κ p] [PerfectRing κ p]

/-- Lemma 10.2 for one Frobenius extraction in the full chart. -/
theorem branch_formula_prime (g : σ → MvPolynomial (Option σ) E) (φ : E →+* LaurentSeries κ)
    (x : σ → LaurentSeries κ) (t : (LaurentSeries κ)ˣ)
    (hg : ∀ i, MvPolynomial.eval₂Hom φ (fun j => j.elim (t : LaurentSeries κ) x) (g i) = 0)
    (hJ : (chartJacobian φ (fun j => j.elim (t : LaurentSeries κ) x) g).det ≠ 0)
    (ht : LaurentSeries.derivative κ (t : LaurentSeries κ) ≠ 0) (f : Mixed σ E) :
    let η₀ := LaurentSeries.derivative κ (t : LaurentSeries κ) /
      (chartJacobian φ (fun j => j.elim (t : LaurentSeries κ) x) g).det
    ∃ z : Mixed σ E, mixedToLaurent z =
      ambientCartier p 1 (mixedToLaurent f * equationProduct (p ^ 1) g) ∧
      cartier p 1 (mixedEval φ x t f * η₀) = mixedEval φ x t z * η₀ := by
  let F := LaurentSeries κ
  let B := BranchJet.Ring κ p
  let Q := Combined σ κ p
  let d := p-1
  let a (i : Option σ) : F := i.elim (t : F) x
  let J : F := (chartJacobian φ a g).det
  let dt : F := LaurentSeries.derivative κ (t : LaurentSeries κ)
  let ρ := algebraMap B Q
  let ψ : F →+* B := jet p
  let τ := Units.map ψ.toMonoidHom t
  let ε := delta p x (t : F)
  let H := (∏ i, polynomialMixed (g i) ^ d) * f
  have : ExpChar Q p := expChar_of_injective_ringHom (JetRing.algebraMap_injective d) p
  have htime : (↑(Units.map ρ.toMonoidHom τ) : Q) = algebraMap F Q (t : F) + ε none := by
    change ρ (ψ (t : F)) = algebraMap F Q (t : F) + ρ (ψ (t : F) - algebraMap F B (t : F))
    rw [map_sub, IsScalarTower.algebraMap_eq F B Q]
    change _ = ρ _ + (_ - ρ _)
    abel
  obtain ⟨z, hz, htval⟩ := ambient_top_jet p 1 φ x t (Units.map ρ.toMonoidHom τ) ε htime
    (fun i => by simpa using delta_pow p x (t : F) i) (chartTop p (t : F))
    (fun b hb => by simpa using chartTop_monomial p x (t : F) ht b (by simpa using hb)) H
  refine ⟨z, ?_, ?_⟩
  · simpa only [H, equationProduct, map_mul, map_prod, map_pow, mixedToLaurent_polynomialMixed,
      pow_one, mul_comm] using hz
  have hφ : (algebraMap F Q).comp φ = ρ.comp (ψ.comp φ) := by
    rw [IsScalarTower.algebraMap_eq F B Q, jet_comp_of_perfect p φ]
    rfl
  have hx (i : σ) : algebraMap F Q (x i) + ε (some i) = ρ (ψ (x i)) + coord d i := by
    change algebraMap F Q (x i) + (ρ (ψ (x i) - algebraMap F B (x i)) + coord d i) = _
    rw [IsScalarTower.algebraMap_eq F B Q, map_sub]
    change ρ _ + (ρ _ - ρ _ + _) = _
    abel
  rw [hφ, show (fun i => algebraMap F Q (x i) + ε (some i)) =
      (fun i => ρ (ψ (x i)) + coord d i) from funext hx, ← mk_shiftMixed] at htval
  let f' := shiftMixed (ψ.comp φ) (ψ ∘ x) τ f
  have ha : (fun j : Option σ => j.elim (τ : B) (ψ ∘ x)) = ψ ∘ a := by
    funext j
    cases j <;> rfl
  have hrows : JetRing.top d (mk d (shiftMixed (ψ.comp φ) (ψ ∘ x) τ H)) =
      ψ (J ^ d) * ψ (mixedEval φ x t f) := by
    simp only [H, map_mul, map_prod, map_pow, shiftMixed_polynomialMixed, ha]
    have h := top_shiftChart_product p 1 φ ψ a g hg f'
    rw [pow_one] at h
    rw [h, shiftMixed_constant]
    exact congrArg₂ (· * ·) (map_pow ψ J d) (mixedEval_map φ ψ x t f).symm
  change (dt ^ p)⁻¹ * BranchJet.top p
    (JetRing.top d (mk d (shiftMixed (ψ.comp φ) (ψ ∘ x) τ H)) * ψ dt) =
    (mixedEval φ x t z) ^ p ^ 1 at htval
  rw [hrows, jacobian_weight p J _ dt hJ, pow_one] at htval
  have he := (frobenius F p).injective htval
  change J / dt * cartier p 1 (mixedEval φ x t f * (dt / J)) = mixedEval φ x t z at he
  change cartier p 1 (mixedEval φ x t f * (dt / J)) = mixedEval φ x t z * (dt / J)
  rw [← he]
  field_simp [show J ≠ 0 from hJ, show dt ≠ 0 from ht]

/-- Lemma 10.2 for every Frobenius power, with the chart Jacobian and actual
Laurent-series Cartier operator. -/
theorem branch_cartier_formula (g : σ → MvPolynomial (Option σ) E) (φ : E →+* LaurentSeries κ)
    (x : σ → LaurentSeries κ) (t : (LaurentSeries κ)ˣ)
    (hg : ∀ i, MvPolynomial.eval₂Hom φ (fun j => j.elim (t : LaurentSeries κ) x) (g i) = 0)
    (hJ : (chartJacobian φ (fun j => j.elim (t : LaurentSeries κ) x) g).det ≠ 0)
    (ht : LaurentSeries.derivative κ (t : LaurentSeries κ) ≠ 0) (u : ℕ) (f : Mixed σ E) :
    let η₀ := LaurentSeries.derivative κ (t : LaurentSeries κ) /
      (chartJacobian φ (fun j => j.elim (t : LaurentSeries κ) x) g).det
    ∃ z : Mixed σ E, mixedToLaurent z =
      ambientCartier p u (mixedToLaurent f * equationProduct (p ^ u) g) ∧
      cartier p u (mixedEval φ x t f * η₀) = mixedEval φ x t z * η₀ :=
  branch_formula_iterate p g φ x t _ (branch_formula_prime p g φ x t hg hJ ht) u f

end Residue

end BorderVNP
end Computability
end OAI
