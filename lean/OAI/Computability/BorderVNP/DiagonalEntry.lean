import OAI.Computability.BorderVNP.Diagonal
import OAI.Computability.BorderVNP.ResiduePinsBasis
import OAI.Computability.BorderVNP.ResidueFourierCount

/-!
# One residue entry per expanded contraction assignment

The final private guess in §11 produces a zero/one path count in the prime
field, even when the gadget value belongs to a larger finite field. A single
choice of coordinate extensions works for all substituted pins, live pins,
gadget coefficients and parameter exponents.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open ResidueBox ResidueFourier ResiduePins Module
open scoped BigOperators Classical

variable {σ β ι E K : Type*} [Fintype σ] [Fintype β] [Fintype ι]
    [Field E] [Field K] [Fintype K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- A parameter monomial carries no power of the distinguished curve coordinate `t`. -/
def parameterShift (μ : σ →₀ ℕ) : Exponent σ := Option.elim' 0 (fun i => (μ i : ℤ))

/-- Additive entry of the actual residue matrix at a chosen substituted row
and live column. Its parameter argument is the formal polynomial exponent. -/
noncomputable def entryWeight (B : Basis β (ZMod p) E) (H q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (μ : σ →₀ ℕ) (i j : Index β σ H) : E →+ ZMod p where
  toFun a := weights B H q hq g (.id E) (parameterShift μ) a i j
  map_zero' := by simp
  map_add' a b := by simp

variable {p}

/-- Binary guesses for the interpolation grid and final prime-residue
threshold, with invalid grid words contributing zero. -/
abbrev EntryChoices (σ K : Type*) [Fintype K] (p : ℕ) :=
  (Option σ → FieldWord K) × Fin (2 ^ Nat.clog 2 p)

/-- The contribution on a single branch of the entry reader, before
reduction modulo the characteristic. -/
noncomputable def entryBranch (B : Basis β (ZMod p) E)
    (φ : E →ₐ[ZMod p] K) (enc : K ≃ Fin (Fintype.card K))
    (projection : β → K →ₗ[ZMod p] ZMod p) {H : ℕ} (q : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (a : E) (μ : σ →₀ ℕ)
    (i j : Index β σ H) (guess : EntryChoices σ K p) : ℤ :=
  let v := wordValue enc (fun x => projection j.1
    (pathSummand φ.toRingHom q g a (B i.1) i.2.val (parameterShift μ) j.2.val x)) guess.1
  if guess.2.val < v.val then 1 else 0

omit [Fintype β] in
/-- The projected residue matrix entry equals the reduction of the signed
sum of its private entry branches. The coordinate extensions are selected
once, before the program is supplied with the two pin indices. -/
theorem exists_entry_reader (B : Basis β (ZMod p) E) (φ : E →ₐ[ZMod p] K)
    (enc : K ≃ Fin (Fintype.card K)) :
    ∃ projection : β → K →ₗ[ZMod p] ZMod p,
      (∀ j, (projection j).comp φ.toLinearMap = B.coord j) ∧
      ∀ (H q : ℕ) (hq : 0 < q) (g : ι → MvPolynomial (Option σ) E)
        (_ : (q - 1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ)
        (a : E) (μ : σ →₀ ℕ) (i j : Index β σ H),
        entryWeight p B H q hq g μ i j a =
          ((∑ guess, entryBranch B φ enc projection q g a μ i j guess : ℤ) : ZMod p) := by
  choose projection hproj hcount using fun j => entry_binary_count (ι := ι) (σ := σ) p φ (B.coord j) enc
  refine ⟨projection, hproj, ?_⟩
  intro H q hq g hwidth a μ i j
  change B.coord j.1 ((rowPolynomial q hq g _ a (B i.1) i.2.val (parameterShift μ)).coeff j.2.val) = _
  rw [hcount j.1 q hq g a (B i.1) i.2.val (parameterShift μ) j.2.val hwidth]
  rw [Fintype.sum_prod_type]
  push_cast
  simp only [entryBranch, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rfl

end Diagonal

end BorderVNP
end Computability
end OAI
