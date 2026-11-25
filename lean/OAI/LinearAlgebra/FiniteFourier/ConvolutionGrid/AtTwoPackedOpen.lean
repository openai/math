import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoJetCoordinates
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoJetPowerBasis
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.DyadicPackedAssembly
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.PackedAssemblyProduct

/-! # The protected open convolution at two

The cyclotomic jet transforms recover multiplication on a product of prime
cyclic groups. Number the grid by CRT and use the monomial jet coordinates
to pack both operands and gather the product. -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Deformation Polynomial
open scoped Classical BigOperators

local notation "φ₂" => algebraMap TwoLocalBase TwoLocalQuadratic
local notation "ω₂" => AdjoinRoot.root (cyclotomic 3 TwoLocalBase)

private theorem cyclicProduct_instance_independent {R G : Type*} [CommSemiring R]
    [Add G] (f g : Fintype G) (d d' : DecidableEq G) (x y : G → R) :
    @cyclicProduct R _ G f _ d x y = @cyclicProduct R _ G g _ d' x y := by
  cases Subsingleton.elim f g
  cases Subsingleton.elim d d'
  rfl

/-- From the charged product circuits on the prime grid, form a common-operand
open convolution over the two-local ring. The transform budget is preserved
explicitly for the subsequent packing estimate. -/
theorem exists_openConvolution_of_atTwoGrid {σ B : Type*} [Fintype σ] [Fintype B]
    (p : σ → ℕ) [∀ i, Fact (p i).Prime] (cop : Pairwise (Function.onFun Nat.Coprime p))
    {n M r : ℕ} (hM : 0 < M) (hr : 0 < r) {H : B → ℕ} (hH : ∀ b, 0 < H b)
    (hcap : 8*n ≤ M.totient*r*(∏ i, p i)) {cost : ℝ}
    (grid : HasGridProductCircuits φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) (∀ i, ZMod (p i))
      M.totient r H cost) :
    ∃ a d : ℕ, ((2*a+d : ℕ) : ℝ) ≤ cost ∧
      ∃ q : OpenConvolution TwoLocalBase n (B × Fin 3) (jetBlockLength (fun _ => M.totient) H),
        q.RealizesMultiple 1 ∧ q.linearCost ≤ 2*a+d+M.totient*r*(∏ i, p i)+
          ∑ b, JetAssembly.blockCost M.totient (H b) := by
  classical
  let : Nontrivial TwoLocalQuadratic :=
    (AdjoinRoot.nontrivial_iff_of_monic (cyclotomic.monic 3 TwoLocalBase)).mpr
      (degree_cyclotomic_pos 3 _ (by decide))
  let : NeZero (∏ i, p i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (Fact.out : (p i).Prime).ne_zero⟩
  let m := cyclotomic M TwoLocalQuadratic
  have hm : m.Monic := cyclotomic.monic _ _
  have hd : m.natDegree = M.totient := natDegree_cyclotomic _ _
  have he := Nat.totient_pos.mpr hM
  let b := jetPowerBasis hm hd he r
  have hdec (x : (Fin r × Fin M.totient) × Fin 2 → TwoLocalBase) (z : JetQuotient m r) :
      jetOperandValue φ₂ ω₂ m x = z ↔ ∀ i : Fin M.totient × Fin r,
        QuadraticDescent.decode φ₂ ω₂ (fun j => x ((j.1.2,j.1.1),j.2)) i = b.repr z i := by
    have h (i : Fin M.totient × Fin r) : b.repr (jetOperandValue φ₂ ω₂ m x) i =
        QuadraticDescent.decode φ₂ ω₂ (fun j => x ((j.1.2,j.1.1),j.2)) i :=
      jetPowerBasis_repr_value hm hd he r _ i
    constructor
    · rintro rfl i
      exact (h i).symm
    · intro hz
      exact b.repr.injective (DFunLike.ext _ _ fun i => (h i).trans (hz i))
  obtain ⟨a, d, q, t, f, j, hcost, hf, hj, hh⟩ := grid
  refine ⟨a, d, hcost, exists_openConvolution_of_grid φ₂ ω₂ atTwoCoefficientEncoding_bijective.injective
    m (fun i => atTwoJetCircuitsOver hM (hH i)) b _ _ (fun i k => jetPowerBasis_apply hm hd he r (i,k))
    hdec (primeResidues p cop) 1 (primeResidues_apply p cop) he hr hcap q t f j hf hj ?_⟩
  exact fun x y => (hh x y).trans (cyclicProduct_instance_independent _ _ _ _ _ _)

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
