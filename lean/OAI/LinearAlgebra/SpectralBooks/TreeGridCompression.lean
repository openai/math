import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundIdentity
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementCatalogueCircuit
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.GridAllFamilies
import OAI.LinearAlgebra.SpectralBooks.TreeProfileShortening
import OAI.LinearAlgebra.SpectralBooks.IndependentSetHardness

/-! # Uniform planar compression and the independent-set obstruction to the tree case

One patch cutoff and one list overhead work for all map orders and all
old widths at the chosen reduction factor. The joint arithmetic program
therefore gives the actual one-step recurrence for all universal tables.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

open PortGraph PortGraph.ReplacementChoices Arithmetic.RecursiveBlock MvPolynomial
open UniformDecorations Arithmetic Filter
open scoped Classical

variable {F : Type} [Field F]

/-- Under the tree hypothesis, the polynomial for all connected spherical
maps with at most `n` vertices is obtained by substituting one computed
table into the polynomial with cap `max 1 (n/a)`. -/
theorem uniform_rounds_of_tree (tree : ¬ HasNonTreeWireMetric F)
    (a : ℕ) (ha : 2 ≤ a) :
    ∃ D : ℕ, ∀ n w : ℕ, 1 < n → 0 < w →
      ∃ w' : ℕ, 0 < w' ∧ w' ≤ 10*w+D*Nat.clog 2 (2*n) ∧
      ∃ p : Family F (Address w) (Address w'), p.cost ≤ 2^(D*(w+Nat.clog 2 (2*n))) ∧
        Zpoly n w = bind₁ (familyPolynomial p) (Zpoly (max 1 (n/a)) w') := by
  have ha' : 0 < a := by omega
  let ε : ℝ := 1 / (2 * (a : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨K,hK,sys⟩ := exists_positive_systems ε hε
  have noPlane : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) :=
    fun ⟨P⟩ => tree (hasNonTreeWireMetric_of_spectralPlane P)
  obtain ⟨c,cat⟩ := ShapeCatalogue.nonempty_of_noPlane noPlane hK
  refine ⟨roundConstant K c (max 1 (4*K)) (PatchShape.entryExponent K),?_⟩
  intro n w hn hw
  have hn' : 0 < n := by omega
  obtain ⟨C⟩ := cat w
  exact C.circuit hn' hw (C.Zpoly_eq_acceptedWeight (sys n hn') ha' rfl (C.encodeRole n hn' ε))

/-- The numeric recurrence uses the minimum circuit cost of the concrete
universal polynomial at every order and width. -/
theorem gridTableCompression_of_tree (tree : ¬ HasNonTreeWireMetric F)
    (a : ℕ) (ha : 2 ≤ a) :
    ∃ b : GridTableCompression a, ∀ n w, b.cost n w = polynomialProgramCost (Zpoly (F:=F) n w) := by
  obtain ⟨C,hr⟩ := uniform_rounds_of_tree tree a ha
  let D := max C (Fintype.card (MapClass 1)+4)
  refine ⟨gridTableCompressionOfCircuits (Zpoly (F:=F)) a D ?_ ?_,fun _ _ => rfl⟩
  · intro w _
    exact (Zpoly_one_cost w).trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (le_max_right ..)))
  · intro n w hn hw
    obtain ⟨v,hv,hsize,p,hcost,h⟩ := hr n w hn hw
    have hCD : C ≤ D := le_max_left ..
    exact ⟨v,hv,hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hCD) _),
      p,hcost.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hCD)),h⟩

/-- Every bipartite graph family of growing order has pinned circuits with the
width and gate bounds of uniform compression in the tree case. -/
theorem grid_compress_of_tree (tree : ¬ HasNonTreeWireMetric F)
    (m k : ℕ → ℕ) (E : ∀ n, Fin (m n) → Fin (k n) → Prop)
    (order : ∀ᶠ n : ℕ in atTop, m n + k n = n) :
    ∀ a : ℕ, 2 ≤ a → ∃ b : GridTableCompression a,
      ∀ᶠ n : ℕ in atTop, ∃ W : ℕ, 0 < W ∧
        (W:ℝ) ≤ b.widthConstant * Real.log (2 * ((m n * k n + 2*n : ℕ):ℝ)) ∧
        ∃ (r : ℕ) (p : Program F ((Fin (m n) ⊕ Fin (k n)) × Bool) r) (o : Fin r),
          registerPolynomial p o = IndependentSetGrid.contraction (E n)
            (fun i s => X (Sum.inl i,s)) (fun _ _ => 1)
            (fun j s => X (Sum.inr j,s)) (fun _ _ => 1) ∧
          (p.cost : ℝ) ≤ (2:ℝ)^(b.pinConstant * Real.log (2 * ((m n * k n + 2*n : ℕ):ℝ))) +
            b.cost (m n * k n + 2*n) W :=
  grid_compress_of_rounds (uniform_rounds_of_tree tree) m k E order

/-- A stretched-exponentially hard subcubic bipartite graph family forces a
finite tensor spectrum to violate the four-point tree inequality. -/
theorem hasNonTreeWireMetric_of_hardSubcubicGrids [Infinite F]
    {δ : ℝ} (hδ : 0 < δ) (hard : HardSubcubicGrids F δ) : HasNonTreeWireMetric F := by
  by_contra tree
  obtain ⟨G,hG⟩ := hard
  let m := fun n => (G n).m
  let k := fun n => (G n).k
  let edge := fun n => (G n).edge
  have order : ∀ᶠ n : ℕ in atTop, m n + k n = n := Eventually.of_forall (fun n => (G n).order)
  exact independentSetGrid_contradiction m k edge order (grid_compress_of_tree tree m k edge order) hδ hG

end

end

end SpectralBooks
end LinearAlgebra
end OAI
