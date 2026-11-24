import OAI.Computability.VPVNP.MotifBase
import OAI.Computability.VPVNP.MotifIntegralWires
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Integral equations for the fixed motif maps

For each point of the demand grid in Theorem 6.1, impose its base tensor
identity in every output coordinate. Distinct entries of the selected local
maps are separate indeterminates. The equations can thus be specialized in
any commutative ring, using the same integer tensors and the same bases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifParameters

open WireTensor MvPolynomial

universe v w x y

/-- Integral arrays and the selectors indexing their local images. -/
structure Data (J : Type v) (Z : Type w) where
  /-- Finite type of admissible supply selections for a given demand grid point. -/
  Selector : Z → Type x
  finiteSelector : ∀ z, Fintype (Selector z)
  /-- Integer tensor to be expanded at the chosen demand grid point. -/
  demand : Z → Tensor.{0,v,y} ℤ J
  /-- Integer supply tensor used by one selector in the local-map expansion of the demand
  tensor. -/
  supply : (z : Z) → Selector z → Tensor.{0,v,y} ℤ J

attribute [instance] Data.finiteSelector

namespace Data

variable {J Z : Type*} (G : Data J Z)

/-- Each grid point, selector, party, row and column specifies one variable. -/
abbrev Entry := (z : Z) × (t : G.Selector z) × (j : J) ×
  (G.demand z).Basis j × (G.supply z t).Basis j

/-- One equation for every joint output coordinate at every grid point. -/
abbrev Output := (z : Z) × ((j : J) → (G.demand z).Basis j)

instance [Finite Z] [Finite J] : Finite G.Entry := by
  unfold Entry
  infer_instance

instance [Finite Z] [Finite J] : Finite G.Output := by
  unfold Output
  infer_instance

/-- The local matrices read from a single parameter assignment. -/
def localMap {R : Type*} (κ : G.Entry → R) (z : Z) (t : G.Selector z) (j : J)
    (a : (G.demand z).Basis j) (b : (G.supply z t).Basis j) : R := κ ⟨z, t, j, a, b⟩

variable [Fintype J]

/-- Difference of the two sides of a base identity at one output coordinate. -/
noncomputable def equation (o : G.Output) : MvPolynomial G.Entry ℤ :=
  C ((G.demand o.1).coeff o.2) - ∑ t,
    applyLocal (G.localMap X o.1 t) (fun b ↦ C ((G.supply o.1 t).coeff b)) o.2

/-- Simultaneous vanishing of the integral equations. -/
def IsSolution {R : Type*} [CommRing R] (κ : G.Entry → R) : Prop :=
  ∀ o : G.Output, eval₂Hom (Int.castRingHom R) κ (G.equation o) = 0

/-- Evaluating a base equation contracts the actual local matrices over the
ring of the assignment. -/
theorem eval_equation {R : Type*} [CommRing R] (κ : G.Entry → R) (o : G.Output) :
    eval₂Hom (Int.castRingHom R) κ (G.equation o) =
      ((G.demand o.1).coeff o.2 : R) - ∑ t, applyLocal (G.localMap κ o.1 t)
        (fun b ↦ ((G.supply o.1 t).coeff b : R)) o.2 := by
  classical
  simp only [equation, applyLocal, localMap, map_sub, map_sum, map_mul, map_prod,
    eval₂Hom_X', eval₂Hom_C]
  rfl

/-- Specialization of all the equations is equivalent to all the ordinary sum
identities, as equalities of arrays in the original demand bases. -/
theorem solution_iff {R : Type*} [CommRing R] (κ : G.Entry → R) :
    G.IsSolution κ ↔ ∀ z, (fun a ↦ ((G.demand z).coeff a : R)) =
      ∑ t, applyLocal (G.localMap κ z t) (fun b ↦ ((G.supply z t).coeff b : R)) := by
  constructor
  · intro h z
    funext a
    simpa only [eval_equation, sub_eq_zero, Finset.sum_apply] using h ⟨z, a⟩
  · intro h o
    simpa only [eval_equation, sub_eq_zero, Finset.sum_apply] using congrFun (h o.1) o.2

/-- Base identities at individual grid points give a single simultaneous
solution by assigning their matrix entries to their own variables. -/
theorem exists_solution {R : Type*} [CommRing R]
    (h : ∀ z, ∃ L : ∀ (t : G.Selector z) (j : J), (G.demand z).Basis j →
        (G.supply z t).Basis j → R,
      (fun a ↦ ((G.demand z).coeff a : R)) =
        ∑ t, applyLocal (L t) (fun b ↦ ((G.supply z t).coeff b : R))) :
    ∃ κ : G.Entry → R, G.IsSolution κ := by
  choose L hL using h
  let κ : G.Entry → R := fun ⟨z, t, j, a, b⟩ ↦ L z t j a b
  exact ⟨κ, (G.solution_iff κ).2 hL⟩

end Data

section WireBases

variable {J Z W : Type*} {D S : Type} [Fintype D] [Fintype S] [Fintype W]
variable (a b : D → J) (c d : S → J) (z : Z → D → ℕ) (w : W → S → ℕ) (K h : ℕ)

/-- The fixed integral tensors for the selectors in the spectral comparison. -/
noncomputable def wireData : Data J Z where
  Selector _ := Fin K × (Fin h → W)
  finiteSelector _ := inferInstance
  demand i := wireNetwork a b (fun e ↦ Fin (2 ^ (h * z i e)))
  supply _ σ := wireNetwork c d (fun e ↦ Fin (2 ^ MotifBase.payload w σ.2 e))

variable [Fintype J]

/-- Specialization recovers the binary wire identities over the assignment's
ring. All their matrix indices are taken in the original wire bases. -/
theorem wire_solution_iff {R : Type*} [CommRing R]
    (κ : (wireData a b c d z w K h).Entry → R) :
    (wireData a b c d z w K h).IsSolution κ ↔ ∀ i,
      (wireNetwork (k := R) a b (fun e ↦ Fin (2 ^ (h * z i e)))).coeff =
        ∑ σ : Fin K × (Fin h → W), applyLocal
          (B := ((wireData a b c d z w K h).supply i σ).Basis)
          ((wireData a b c d z w K h).localMap κ i σ)
          (wireNetwork (k := R) c d (fun e ↦ Fin (2 ^ MotifBase.payload w σ.2 e))).coeff := by
  rw [Data.solution_iff]
  apply forall_congr' fun i ↦ ?_
  have hd := intCast_wireNetwork_coeff_fun R a b (fun e ↦ Fin (2 ^ (h * z i e)))
  have hs (σ : Fin K × (Fin h → W)) := intCast_wireNetwork_coeff_fun R c d
    (fun e ↦ Fin (2 ^ MotifBase.payload w σ.2 e))
  simp_rw [← hd, ← hs]
  rfl

/-- Spectral base identities over the chosen field supply all the parameters
of a single integral equation system at once. -/
theorem exists_wire_solution {k : Type*} [Field k]
    (base : ∀ i, MotifBase.BaseIdentity k a b c d (z i) w K h) :
    ∃ κ : (wireData a b c d z w K h).Entry → k, (wireData a b c d z w K h).IsSolution κ := by
  choose L hL using base
  let κ : (wireData a b c d z w K h).Entry → k := fun ⟨i, σ, j, r, s⟩ ↦ L i σ j r s
  exact ⟨κ, (wire_solution_iff a b c d z w K h κ).2 hL⟩

end WireBases

/-- Counting repeated parameter indices gives the exponent vector of one
matrix entry in the repeated local map. -/
noncomputable def entryExponents {V : Type*} {u : ℕ} (i : Fin u → V) : V →₀ ℕ :=
  ∑ r, Finsupp.single (i r) 1

/-- A product of base entries, including repetitions, is one monomial with
coefficient one. The empty product also satisfies this formula. -/
theorem prod_entries_eq_monomial {V : Type*} {u : ℕ} (i : Fin u → V) :
    (∏ r, X (i r) : MvPolynomial V ℤ) = monomial (entryExponents i) 1 :=
  (monomial_sum_one Finset.univ (fun r ↦ Finsupp.single (i r) 1)).symm

/-- One selected base entry per copy contributes at most one degree per copy. -/
theorem prod_entries_degree_le {V : Type*} {u : ℕ} (i : Fin u → V) :
    (∏ r, X (i r) : MvPolynomial V ℤ).totalDegree ≤ u := by
  simpa using totalDegree_finsetProd Finset.univ (fun r ↦ (X (i r) : MvPolynomial V ℤ))

end MotifParameters

end VPVNP
end Computability
end OAI
