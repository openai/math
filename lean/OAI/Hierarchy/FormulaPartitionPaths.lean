import OAI.Hierarchy.FormulaPartitionStep
import OAI.Hierarchy.FormulaDepth
import Mathlib.Data.Finsupp.Weight

namespace OAI
/-! # Heavy-child expansion of every arithmetic formula -/

namespace Hierarchy.FormulaPartition
open ABPFirstCut MvPolynomial
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V] [Fintype V]

/-- A root-to-leaf walk remembers its kernel at every ancestor. -/
structure Route (V : Type) (τ : V → Type) (F : Type*) [Field F] [DecidableEq V] where
  steps : List (Kernel V τ F)
  tip : Leaf V τ F

private def linearLeaf (p : MvPolynomial (Σ i, τ i) F) (degree : p.totalDegree ≤ 1) :
    Leaf V τ F where
  value a S := slotCoeff a S p
  small := by
    intro a S nz
    have bound := le_totalDegree (mem_support_iff.mpr nz)
    change (slotExponent a S).degree ≤ p.totalDegree at bound
    have selected : (slotExponent a S).degree = S.card := by
      simp [slotExponent, Finsupp.degree_single]
    exact selected ▸ bound.trans degree
  locality := fun _ _ S same => slotCoeff_congr S same p

def Route.prepend (k : Kernel V τ F) (r : Route V τ F) : Route V τ F :=
  ⟨k :: r.steps, r.tip⟩

private def joinRoutes (k l : Kernel V τ F) (g h : List (Route V τ F)) :=
  g.map (Route.prepend k) ++ h.map (Route.prepend l)

def routes : Formula F (Σ i, τ i) → List (Route V τ F)
  | .constant c => [⟨[], linearLeaf (C c) (by simp)⟩]
  | .input v => [⟨[], linearLeaf (X v) (by simp)⟩]
  | .add g h => joinRoutes (sumStep 1) (sumStep 1) (routes g) (routes h)
  | .sub g h => joinRoutes (sumStep 1) (sumStep (-1)) (routes g) (routes h)
  | .mul g h => joinRoutes (productStep true (Formula.polynomial h)) (productStep false (Formula.polynomial g))
      (routes g) (routes h)

omit [Fintype V] in
theorem length_routes (f : Formula F (Σ i, τ i)) : (routes f).length = f.cost+1 := by
  induction f with
  | constant _ | input _ => rfl
  | add g h ih jh | sub g h ih jh | mul g h ih jh =>
    simp only [routes, joinRoutes, List.length_append, List.length_map,
      MatrixMultiplication.Arithmetic.Expression.cost, ih, jh]
    omega

omit [Fintype V] in
private theorem depth_join {g h : List (Route V τ F)} (k l : Kernel V τ F) {m n : ℕ}
    (hg : ∀ r ∈ g, r.steps.length ≤ m) (hh : ∀ r ∈ h, r.steps.length ≤ n) :
    ∀ r ∈ joinRoutes k l g h, r.steps.length ≤ max m n+1 := by
  intro r member
  rcases List.mem_append.mp member with one | two
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp one
    exact Nat.succ_le_succ ((hg e he).trans (le_max_left _ _))
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp two
    exact Nat.succ_le_succ ((hh e he).trans (le_max_right _ _))

omit [Fintype V] in
theorem route_length_le_depth (f : Formula F (Σ i, τ i)) :
    ∀ r ∈ routes f, r.steps.length ≤ Formula.depth f := by
  induction f with
  | constant c | input c => simp [routes, Formula.depth]
  | add g h ig ih | sub g h ig ih | mul g h ig ih => exact depth_join _ _ ig ih

def routeSum (a : ∀ v, τ v) (rs : List (Route V τ F)) (S : Finset V) : F :=
  (rs.map fun r => run a r.tip r.steps S).sum

private theorem prepend_sum (a : ∀ v, τ v) (k : Kernel V τ F) (rs : List (Route V τ F)) (S : Finset V) :
    routeSum a (rs.map (Route.prepend k)) S = k.act a (routeSum a rs) S := by
  induction rs with
  | nil => simp [routeSum, Kernel.act]
  | cons r rs ih =>
    change k.act a (run a r.tip r.steps) S + routeSum a (rs.map (Route.prepend k)) S = _
    rw [ih]
    simp only [Kernel.act, routeSum, List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]

private theorem join_sum (a : ∀ v, τ v) (k l : Kernel V τ F)
    (g h : List (Route V τ F)) (S : Finset V) :
    routeSum a (joinRoutes k l g h) S = k.act a (routeSum a g) S + l.act a (routeSum a h) S := by
  change (((g.map (Route.prepend k) ++ h.map (Route.prepend l)).map _).sum) = _
  rw [List.map_append, List.sum_append]
  exact congrArg₂ (·+·) (prepend_sum a k g S) (prepend_sum a l h S)

/-- Every coefficient is the sum of the root-to-leaf walks. In a product the
two terms split the convolution by the larger of the two child slot counts. -/
theorem slotCoeff_routes (a : ∀v,τ v) (f : Formula F (Σ i, τ i)) :
    ∀ S, slotCoeff a S f.polynomial = routeSum a (routes f) S := by
  induction f with
  | constant _ | input _ =>
    intro S
    simp [routes, routeSum, run, linearLeaf, Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial]
  | add g h ig ih =>
    intro S
    rw [routes, join_sum, sumStep_act, sumStep_act, one_mul, one_mul, ← ig, ← ih]
    simp [slotCoeff, Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial]
  | sub g h ig ih =>
    intro S
    rw [routes, join_sum, sumStep_act, sumStep_act, one_mul, neg_one_mul, ← ig, ← ih, ← sub_eq_add_neg]
    simp [slotCoeff, Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial]
  | mul g h ig ih =>
    intro S
    rw [routes, join_sum, ← funext ig, ← funext ih]
    exact product_step_eq a S (Formula.polynomial g) (Formula.polynomial h)


end
end Hierarchy.FormulaPartition

end OAI
