import OAI.Computability.BorderVNP.CrossingNetwork
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Parallel products of placed networks

The indexed disjoint union of networks contracts to their ordinary tensor
product on separate external ports. Its length is the sum of the lengths of
the constituents. Multiplication by a scalar changes only one local table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped BigOperators
variable {D : ℕ} {P I : Type} [Fintype I] {bits : P → ℕ} {K : Type*} [CommSemiring K]

/-- Disjoint union of the sites, cables and external slots of the factors. -/
def parallel (N : I → Network D P bits) : Network D (I × P) (fun ip => bits ip.2) where
  Site := Σ i, (N i).Site
  Edge := Σ i, (N i).Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := ⟨e.1, (N e.1).src e.2⟩
  dst e := ⟨e.1, (N e.1).dst e.2⟩
  width e := (N e.1).width e.2
  attach ip := ⟨ip.1, (N ip.1).attach ip.2⟩
  position v := (N v.1).position v.2
  in_ball v := (N v.1).in_ball v.2

/-- Each constituent reads its own tagged cables and ports in the union. -/
def parallelTables (N : I → Network D P bits) (T : ∀ i, (N i).Tables K) :
    (parallel N).Tables K := fun v a x =>
  T v.1 v.2 (fun e => a ⟨⟨v.1, e.val⟩, e.property.imp
    (congrArg (Sigma.mk v.1)) (congrArg (Sigma.mk v.1))⟩)
    (fun p => x ⟨(v.1, p.val), congrArg (Sigma.mk v.1) p.property⟩)

/-- Independent tensor contraction is multiplication on disjoint external slots. -/
theorem parallel_value (N : I → Network D P bits) (T : ∀ i, (N i).Tables K)
    (x : Ports (fun ip : I × P => bits ip.2)) :
    (parallel N).value (parallelTables N T) x = ∏ i, (N i).value (T i) (fun p => x (i,p)) := by
  classical
  let e : (parallel N).Assignment ≃ (∀ i, (N i).Assignment) := Equiv.piCurry fun i (b : (N i).Edge) => Fin ((N i).width b) → Bool
  unfold value
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv e
  intro a
  apply Fintype.prod_sigma

/-- Length is additive under independent parallel use of the cables. -/
theorem parallel_cost (N : I → Network D P bits) : (parallel N).cost = ∑ i, (N i).cost :=
  Fintype.sum_sigma _

/-- Parallel factors retain the locations of their external slots. -/
theorem parallel_placedAt (N : I → Network D P bits) {p : P → EuclideanSpace ℝ (Fin D)}
    (hp : ∀ i, (N i).PlacedAt p) : (parallel N).PlacedAt (fun ip => p ip.2) := fun ip =>
  hp ip.1 ip.2

/-- Put the scalar at one local site without changing any cable. -/
noncomputable def scaleTable (N : Network D P bits) (v : N.Site) (c : K) (T : N.Tables K) :
    N.Tables K := by
  classical
  exact fun u a x => (if u = v then c else 1) * T u a x

/-- Scaling a single local table multiplies the whole tensor by that scalar. -/
theorem value_scaleTable (N : Network D P bits) (v : N.Site) (c : K) (T : N.Tables K)
    (x : Ports bits) : N.value (N.scaleTable v c T) x = c * N.value T x := by
  classical
  simp only [value, read, scaleTable, Finset.prod_mul_distrib, Finset.mul_sum]
  simp

end Crossing.Network

end BorderVNP
end Computability
end OAI
