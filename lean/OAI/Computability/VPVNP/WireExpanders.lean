import OAI.Computability.VPVNP.Expanders
import OAI.Computability.VPVNP.GraphConnectivity
import OAI.Computability.VPVNP.SpectralCubeObstruction

/-!
# Common expanders for spectral wire pseudometrics

In Corollary 5.2 the class of complete CAT(0) targets consists of spaces whose
finite distance configurations are realizable by wires over the given field.
Closedness upgrades exact cube exclusion to uniform exclusion throughout the
class. Theorem 5.1 then provides a single graph at each selected order. Its
Poincaré bound pulls back to every labeling by parties of every spectral point.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open WireTensor WireGeometry Grassmann

private structure WireTarget (k : Type*) [Field k] where
  carrier : Type
  metric : MetricSpace carrier
  complete : CompleteSpace carrier
  realizable : RealizableConfigurations k carrier
  comparison : HasCATZeroSegments carrier

attribute [local instance] WireTarget.metric WireTarget.complete

/-- Connected loopless regular graphs of arbitrarily large power-of-two orders
have the same power-of-two degree and Poincaré bound for all spectral wire
pseudometrics over the field. Arc multiplicities come from port reversal. -/
def HasWireExpanders (k : Type*) [Field k] : Prop :=
  ∃ (e : ℕ) (γ : ℝ), 0 < γ ∧ ∀ minimum : ℕ, ∃ o : ℕ, minimum ≤ 2 ^ o ∧
    ∃ G : RegularArcGraph (Fin (2 ^ o)) (2 ^ e), (arcSupportGraph G.multiplicity).Connected ∧
      ∀ (J : Type) [Fintype J] (F : SpectralPoint k J),
        letI := F.wirePseudoMetric
        HasPoincareBound J (normalizeArcs G.multiplicity (2 ^ e)) γ

/-- Exact exclusion of one cube over the field implies the common graph
family of Corollary 5.2, with all its bounds uniform over the spectral points. -/
theorem wire_expanders_of_cube_exclusion (k : Type*) [Field k] {ℓ : ℕ}
    (hexclude : ¬ RealizableUpToScale k (cubeDistances ℓ)) : HasWireExpanders k := by
  classical
  let Y := WireTarget.carrier (k := k)
  have hclosed : cubeDistances ℓ ∉ closure (markedDistances Y (Finset (Fin ℓ))) := by
    apply RealizableUpToScale.notMem_closure_markedDistances Y _ hexclude
    intro a x
    let v := Fintype.equivFin (Finset (Fin ℓ))
    simpa only [Equiv.symm_apply_apply] using
      (a.realizable _ (fun i ↦ x (v.symm i))).relabel v
  obtain ⟨e, γ, hγ, hgraphs⟩ := expanders_of_cube_exclusion Y WireTarget.comparison hclosed
  refine ⟨e, γ, hγ, fun minimum ↦ ?_⟩
  obtain ⟨o, ho, M, hsym, hloop, hrow, hreach, hbound⟩ := hgraphs minimum
  obtain ⟨G, hG, hconnected⟩ := exists_connected_regularArcGraph M hsym hrow hloop hreach
  refine ⟨o, ho, G, hconnected, fun J _ F ↦ ?_⟩
  let : PseudoMetricSpace J := F.wirePseudoMetric
  intro x
  rw [hG]
  rcases subsingleton_or_nontrivial J with hJ | hJ
  · have hz (i j) : dist (x i) (x j) = 0 := by rw [Subsingleton.elim (x i) (x j), dist_self]
    simp [walkEnergy, hz]
  · obtain ⟨X, hX, hcomplete, p, hp, hr, hc⟩ := F.exists_catZero_completion
    let a : WireTarget k := ⟨X, hX, hcomplete, hr, hc⟩
    have h := hbound a (p ∘ x)
    change (∑ i, ∑ j, dist (p (x i)) (p (x j)) ^ 2) / Fintype.card (Fin (2 ^ o)) ≤
      γ * walkEnergy (normalizeArcs M (2 ^ e)) (p ∘ x) at h
    change (∑ i, ∑ j, F.wireDistance (x i) (x j) ^ 2) / Fintype.card (Fin (2 ^ o)) ≤
      γ * ∑ i, ∑ j, normalizeArcs M (2 ^ e) i j * F.wireDistance (x j) (x i) ^ 2
    simpa only [walkEnergy, Function.comp_apply, hp] using h

/-- Corollary 5.2. Infinitely many small exact circuits for the integer
family over a fixed field provide one common expander family for its wire
pseudometrics. The excluded dimension can be chosen after the circuit exponent. -/
theorem wire_expanders_of_small_circuits (k : Type*) [Field k] {C : ℕ} (hC : 1 ≤ C)
    (hsmall : ∀ N, ∃ n ≥ N, circuitSize (MvPolynomial.map (Int.castRingHom k) (P n)) ≤ n ^ C) :
    HasWireExpanders k :=
  wire_expanders_of_cube_exclusion k (cube_obstruction k hC le_rfl hsmall)

end SpectralGeometry

end VPVNP
end Computability
end OAI
