import OAI.Computability.VPVNP.DegreeRefreshMotif
import OAI.Computability.VPVNP.FlatteningWires
import OAI.Computability.VPVNP.GraphConnectivity
import OAI.Computability.VPVNP.MotifBlocks

/-!
# The expander supply motif of a degree refresh

Section 7.3 of *VP and VNP differ over every field* divides both arc masses
by the old arc mass. The two copies of the ordered port pairs then have
unit mass, and every directed expander arc has mass `D / d₀`. The Poincaré
bound for the spectral wire pseudometrics supplies the comparison required
by Theorem 6.1. The flattening spectral point also detects connectivity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

open SpectralGeometry WireTensor MotifGrid DegreeRefresh

variable {k : Type*} [Field k] {D dH d₀ : ℕ} {γ : ℝ}

/-- The common Poincaré bound for every labeling of the ports in every
spectral wire pseudometric on the port set. -/
def SpectralPortBound (k : Type*) [Field k] (G : RegularArcGraph (Fin D) dH) (γ : ℝ) : Prop :=
  ∀ F : SpectralPoint k (Fin D), letI := F.wirePseudoMetric
    HasPoincareBound (Fin D) (normalizeArcs G.multiplicity dH) γ

/-- The same Poincaré hypothesis implies connectivity and positivity of the
bound. The one-party flattening gives two ports at distance one. -/
theorem SpectralPortBound.connected_and_pos {G : RegularArcGraph (Fin D) dH}
    (hP : SpectralPortBound k G γ) (hD : 2 ≤ D) :
    (arcSupportGraph G.multiplicity).Connected ∧ 0 < γ := by
  let : Nontrivial (Fin D) := Fin.nontrivial_iff_two_le.mpr hD
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin D)
  let F := flatteningPoint (k := k) a
  let := F.wirePseudoMetric
  have hsep : 0 < dist a b := by
    change 0 < (flatteningPoint (k := k) a).wireDistance a b
    simp [flatteningPoint_wireDistance, hab]
  let P := normalizeArcs G.multiplicity dH
  have hn (i j : Fin D) : 0 ≤ P i j := by unfold P normalizeArcs; positivity
  have hs (i j : Fin D) : P i j = P j i := by
    simp only [P, normalizeArcs, G.multiplicity_symmetric i j]
  constructor
  · refine ⟨fun i j ↦ (arcSupportGraph_reachable_iff G.multiplicity G.multiplicity_symmetric i j).mpr ?_⟩
    apply Relation.ReflTransGen.mono _ i j (reachable_of_poincare a b hsep P hn hs (hP F) i j)
    intro u v h
    exact Nat.pos_of_ne_zero (fun hz ↦ by simp [P, normalizeArcs, hz] at h)
  · have hsquares : 0 < ∑ u, ∑ v, dist u v ^ 2 := Finset.sum_pos'
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
        ⟨b, Finset.mem_univ _, sq_pos_of_pos hsep⟩⟩
    have hwalk : 0 ≤ walkEnergy P id := Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (hn i j) (sq_nonneg _)
    have hprod : 0 < γ * walkEnergy P id :=
      (div_pos hsquares (Nat.cast_pos.mpr (Fintype.card_pos (α := Fin D)))).trans_le (hP F id)
    exact pos_of_mul_pos_left hprod hwalk

/-- Use every directed arc as one supply edge. Its source's first outgoing
slot is the local selector anchor. -/
def expanderSupply (G : RegularArcGraph (Fin D) dH) (hdH : 0 < dH)
    (hconn : (arcSupportGraph G.multiplicity).Connected) :
    MotifSelector.Supply (Fin D) (Fin D × Fin dH) where
  src := Prod.fst
  dst e := (G.reverse e).1
  anchor i := (i, ⟨0, hdH⟩)
  anchor_incident _ := Or.inl rfl
  connected u v := by
    have hpath := (arcSupportGraph_reachable_iff G.multiplicity G.multiplicity_symmetric u v).mp
      (hconn.preconnected u v)
    apply Relation.ReflTransGen.mono _ u v hpath
    intro i j hij
    obtain ⟨h, hh⟩ := (G.multiplicity_pos_iff i j).mp hij
    exact ⟨(i,h), Or.inl ⟨rfl, hh⟩⟩

/-- Each segment tie has unit mass after dividing out the old arc mass. -/
def tieMass (_ : Tie D) : ℚ := 1

/-- Each expander arc has mass equal to the ratio of the old degree to the new degree. -/
def expanderMass (d₀ : ℕ) (_ : Fin D × Fin dH) : ℚ := (D : ℚ) / d₀

/-- The common port bound gives the fixed-motif comparison with the paper's
constant `2 γ d₀ / dH`, independent of the order `D`. -/
theorem expander_distanceEnergy (G : RegularArcGraph (Fin D) dH) (hdH : 0 < dH)
    (hconn : (arcSupportGraph G.multiplicity).Connected) (hD : 0 < D) (hd₀ : 0 < d₀)
    (hP : SpectralPortBound k G γ) (F : SpectralPoint k (Fin D)) :
    distanceEnergy (realWidths tieMass) (fun t ↦ F.wireDistance (tieSource t) (tieTarget t)) ≤
      (2 * γ * d₀ / dH) * distanceEnergy (realWidths (expanderMass d₀))
        (fun e ↦ F.wireDistance ((expanderSupply G hdH hconn).src e) ((expanderSupply G hdH hconn).dst e)) := by
  have h := @metric_comparison D dH (Fin D) F.wirePseudoMetric G 1 ((D : ℝ) / d₀) d₀ γ hD zero_le_one
    (by field_simp [Nat.cast_ne_zero.mpr hd₀.ne']) (hP F) id
  simp only [distanceEnergy, realWidths, tieMass, expanderMass, Rat.cast_one, Rat.cast_div,
    Rat.cast_natCast]
  exact h

/-- Fix a single block of exact base identities and a uniform width-energy
error, with the slack `H' = H + 1` used at the degree refresh. -/
theorem exists_expander_block (G : RegularArcGraph (Fin D) dH) (hdH : 0 < dH)
    (hD : 2 ≤ D) (hd₀ : 0 < d₀) (hP : SpectralPortBound k G γ) :
    let P := expanderSupply G hdH (hP.connected_and_pos hD).1
    let H := 2 * γ * d₀ / dH
    Nonempty (MotifBlocks.FixedBlock k tieSource tieTarget P
      (realWidths tieMass) (realWidths (expanderMass d₀)) H (H + 1)) := by
  intro P H
  let : Nontrivial (Fin D) := Fin.nontrivial_iff_two_le.mpr hD
  obtain ⟨hconn, hγ⟩ := hP.connected_and_pos hD
  have hD' : 0 < D := by omega
  apply MotifBlocks.exists_fixed_block tieSource tieTarget P _ _
  · simp [realWidths, tieMass]
  · intro e
    simp only [realWidths, expanderMass, Rat.cast_div, Rat.cast_natCast]
    positivity
  · dsimp [H]
    positivity
  · linarith
  · exact expander_distanceEnergy G hdH hconn hD' hd₀ hP

end Compression.Refresh

end VPVNP
end Computability
end OAI
