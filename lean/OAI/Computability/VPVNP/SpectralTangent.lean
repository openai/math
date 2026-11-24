import OAI.Computability.VPVNP.WireGeodesic
import OAI.Computability.VPVNP.ConfigurationCompletion
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact

/-!
# Rescaling at a basepoint of a wire metric space

Lemma 4.1 passes to a simultaneous limit of rescaled configurations. An
ultrafilter tending to infinity takes that limit for all bounded marked
sequences at once. Its pseudometric retains every finite configuration when
the cone of spectral configurations is closed. Fractional points can be
chosen term by term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Filter Set Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- The rescaling factors at the successive terms of a marked sequence. -/
def tangentScale (n : ℕ) : ℝ := n + 1

theorem tangentScale_pos (n : ℕ) : 0 < tangentScale n := by unfold tangentScale; positivity

/-- The filter used for simultaneous convergence of all marked distances. -/
noncomputable def tangentFilter : Ultrafilter ℕ := Ultrafilter.of atTop

theorem tangentFilter_le_atTop : (tangentFilter : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

/-- Sequences at uniformly bounded rescaled distance from the basepoint. -/
structure Tangent (o : X) where
  /-- Sequence of marked points whose rescaled distances to the basepoint have a common upper
  bound. -/
  point : ℕ → X
  bounded : ∃ C : ℝ, ∀ n, tangentScale n * dist o (point n) ≤ C

variable {o : X}

private theorem bounded_pair (a b : Tangent o) :
    ∃ C : ℝ, ∀ n, tangentScale n * dist (a.point n) (b.point n) ≤ C := by
  obtain ⟨A, hA⟩ := a.bounded
  obtain ⟨B, hB⟩ := b.bounded
  refine ⟨A+B, fun n ↦ ?_⟩
  have ht := mul_le_mul_of_nonneg_left (dist_triangle (a.point n) o (b.point n))
    (tangentScale_pos n).le
  rw [dist_comm (a.point n) o, mul_add] at ht
  exact ht.trans (add_le_add (hA n) (hB n))

private noncomputable def tangentDist (a b : Tangent o) : ℝ :=
  limUnder tangentFilter (fun n ↦ tangentScale n * dist (a.point n) (b.point n))

private theorem tangentDist_tendsto (a b : Tangent o) :
    Tendsto (fun n ↦ tangentScale n * dist (a.point n) (b.point n)) tangentFilter
      (𝓝 (tangentDist a b)) := by
  obtain ⟨C, hC⟩ := bounded_pair a b
  let d (n : ℕ) := tangentScale n * dist (a.point n) (b.point n)
  have hI : Icc (0 : ℝ) C ∈ tangentFilter.map d := by
    change ∀ᶠ n : ℕ in (tangentFilter : Filter ℕ), d n ∈ Icc 0 C
    exact Eventually.of_forall fun n ↦ ⟨mul_nonneg (tangentScale_pos n).le dist_nonneg, hC n⟩
  obtain ⟨v, _, hv⟩ := isCompact_Icc.ultrafilter_le_nhds' (tangentFilter.map d) hI
  exact tendsto_nhds_limUnder ⟨v, hv⟩

noncomputable instance (o : X) : PseudoMetricSpace (Tangent o) where
  dist := tangentDist
  dist_self a := (tendsto_nhds_unique (tangentDist_tendsto a a) (by simp))
  dist_comm a b := by simp only [tangentDist, dist_comm (a.point _) (b.point _)]
  dist_triangle a b c := le_of_tendsto_of_tendsto (tangentDist_tendsto a c)
    ((tangentDist_tendsto a b).add (tangentDist_tendsto b c)) <| Eventually.of_forall fun n ↦ by
      simpa only [Pi.add_apply, ← mul_add] using
        mul_le_mul_of_nonneg_left (dist_triangle (a.point n) (b.point n) (c.point n))
          (tangentScale_pos n).le

/-- Rescaled distances converge to the distance in the tangent pseudometric. -/
theorem tangent_dist_tendsto (a b : Tangent o) :
    Tendsto (fun n ↦ tangentScale n * dist (a.point n) (b.point n)) tangentFilter (𝓝 (dist a b)) :=
  tangentDist_tendsto a b

theorem tangent_dist_eq_of_tendsto {a b : Tangent o} {v : ℝ}
    (h : Tendsto (fun n ↦ tangentScale n * dist (a.point n) (b.point n)) atTop (𝓝 v)) :
    dist a b = v :=
  tendsto_nhds_unique (tangent_dist_tendsto a b) (h.mono_left tangentFilter_le_atTop)

/-- A geodesic fraction can be taken independently at each term. -/
theorem tangent_hasFractions (hf : HasFractions X) (o : X) : HasFractions (Tangent o) := by
  intro a b t ht ht'
  choose p hp using fun n ↦ hf (a.point n) (b.point n) t ht ht'
  obtain ⟨A, hA⟩ := a.bounded
  obtain ⟨C, hC⟩ := bounded_pair a b
  have hbounded (n : ℕ) : tangentScale n * dist o (p n) ≤ A + t*C := by
    have htri := mul_le_mul_of_nonneg_left (dist_triangle o (a.point n) (p n)) (tangentScale_pos n).le
    rw [mul_add, (hp n).1, mul_left_comm] at htri
    exact htri.trans (add_le_add (hA n) (mul_le_mul_of_nonneg_left (hC n) ht))
  let q : Tangent o := ⟨p, A+t*C, hbounded⟩
  refine ⟨q, ?_, ?_⟩
  · apply tendsto_nhds_unique (tangent_dist_tendsto a q)
    exact ((tangent_dist_tendsto a b).const_mul t).congr fun n ↦ by simp [q, (hp n).1, mul_left_comm]
  · apply tendsto_nhds_unique (tangent_dist_tendsto q b)
    exact ((tangent_dist_tendsto a b).const_mul (1-t)).congr fun n ↦ by simp [q, (hp n).2, mul_left_comm]

/-- Finite configurations pass to the tangent space by closedness of each
realizable cone. The common positive scale absorbs the rescaling factor. -/
theorem tangent_realizableConfigurations {k : Type*} [Field k]
    (h : RealizableConfigurations k X) (o : X) : RealizableConfigurations k (Tangent o) := by
  intro n p
  apply (WireTensor.RealizableUpToScale.isClosed (k := k) (ι := Fin n)).mem_of_tendsto (f := fun i a b ↦
    tangentScale i * dist ((p a).point i) ((p b).point i)) (b := (tangentFilter : Filter ℕ))
  · exact tendsto_pi_nhds.mpr fun a ↦ tendsto_pi_nhds.mpr fun b ↦ tangent_dist_tendsto _ _
  · exact Eventually.of_forall fun i ↦ (h n (fun a ↦ (p a).point i)).smul (tangentScale_pos i)

end WireGeometry

end VPVNP
end Computability
end OAI
