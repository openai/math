import OAI.Computability.VPVNP.GrassmannCompactness
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Enlarging a class of targets by the real line

In Section 5.1 of *VP and VNP differ over every field*, uniform exclusion
passes to every larger cube by restriction to a face. In dimension at least
two the real line can then be included among the targets. Every triple on
the real line satisfies a closed polynomial identity on its distances, while
three corners of a Euclidean square violate that identity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set
open scoped symmDiff

universe u

variable {κ : Type*} (X : κ → Type u) [∀ k, PseudoMetricSpace (X k)]

/-- Euclidean distances between the corners of the unit cube. -/
noncomputable def cubeDistances (ℓ : ℕ) (A B : Finset (Fin ℓ)) : ℝ :=
  √((A ∆ B).card : ℝ)

theorem cube_exclusion_mono {ℓ L : ℕ} (h : ℓ ≤ L)
    (hQ : cubeDistances ℓ ∉ closure (markedDistances X (Finset (Fin ℓ)))) :
    cubeDistances L ∉ closure (markedDistances X (Finset (Fin L))) := by
  let e := Fin.castLEEmb h
  let f := fun (D : Finset (Fin L) → Finset (Fin L) → ℝ) (A B : Finset (Fin ℓ)) =>
    D (A.map e) (B.map e)
  have hf : MapsTo f (markedDistances X _) (markedDistances X _) := by
    rintro _ ⟨k, s, hs, x, rfl⟩
    exact ⟨k, s, hs, fun A => x (A.map e), rfl⟩
  have hc : Continuous f := by dsimp [f]; fun_prop
  have heq : f (cubeDistances L) = cubeDistances ℓ := by
    ext A B
    have hdiff : (A ∆ B).map e = A.map e ∆ B.map e := by
      simp only [Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff]
    simp only [f, cubeDistances, ← hdiff, Finset.card_map]
  exact fun hmem => hQ (heq ▸ hf.closure hc hmem)

/-- Add the real line at the extra index `none`. -/
def withRealLine (X : κ → Type u) : Option κ → Type u
  | none => ULift.{u} ℝ
  | some k => X k

instance (k : Option κ) : PseudoMetricSpace (withRealLine X k) := by
  cases k <;> unfold withRealLine <;> infer_instance

instance [∀ k, CompleteSpace (X k)] (k : Option κ) : CompleteSpace (withRealLine X k) := by
  cases k <;> unfold withRealLine <;> infer_instance

instance [∀ k, Nonempty (X k)] (k : Option κ) : Nonempty (withRealLine X k) := by
  cases k <;> unfold withRealLine <;> infer_instance

theorem withRealLine_hasCATZeroSegments (hcat : ∀ k, SpectralGeometry.HasCATZeroSegments (X k)) :
    ∀ k, SpectralGeometry.HasCATZeroSegments (withRealLine X k) := by
  intro k
  cases k with
  | some k => exact hcat k
  | none =>
    intro x y t _ _
    refine ⟨ULift.up ((1 - t) * x.down + t * y.down), fun z => ?_⟩
    change dist z.down ((1 - t) * x.down + t * y.down) ^ 2 ≤
      (1 - t) * dist z.down x.down ^ 2 + t * dist z.down y.down ^ 2 -
        t * (1 - t) * dist x.down y.down ^ 2
    simp only [Real.dist_eq, sq_abs]
    exact le_of_eq (by ring)

/-- On the line a triple has zero squared area. This is a closed condition
on ordinary distances, including after any choice of scale. -/
private theorem line_triple_closure {J : Type*} {D : J → J → ℝ}
    (hD : D ∈ closure (markedDistances (fun _ : Unit => ℝ) J)) (a b c : J) :
    (D a c ^ 2 - D a b ^ 2 - D b c ^ 2) ^ 2 = 4 * D a b ^ 2 * D b c ^ 2 := by
  let S : Set (J → J → ℝ) := {A | (A a c ^ 2 - A a b ^ 2 - A b c ^ 2) ^ 2 =
    4 * A a b ^ 2 * A b c ^ 2}
  have hclosed : IsClosed S := isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (t := S) _ hclosed hD
  rintro _ ⟨_, s, _, x, rfl⟩
  simp only [S, mem_ofPred_eq, Real.dist_eq, mul_pow, sq_abs]
  ring

/-- The Euclidean square has a right triangle of side lengths `1`, `1`, `√2`. -/
theorem realLine_cube_exclusion {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    cubeDistances ℓ ∉ closure (markedDistances (fun _ : Unit => ℝ) (Finset (Fin ℓ))) := by
  apply cube_exclusion_mono (fun _ : Unit => ℝ) hℓ
  intro hD
  have h := line_triple_closure hD {0} ∅ {1}
  have h2 : (({0} : Finset (Fin 2)) ∆ {1}).card = 2 := by decide
  have h1 : (({0} : Finset (Fin 2)) ∆ ∅).card = 1 := by decide
  have h1' : ((∅ : Finset (Fin 2)) ∆ {1}).card = 1 := by decide
  simp only [cubeDistances, Real.sq_sqrt (Nat.cast_nonneg _), h1, h1', h2] at h
  norm_num at h

/-- Marked arrays for the enlarged class are the union of the two classes
of arrays, so uniform exclusion in dimension at least two is preserved. -/
theorem withRealLine_cube_exclusion {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hQ : cubeDistances ℓ ∉ closure (markedDistances X (Finset (Fin ℓ)))) :
    cubeDistances ℓ ∉ closure (markedDistances (withRealLine X) (Finset (Fin ℓ))) := by
  have hs : markedDistances (withRealLine X) (Finset (Fin ℓ)) ⊆
      markedDistances X _ ∪ markedDistances (fun _ : Unit => ℝ) _ := by
    rintro _ ⟨k, s, hs, x, rfl⟩
    cases k with
    | none => exact Or.inr ⟨(), s, hs, fun A => (x A).down, rfl⟩
    | some k => exact Or.inl ⟨k, s, hs, x, rfl⟩
  intro hmem
  have h := closure_mono hs hmem
  rw [closure_union] at h
  exact h.elim hQ (realLine_cube_exclusion hℓ)

end Grassmann

end VPVNP
end Computability
end OAI
