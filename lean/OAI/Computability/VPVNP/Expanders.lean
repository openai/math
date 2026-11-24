import OAI.Computability.VPVNP.ExpanderOrders
import OAI.Computability.VPVNP.SparseGrassmannFamily
import OAI.Computability.VPVNP.GrassmannInequality
import OAI.Computability.VPVNP.WalkDenominators

/-!
# Expanders from uniform exclusion of a Euclidean cube

Theorem 5.1 of *VP and VNP differ over every field*. The strict Grassmann
inequality supplies a sparse family with growth exponent below the plane
dimension. Choose the iteration count first, then the starting size, so the
resulting port graph admits both smoothing and an integral port matching.
Cloud replacement and the loopless double give fixed degree and Poincaré
bound at arbitrarily large power-of-two orders.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

universe u

variable {κ : Type*} (Y : κ → Type u) [∀ i, PseudoMetricSpace (Y i)]

open Grassmann

private theorem choosePortGraph {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hcat : ∀ k, HasCATZeroSegments (Y k))
    (hexclude : cubeDistances ℓ ∉ closure (markedDistances Y (Finset (Fin ℓ)))) :
    ∃ (s e n : ℕ) (β : ℝ) (H : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℕ),
      0 < s ∧ 0 < n ∧ 1 ≤ β ∧ 1776 * β ≤ 2 * (n : ℝ) ∧
      (2 * n) * (2 * (2 * 2 ^ e)) ^ (2 * n) ∣ 2 ^ s ∧
      (∀ i j, H i j = H j i) ∧ (∀ i, ∑ j, H i j = 2 ^ e) ∧
      ∀ a, HasPoincareBound (Y a) (normalizeArcs H (2 ^ e)) β := by
  let r := ℓ
  have hr : 0 < r := by dsimp [r]; omega
  have hm : ℓ < 2 ^ r := Nat.lt_two_pow_self
  obtain ⟨η, hη, hgap⟩ := strict_grassmann_bound Y hm hcat hexclude
  obtain ⟨α, C', hα, hsmall, _, hgraphs⟩ := exists_sparse_rounded_family Y (by omega : 1 < 2 ^ r)
    (sub_lt_self _ hη) hgap
  push_cast at hsmall
  obtain ⟨j, k, hk, hfour, hβ⟩ := exists_walk_smoothing_scale r hr hα.le hsmall C'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨Cj, _, hCj⟩ := hgraphs j
  obtain ⟨d, _, hd₂, hdvd⟩ := exists_walk_port_order (k+1) Cj 2
  have hd : 0 < d := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hd₂
  let s := d * ((2 ^ r) ^ j)
  have hs : 0 < s := Nat.mul_pos hd (pow_pos (pow_pos (by decide) _) _)
  have hsize : ((2 ^ d) ^ ((2 ^ r) ^ j) : ℕ) = 2 ^ s := (pow_mul _ _ _).symm
  have h := hCj d hd
  rw [hsize] at h
  obtain ⟨e, he, H, hsym, hrow, hH⟩ := h
  have hdiv := hdvd (e+1) (by rw [pow_succ']; nlinarith only [he])
  rw [← hfour, hsize, pow_succ' 2 e, pow_succ' 2 k] at hdiv
  let β := max 1 (2 * C' * α ^ j)
  refine ⟨s, e, 2 ^ k, β, H, hs, by positivity, le_max_left _ _, ?_, hdiv, hsym, hrow, ?_⟩
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ'] using hβ
  · intro a x
    apply (hH a x).trans
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (show 0 ≤ normalizeArcs H (2 ^ e) i j by unfold normalizeArcs; positivity)
        (sq_nonneg _)

/-- Theorem 5.1. The vertex sets are `Fin (2 ^ o)` and the integral arc
multiplicities describe connected loopless symmetric `2 ^ e`-regular
multigraphs. The degree and the Poincaré constant precede the order bound
and work for every space in the original class. -/
theorem expanders_of_cube_exclusion [∀ a, CompleteSpace (Y a)] {ℓ : ℕ}
    (hcat : ∀ a, HasCATZeroSegments (Y a))
    (hexclude : cubeDistances ℓ ∉ closure (markedDistances Y (Finset (Fin ℓ)))) :
    ∃ (e : ℕ) (γ : ℝ), 0 < γ ∧ ∀ minimum : ℕ, ∃ o : ℕ, minimum ≤ 2 ^ o ∧
      ∃ G : Matrix (Fin (2 ^ o)) (Fin (2 ^ o)) ℕ, (∀ i j, G i j = G j i) ∧
        (∀ i, G i i = 0) ∧ (∀ i, ∑ j, G i j = 2 ^ e) ∧
        (∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < G a b) i j) ∧
        ∀ a, HasPoincareBound (Y a) (normalizeArcs G (2 ^ e)) γ := by
  let I := {a : κ // Nonempty (Y a)}
  let X : I → Type u := fun i ↦ Y i.val
  let (i : I) : Nonempty (X i) := i.property
  have hx : cubeDistances ℓ ∉ closure (markedDistances X (Finset (Fin ℓ))) := by
    intro h
    apply hexclude
    refine closure_mono ?_ h
    rintro _ ⟨a, s, hs, x, rfl⟩
    exact ⟨a.val, s, hs, x, rfl⟩
  let L := max 2 ℓ
  have hL : 2 ≤ L := le_max_left _ _
  have hex := withRealLine_cube_exclusion X hL (cube_exclusion_mono X (le_max_right _ _) hx)
  have hcat' := withRealLine_hasCATZeroSegments X (fun a ↦ hcat a.val)
  obtain ⟨s, e, n, β, H, hs, hn, hβ, ht, hdiv, hsym, hrow, hH⟩ :=
    choosePortGraph (withRealLine X) hL hcat' hex
  refine ⟨e+2, 6 + 12 * (444 * β), by linarith only [hβ], fun minimum ↦ ?_⟩
  obtain ⟨o, ho, G, hsym', hloop, hrow', hconn, hbound⟩ :=
    exists_expander_orders (withRealLine X) hs hn H hsym hrow hβ ht hdiv hcat' hH none
      (fun a ↦ ULift.up a) (fun _ _ ↦ rfl) minimum
  refine ⟨o, ho, G, hsym', hloop, hrow', hconn, fun a x ↦ ?_⟩
  have ha : Nonempty (Y a) := ⟨x ⟨0, pow_pos (by decide) _⟩⟩
  exact hbound (some ⟨a, ha⟩) x

end SpectralGeometry

end VPVNP
end Computability
end OAI
