import OAI.Computability.VPVNP.Compression
import OAI.Computability.VPVNP.RegularArcGraph
import OAI.Computability.VPVNP.GraphRounding

/-!
# Energy of the degree-restoring step

Section 7.3 of *VP and VNP differ over every field* concatenates all the old
wires over one base arc and replaces the segment ties in each block of ports
by a term of a fixed expander motif. There are two internal ties per ordered
pair of distinct ports. The external widths cost at most `d₀ L`; across all
blocks the internal demands cost at most `2 L`. The comparison constant
`2 γ d₀ / dH` for the metric motif is independent of the order of the block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.DegreeRefresh

open SpectralGeometry

variable {B : Type*} [Fintype B] {D dH : ℕ}

/-- The two copies distinguish the incoming and outgoing ties between ports. -/
abbrev Tie (D : ℕ) := Bool × {q : Fin D × Fin D // q.1 ≠ q.2}

/-- Old wires indexed in source-port order, before their concatenation. -/
abbrev Widths (B : Type*) (D : ℕ) := (B × Fin D) → Fin D → ℕ

/-- The width found at a destination block, incoming slot and destination port. -/
def incoming (target : Equiv.Perm (B × Fin D)) (lane : B × Fin D → Equiv.Perm (Fin D))
    (w : Widths B D) (e : B × Fin D) (j : Fin D) : ℕ :=
  w (target.symm e) ((lane (target.symm e)).symm j)

/-- In either direction the first port carries the old half-wire; the second
is the designated slot at which its segment of the external wire is read. -/
def tieWidth (target : Equiv.Perm (B × Fin D)) (lane : B × Fin D → Equiv.Perm (Fin D))
    (w : Widths B D) (z : B) (t : Tie D) : ℕ :=
  if t.1 then w (z,t.2.val.2) t.2.val.1 else incoming target lane w (z,t.2.val.2) t.2.val.1

/-- Squared-width energy of the old network. -/
noncomputable def oldEnergy (p : ℝ) (w : Widths B D) : ℝ :=
  ∑ e, ∑ i, (w e i : ℝ) ^ 2 / p

/-- Squared-width energy of the concatenated external payloads. -/
noncomputable def externalEnergy (p' : ℝ) (w : Widths B D) : ℝ :=
  ∑ e, ((∑ i, w e i : ℕ) : ℝ) ^ 2 / p'

/-- The energy of the two sets of nonlocal segment ties in a block. -/
noncomputable def demandEnergy (p : ℝ) (target : Equiv.Perm (B × Fin D))
    (lane : B × Fin D → Equiv.Perm (Fin D)) (w : Widths B D) (z : B) : ℝ :=
  ∑ t : Tie D, (tieWidth target lane w z t : ℝ) ^ 2 / p

/-- Reindexing the old energy at its incoming half-wires counts every width once. -/
theorem oldEnergy_incoming (target : Equiv.Perm (B × Fin D))
    (lane : B × Fin D → Equiv.Perm (Fin D)) (w : Widths B D) (p : ℝ) :
    oldEnergy p (incoming target lane w) = oldEnergy p w := by
  unfold oldEnergy incoming
  calc
    _ = ∑ e, ∑ j, (w (target.symm e) j : ℝ) ^ 2 / p :=
      Finset.sum_congr rfl fun e _ ↦ (lane (target.symm e)).symm.sum_comp _
    _ = _ := target.symm.sum_comp (fun e ↦ ∑ i, (w e i : ℝ) ^ 2 / p)

private theorem offDiagonal_le (f : Fin D × Fin D → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ u : {q : Fin D × Fin D // q.1 ≠ q.2}, f u.val) ≤ ∑ q, f q := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun q : Fin D × Fin D ↦ q.1 ≠ q.2) f
  exact (le_add_of_nonneg_right (Finset.sum_nonneg fun u _ ↦ hf u.val)).trans_eq h

/-- All internal ties together cost at most the old energy counted twice. Ties
at the same port are local and may be omitted even if their widths are positive. -/
theorem demandEnergy_sum_le (target : Equiv.Perm (B × Fin D))
    (lane : B × Fin D → Equiv.Perm (Fin D)) (w : Widths B D) {p : ℝ} (hp : 0 ≤ p) :
    (∑ z, demandEnergy p target lane w z) ≤ 2 * oldEnergy p w := by
  let total (z : B) (b : Widths B D) := ∑ j, ∑ i, (b (z,j) i : ℝ) ^ 2 / p
  have hlocal (z : B) : demandEnergy p target lane w z ≤
      total z w + total z (incoming target lane w) := by
    have haux (b : Widths B D) : (∑ u : {q : Fin D × Fin D // q.1 ≠ q.2},
        (b (z,u.val.2) u.val.1 : ℝ) ^ 2 / p) ≤ total z b := by
      refine (offDiagonal_le (fun q ↦ (b (z,q.2) q.1 : ℝ) ^ 2 / p)
        (fun _ ↦ div_nonneg (sq_nonneg _) hp)).trans_eq ?_
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa [demandEnergy, Fintype.sum_prod_type, Fintype.sum_bool, tieWidth] using
      add_le_add (haux w) (haux (incoming target lane w))
  have h := Finset.sum_le_sum (s := Finset.univ) fun z _ ↦ hlocal z
  have htotal (b : Widths B D) : ∑ z, total z b = oldEnergy p b := by
    rw [oldEnergy, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, htotal, htotal, oldEnergy_incoming, ← two_mul] at h
  exact h

/-- Cauchy–Schwarz bounds the external energy after concatenating the `D`
segments of each bundle, using `D p = d₀ p'`. -/
theorem externalEnergy_le (w : Widths B D) {p p' d₀ : ℝ}
    (hp : 0 < p) (hp' : 0 < p') (hmass : (D : ℝ) * p = d₀ * p') :
    externalEnergy p' w ≤ d₀ * oldEnergy p w := by
  unfold externalEnergy oldEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin D ↦ (1 : ℝ)) (fun i ↦ (w e i : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  rw [Nat.cast_sum]
  apply (div_le_iff₀ hp').mpr
  calc
    _ ≤ (D : ℝ) * ∑ i, (w e i : ℝ) ^ 2 := h
    _ = _ := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      field_simp [hp.ne']
      linarith only [congrArg (fun z : ℝ ↦ z * ∑ i, (w e i : ℝ) ^ 2) hmass]

private theorem offDiagonal_dist_eq {X : Type*} [PseudoMetricSpace X] (x : Fin D → X) :
    (∑ u : {q : Fin D × Fin D // q.1 ≠ q.2}, dist (x u.val.1) (x u.val.2) ^ 2) =
      ∑ u, ∑ v, dist (x u) (x v) ^ 2 := by
  let f (q : Fin D × Fin D) := dist (x q.1) (x q.2) ^ 2
  have hz : (∑ u : {q : Fin D × Fin D // ¬q.1 ≠ q.2}, f u.val) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    simp [f, not_not.mp u.property]
  have h := Fintype.sum_subtype_add_sum_subtype (fun q : Fin D × Fin D ↦ q.1 ≠ q.2) f
  rw [hz, add_zero, Fintype.sum_prod_type] at h
  exact h

/-- The metric hypothesis of the expander motif in Section 7.3, with the actual
directed arcs as supply and two copies of the off-diagonal as demand. -/
theorem metric_comparison {X : Type*} [PseudoMetricSpace X]
    (G : RegularArcGraph (Fin D) dH) {p p' d₀ γ : ℝ}
    (hD : 0 < D) (hp : 0 ≤ p) (hmass : (D : ℝ) * p = d₀ * p')
    (hbound : HasPoincareBound X (normalizeArcs G.multiplicity dH) γ) (x : Fin D → X) :
    (∑ t : Tie D, p * dist (x t.2.val.1) (x t.2.val.2) ^ 2) ≤
      (2 * γ * d₀ / dH) * ∑ e : Fin D × Fin dH, p' * dist (x e.1) (x (G.reverse e).1) ^ 2 := by
  have hwalk : walkEnergy (normalizeArcs G.multiplicity dH) x =
      (∑ e : Fin D × Fin dH, dist (x e.1) (x (G.reverse e).1) ^ 2) / dH := by
    rw [G.sum_cost (fun a b ↦ dist (x a) (x b) ^ 2)]
    simp only [walkEnergy, normalizeArcs, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [dist_comm (x v) (x u)]
    ring
  have hD' : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hb := hbound x
  rw [Fintype.card_fin, hwalk] at hb
  have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hD').mp hb) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp)
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [← Finset.mul_sum, offDiagonal_dist_eq]
  refine le_trans (le_of_eq (by ring)) (h.trans_eq ?_)
  calc
    _ = (2 * γ / (dH : ℝ)) * ((D : ℝ) * p) * ∑ e : Fin D × Fin dH, dist (x e.1) (x (G.reverse e).1) ^ 2 := by ring
    _ = _ := by rw [hmass]; ring

/-- Summing the termwise energy inequality of Theorem 6.1 over all blocks
gives Equation (7.3). The additive term is exactly `C · P²` when the motif's
scaled additive constant is `C` and `P = #blocks · D`. -/
theorem refresh_energy_le (target : Equiv.Perm (B × Fin D))
    (lane : B × Fin D → Equiv.Perm (Fin D)) (w : Widths B D) (supply : B → ℝ)
    {p p' d₀ H' C : ℝ} (hp : 0 < p) (hp' : 0 < p') (hH : 0 ≤ H')
    (hmass : (D : ℝ) * p = d₀ * p') (hold : 1 / p = (Fintype.card B : ℝ) * D * D)
    (hterm : ∀ z, supply z ≤ H' * demandEnergy p target lane w z + C / p) :
    externalEnergy p' w + ∑ z, supply z ≤
      (d₀ + 2 * H') * oldEnergy p w + C * ((Fintype.card B : ℝ) * D) ^ 2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun z _ ↦ hterm z
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  have hinc := mul_le_mul_of_nonneg_left (demandEnergy_sum_le target lane w hp.le) hH
  have hconst : (Fintype.card B : ℝ) * (C / p) = C * ((Fintype.card B : ℝ) * D) ^ 2 := by
    rw [show C / p = C * (1 / p) by ring, hold]
    ring
  rw [hconst] at hs
  linarith only [externalEnergy_le w hp hp' hmass, hs, hinc]

end Compression.DegreeRefresh

end VPVNP
end Computability
end OAI
