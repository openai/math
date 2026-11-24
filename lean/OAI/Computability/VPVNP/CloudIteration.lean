import OAI.Computability.VPVNP.CloudReplacement
import OAI.Computability.VPVNP.GraphRounding
import OAI.Computability.VPVNP.LayerWalk
import OAI.Computability.VPVNP.PortWalkRealization

/-!
# Iterating cloud replacement at a fixed degree

Section 5.3 of *VP and VNP differ over every field* iterates the replacement
starting at a single vertex. All targets in the given family share the same
sequence of integer adjacency matrices. For a port graph with bound `β ≥ 1`,
the explicit bound `444 * β` is preserved when `t ≥ 1776 * β`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V K X : Type*} [Fintype V] [Fintype K] [PseudoMetricSpace X]

/-- Poincaré bounds are independent of vertex labels. -/
theorem hasPoincareBound_equiv (e : V ≃ K) (P : Matrix V V ℝ) {γ : ℝ}
    (hP : HasPoincareBound X P γ) :
    HasPoincareBound X (fun i j ↦ P (e.symm i) (e.symm j)) γ := by
  intro x
  have hpair :
      (∑ i : V, ∑ j : V, dist (x (e i)) (x (e j)) ^ 2) =
        ∑ i : K, ∑ j : K, dist (x i) (x j) ^ 2 := by
    apply Fintype.sum_equiv e
    intro i
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  have hedge :
      walkEnergy P (fun i ↦ x (e i)) =
        walkEnergy (fun i j ↦ P (e.symm i) (e.symm j)) x := by
    unfold walkEnergy
    apply Fintype.sum_equiv e
    intro i
    apply Fintype.sum_equiv e
    simp
  simpa only [hpair, Fintype.card_congr e, hedge] using hP (fun i ↦ x (e i))

omit [Fintype V] [Fintype K] in
/-- Normalizing the integer replacement by its degree gives the equal mixture
of internal moves and matching moves. -/
theorem normalize_replacementArcs [DecidableEq V] [DecidableEq K] (H : Matrix K K ℕ)
    (σ : Equiv.Perm (V × K)) {h : ℕ} (hh : 0 < h) :
    normalizeArcs (replacementArcs H σ h) (2 * h) = cloudWalk (normalizeArcs H h) σ := by
  ext p q
  have hh' : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
  simp only [normalizeArcs, replacementArcs, cloudWalk, Nat.cast_mul, Nat.cast_ofNat,
    eq_comm (a := q.1) (b := p.1), eq_comm (a := q) (b := σ p)]
  split_ifs <;> push_cast <;> field_simp <;> ring

variable {T : Type*} (Y : T → Type*) [∀ a, PseudoMetricSpace (Y a)]
  [∀ a, CompleteSpace (Y a)] [∀ a, Nonempty (Y a)]

/-- One amplification step on integral regular multigraphs. The matching,
hence the resulting graph, works simultaneously for every target. -/
theorem exists_cloudStep [DecidableEq V] [Nonempty V] {Q h n : ℕ}
    (hQ : 0 < Q) (hh : 0 < h) (hn : 0 < n)
    (H : Matrix (Fin Q) (Fin Q) ℕ) (hHs : ∀ i j, H i j = H j i)
    (hHr : ∀ i, ∑ j, H i j = h)
    (G : Matrix V V ℕ) (hGs : ∀ i j, G i j = G j i)
    (hGr : ∀ i, ∑ j, G i j = 2 * h)
    {β : ℝ} (hβ : 1 ≤ β) (ht : 1776 * β ≤ 2 * (n : ℝ))
    (hdiv : (2 * n) * (2 * (2 * h)) ^ (2 * n) ∣ Q)
    (hcat : ∀ a, HasCATZeroSegments (Y a))
    (hH : ∀ a, HasPoincareBound (Y a) (normalizeArcs H h) β)
    (hG : ∀ a, HasPoincareBound (Y a) (normalizeArcs G (2 * h)) (444 * β)) :
    ∃ G' : Matrix (V × Fin Q) (V × Fin Q) ℕ, (∀ i j, G' i j = G' j i) ∧
      (∀ i, ∑ j, G' i j = 2 * h) ∧
      ∀ a, HasPoincareBound (Y a) (normalizeArcs G' (2 * h)) (444 * β) := by
  let : NeZero Q := ⟨hQ.ne'⟩
  have hb : 0 < 2 * h := by omega
  have hn' : 0 < 2 * n := by omega
  let P := normalizeArcs G (2 * h)
  obtain ⟨σ, hi, port, _⟩ := exists_cesaroPortMatching G hb hn' hQ hGs hGr hdiv
  refine ⟨replacementArcs H σ h, replacementArcs_symmetric H hHs σ hi h,
    replacementArcs_degree H h hHr σ, ?_⟩
  intro a
  rw [normalize_replacementArcs H σ hh]
  have hpos (v w : V) : 0 ≤ P v w := by unfold P normalizeArcs; positivity
  have hrow (v : V) : ∑ w, P v w = 1 := normalizeArcs_row_sum G hb v (hGr v)
  have hcol (w : V) : ∑ v, P v w = 1 := by
    have sym (v : V) : P v w = P w v := by simp only [P, normalizeArcs, hGs v w]
    simp only [sym]
    exact hrow w
  have hbound := cesaroWalk_hasPoincareBound (hcat a) P hpos hrow hcol
    (show 0 ≤ 444 * β by linarith only [hβ]) (hG a) hn
  have hmax : max 12 (48 * (444 * β) / (2 * (n : ℝ))) = 12 := by
    apply max_eq_left
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [ht])
  rw [hmax] at hbound
  have hS : HasPoincareBound (Y a) (portWalk σ) 12 := port ▸ hbound
  convert cloudWalk_hasPoincareBound (normalizeArcs H h) σ hβ (by norm_num : (0 : ℝ) ≤ 12)
    (hH a) hS using 1
  ring

/-- Starting with a single vertex and `2h` loops, repeated cloud replacement
gives orders `Q^j`, keeping both degree and Poincaré bound independent of `j`. -/
theorem exists_iteratedCloudGraph {Q h n : ℕ} (hQ : 0 < Q) (hh : 0 < h) (hn : 0 < n)
    (H : Matrix (Fin Q) (Fin Q) ℕ) (hHs : ∀ i j, H i j = H j i)
    (hHr : ∀ i, ∑ j, H i j = h) {β : ℝ} (hβ : 1 ≤ β)
    (ht : 1776 * β ≤ 2 * (n : ℝ)) (hdiv : (2 * n) * (2 * (2 * h)) ^ (2 * n) ∣ Q)
    (hcat : ∀ a, HasCATZeroSegments (Y a))
    (hH : ∀ a, HasPoincareBound (Y a) (normalizeArcs H h) β) (j : ℕ) :
    ∃ G : Matrix (Fin (Q ^ j)) (Fin (Q ^ j)) ℕ, (∀ u v, G u v = G v u) ∧
      (∀ u, ∑ v, G u v = 2 * h) ∧
      ∀ a, HasPoincareBound (Y a) (normalizeArcs G (2 * h)) (444 * β) := by
  induction j with
  | zero =>
    refine ⟨fun _ _ ↦ 2 * h, fun _ _ ↦ rfl, ?_, ?_⟩
    · intro _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, pow_zero, one_nsmul]
    intro a x
    have hall (i j : Fin (Q ^ 0)) : i = j := by
      have hi := i.isLt
      have hj := j.isLt
      simp only [pow_zero] at hi hj
      exact Fin.ext (by omega)
    have hd (i j : Fin (Q ^ 0)) : dist (x i) (x j) = 0 := by rw [hall i j, dist_self]
    simp only [walkEnergy, hd, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero,
      zero_div, le_refl]
  | succ j ih =>
    obtain ⟨G, hs, hr, hg⟩ := ih
    let : NeZero (Q ^ j) := ⟨(pow_pos hQ j).ne'⟩
    obtain ⟨G', hs', hr', hg'⟩ :=
      exists_cloudStep Y hQ hh hn H hHs hHr G hs hr hβ ht hdiv hcat hH hg
    let e : (Fin (Q ^ j) × Fin Q) ≃ Fin (Q ^ (j + 1)) :=
      Fintype.equivFinOfCardEq (by simp [pow_succ])
    refine ⟨fun u v ↦ G' (e.symm u) (e.symm v), fun _ _ ↦ hs' _ _, ?_, ?_⟩
    · intro u
      exact (Equiv.sum_comp e.symm (G' (e.symm u))).trans (hr' (e.symm u))
    · exact fun a ↦ hasPoincareBound_equiv e _ (hg' a)

/-- The double cover of each iterated graph has no loops and has a common
Poincaré bound for the entire target family. Its order and degree are twice
those of the iterated graph. -/
theorem exists_looplessCloudGraph {Q h n : ℕ} (hQ : 0 < Q) (hh : 0 < h) (hn : 0 < n)
    (H : Matrix (Fin Q) (Fin Q) ℕ) (hHs : ∀ i j, H i j = H j i)
    (hHr : ∀ i, ∑ j, H i j = h) {β : ℝ} (hβ : 1 ≤ β)
    (ht : 1776 * β ≤ 2 * (n : ℝ)) (hdiv : (2 * n) * (2 * (2 * h)) ^ (2 * n) ∣ Q)
    (hcat : ∀ a, HasCATZeroSegments (Y a))
    (hH : ∀ a, HasPoincareBound (Y a) (normalizeArcs H h) β) (j : ℕ) :
    ∃ G : Matrix (Fin (2 * Q ^ j)) (Fin (2 * Q ^ j)) ℕ, (∀ u v, G u v = G v u) ∧
      (∀ u, ∑ v, G u v = 4 * h) ∧ (∀ u, G u u = 0) ∧
      ∀ a, HasPoincareBound (Y a) (normalizeArcs G (4 * h)) (6 + 12 * (444 * β)) := by
  obtain ⟨G, hs, hr, hb⟩ := exists_iteratedCloudGraph Y hQ hh hn H hHs hHr hβ ht hdiv hcat hH j
  let : NeZero (Q ^ j) := ⟨(pow_pos hQ j).ne'⟩
  let e : (Fin (Q ^ j) × Bool) ≃ Fin (2 * Q ^ j) := Fintype.equivFinOfCardEq (by simp [mul_comm])
  let G' := layerArcs G (2 * h)
  refine ⟨fun u v ↦ G' (e.symm u) (e.symm v), fun _ _ ↦ layerArcs_symmetric G hs _ _ _,
    ?_, fun _ ↦ layerArcs_no_loops G _ _, ?_⟩
  · intro u
    rw [Equiv.sum_comp e.symm (G' (e.symm u))]
    exact (layerArcs_degree G _ hr _).trans (by omega)
  · intro a
    let P := normalizeArcs G (2 * h)
    have hnP (i j) : 0 ≤ P i j := by unfold P normalizeArcs; positivity
    have hsP (i j) : P i j = P j i := by simp only [P, normalizeArcs, hs i j]
    have hcP (j) : ∑ i, P i j = 1 := by
      simp only [fun i ↦ hsP i j]
      exact normalizeArcs_row_sum G (by omega) j (hr j)
    have hnorm : normalizeArcs G' (4 * h) = layerWalk P := by
      ext p q
      change (layerArcs G (2 * h) p q : ℝ) / (4 * h : ℕ) =
        layerWalk (fun u v ↦ (G u v : ℝ) / (2 * h : ℕ)) p q
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simpa only [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]
        using layerArcs_normalize G (show 0 < 2 * h by omega) p q
    apply hasPoincareBound_equiv e (normalizeArcs G' (4 * h))
    rw [hnorm]
    exact layerWalk_hasPoincareBound P hnP hsP hcP (by linarith only [hβ]) (hb a)

end SpectralGeometry

end VPVNP
end Computability
end OAI
