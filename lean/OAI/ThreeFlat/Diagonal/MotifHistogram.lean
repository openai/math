import OAI.ThreeFlat.Diagonal.MotifPayload

namespace OAI
/-! # A fixed number of histogram words per motif

Counting occurrences of each base selector gives a branch format whose
admission test sums a fixed number of integers. Supply lengths are dot
products with the fixed tile table. Histograms having the same resulting
widths still partition disjoint sets of selector sequences.
-/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open scoped BigOperators Classical

variable {H S : Type*} [Fintype H] [DecidableEq H] {r : ℕ}

abbrev Histogram (H : Type*) [Fintype H] (r : ℕ) := {a : H → Fin (r+1) // ∑ i, (a i).val = r}

def occurrence (t : Fin r → H) (i : H) : ℕ := ∑ j, if t j = i then 1 else 0

private theorem occurrence_dot (t : Fin r → H) (v : H → ℕ) :
    (∑ h, occurrence t h * v h) = ∑ j, v (t j) := by
  simp only [occurrence, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

def histogram (t : Fin r → H) : Histogram H r :=
  ⟨fun h => ⟨occurrence t h, Nat.lt_succ_of_le (by
    calc
      occurrence t h ≤ ∑ _j : Fin r, 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> omega
      _ = r := by simp)⟩,
   by simpa using occurrence_dot t (fun _ => 1)⟩

def histWidth (w : H → S → ℕ) (h : Histogram H r) (e : S) := ∑ i, (h.1 i).val * w i e

theorem histogram_width (w : H → S → ℕ) (t : Fin r → H) (e : S) :
    histWidth w (histogram t) e = totalWidth w t e := occurrence_dot t _

omit [DecidableEq H] in
theorem histogram_norm [Fintype S] (w : H → S → ℕ) (q : S → ℝ) (hq : ∀ e, 0 < q e)
    {R : ℝ} (base : ∀ h, Computability.VPVNP.MotifGrid.widthNorm q (fun e => (w h e : ℝ)) ≤ R)
    (h : Histogram H r) : Computability.VPVNP.MotifGrid.widthNorm q (fun e => (histWidth w h e : ℝ)) ≤ r * R := by
  let f (i : H) (e : S) : ℝ := (h.1 i).val * (w i e : ℝ)
  have eqn (e : S) : (histWidth w h e : ℝ) = ∑ i, f i e := by simp [histWidth, f]
  simp_rw [eqn]
  calc
    _ ≤ ∑ i, Computability.VPVNP.MotifGrid.widthNorm q (f i) := Computability.VPVNP.MotifWidths.widthNorm_sum_le q hq _
    _ ≤ ∑ i, ((h.1 i).val : ℝ) * R := Finset.sum_le_sum fun i _ => by
      dsimp only [f]
      rw [Computability.VPVNP.MotifGrid.widthNorm_scale q _ (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (base i) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum, h.2]

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
