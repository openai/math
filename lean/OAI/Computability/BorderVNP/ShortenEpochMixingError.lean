import OAI.Computability.BorderVNP.ShortenEpochMatching

/-!
# From finite-motion errors on individual segments to matched mean length

The finite motion table approximates the ideal bin law separately for each
original segment. A bin retains that segment's length. Hence the weighted
total variation of the count vector is bounded by the sum of the individual
variation errors times their respective widths and lengths. No independence
among segments within a pack is used.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Finset

variable {W B J : Type*} [Fintype W] [Fintype B] [Fintype J] [Nonempty J]

/-- Expected bin counts for a finite set of weighted segments. -/
noncomputable def binCounts (width : W → ℝ) (law : W → B → ℝ) (b : B) : ℝ :=
  ∑ w, width w * law w b

/-- The weighted variation of the whole-pack means is at most the sum of
the single-segment variations. -/
theorem binCounts_variation (width wireLength : W → ℝ) (binLength : B → ℝ)
    (p q : W → B → ℝ) {δ : ℝ} (hw : ∀ w, 0 ≤ width w) (hl : ∀ w, 0 ≤ wireLength w)
    (hb : ∀ b, 0 ≤ binLength b)
    (hsupp : ∀ w b, p w b ≠ q w b → binLength b = wireLength w)
    (hclose : ∀ w, ∑ b, |p w b - q w b| ≤ δ) :
    ∑ b, binLength b * |binCounts width p b - binCounts width q b| ≤
      δ * ∑ w, width w * wireLength w := by
  have hbin (b : B) : |binCounts width p b - binCounts width q b| ≤
      ∑ w, width w * |p w b - q w b| := by
    simp only [binCounts, ← sum_sub_distrib, ← mul_sub]
    exact (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl (fun w _ => by
      rw [abs_mul, abs_of_nonneg (hw w)]))
  calc
    _ ≤ ∑ b, binLength b * ∑ w, width w * |p w b - q w b| :=
      sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hbin b) (hb b)
    _ = ∑ w, width w * wireLength w * ∑ b, |p w b - q w b| := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro w _
      apply sum_congr rfl
      intro b _
      by_cases he : p w b = q w b
      · simp [he]
      · rw [hsupp w b he]; ring
    _ ≤ ∑ w, width w * wireLength w * δ := sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hclose w) (mul_nonneg (hw w) (hl w))
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Full weighted mean length is preserved when the law for each segment
is supported on bins of its own length. -/
theorem binCounts_length (width wireLength : W → ℝ) (binLength : B → ℝ)
    (q : W → B → ℝ) (hprob : ∀ w, ∑ b, q w b = 1)
    (hsupp : ∀ w b, q w b ≠ 0 → binLength b = wireLength w) :
    ∑ b, binLength b * binCounts width q b = ∑ w, width w * wireLength w := by
  simp_rw [binCounts, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  calc
    _ = ∑ b, (width w * wireLength w) * q w b := by
      apply sum_congr rfl
      intro b _
      by_cases h : q w b = 0
      · simp [h]
      · rw [hsupp w b h]; ring
    _ = _ := by rw [← mul_sum, hprob, mul_one]

/-- If every finite motion law approximates the invariant ideal law to
variation at most `1/(2D)`, at least half the full mean bit length is matched. -/
theorem half_mean_length_of_wire_mixing (A : J → Equiv.Perm B)
    (width wireLength : W → ℝ) (binLength : B → ℝ) (p q : W → B → ℝ)
    (hw : ∀ w, 0 ≤ width w) (hl : ∀ w, 0 ≤ wireLength w) (hb : ∀ b, 0 ≤ binLength b)
    (hlen : ∀ j b, binLength (A j b) = binLength b) (hprob : ∀ w, ∑ b, q w b = 1)
    (hp : ∀ w b, p w b ≠ 0 → binLength b = wireLength w)
    (hq : ∀ w b, q w b ≠ 0 → binLength b = wireLength w)
    (hinv : ∀ w j b, q w (A j b) = q w b)
    (hclose : ∀ w, ∑ b, |p w b - q w b| ≤ 1 / (2 * Fintype.card J)) :
    (∑ w, width w * wireLength w) / 2 ≤ matchedLength A binLength (binCounts width p) := by
  rw [← binCounts_length width wireLength binLength q hprob hq]
  apply half_length_le_matchedLength A binLength _ (binCounts width q) hb hlen
  · intro j b
    simp [binCounts, hinv]
  · have hsupport (w : W) (b : B) (hne : p w b ≠ q w b) : binLength b = wireLength w := by
      by_cases he : p w b = 0
      · exact hq w b (fun h => hne (he.trans h.symm))
      · exact hp w b he
    have hvar := binCounts_variation width wireLength binLength p q hw hl hb hsupport hclose
    have hmul := mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg (α := ℝ) (Fintype.card J))
    rw [binCounts_length width wireLength binLength q hprob hq]
    apply hmul.trans_eq
    have hD : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

end Epoch

end BorderVNP
end Computability
end OAI
