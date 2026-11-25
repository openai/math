import OAI.Computability.BorderVNP.PackedDeckScoreMath
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.PUnit

/-! # Exact finite-candidate comparison before deck refinement

For different candidates the centered norm in §6 varies. A full first-level
score retains the sum of squares, the translated correlation and the rational
mean correction. Positive and negative integer numerators are kept separately.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate

open CoverDeck Finset

variable {B G : Type*} [Fintype B] [Fintype G] [Group G]

/-- The positive terms in the cleared-denominator score for one finite candidate. -/
def positive (D : ℕ) (A C : B → G → ℕ) : ℕ :=
  ∑ t, (D * Fintype.card G * (∑ g, C t g * C t g) +
    2*D*(∑ g, A t g)*(∑ g, C t g))

/-- Cleared-denominator contribution of the previously centered mean plus the current mean. -/
def negative (T : B → ℕ) (C : B → G → ℕ) : ℕ :=
  ∑ t, 2*Fintype.card G * T t * ∑ g, C t g

/-- The exact score of a candidate before its deck digits are exposed. -/
def uniformScore (A C : B → G → ℕ) (base mean : B → ℚ) : ℚ :=
  (∑ h, increment (fun b g => (A b g : ℚ) - base b)
    (fun b g => (C b g : ℚ)) mean h) / Fintype.card G

private theorem unshifted (A C : B → G → ℕ) (base mean : B → ℚ) :
    uniformScore A C base mean =
      ∑ t, ((∑ g, (((C t g : ℚ) - mean t)^2 - 2*((A t g : ℚ) - base t)*mean t)) +
        2*((∑ g, (C t g : ℚ)) * ((∑ g, (A t g : ℚ)) - Fintype.card G * base t) / Fintype.card G)) := by
  let π : G →* PUnit.{1} := 1
  have hπ : Function.Surjective π := fun v => ⟨1, Subsingleton.elim ..⟩
  have h := conditionalScore_eq π hπ (fun b g => (A b g : ℚ) - base b)
    (fun b g => (C b g : ℚ)) mean PUnit.unit
  have hf (u : PUnit.{1}) : fiber π u = Finset.univ := by ext; simp [fiber]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simpa only [uniformScore, conditionalScore, offset, residueMean, histogram, hf, Finset.card_univ,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Fintype.card_unique, Nat.cast_one, one_mul] using h.symm

omit [Fintype B] [Group G] in
private theorem squareSum (A C : G → ℕ) (base mean : ℚ) :
    (∑ g, (((C g : ℚ)-mean)^2 - 2*((A g : ℚ)-base)*mean)) =
      (∑ g, (C g : ℚ)*(C g : ℚ)) - 2*(∑ g, (C g : ℚ))*mean +
        (Fintype.card G : ℚ)*mean^2 - 2*((∑ g, (A g : ℚ)) - Fintype.card G * base)*mean := by
  have term (g) : (((C g : ℚ)-mean)^2 - 2*((A g : ℚ)-base)*mean) =
      ((C g : ℚ)*(C g : ℚ) - (C g : ℚ)*(2*mean) + mean^2) - ((A g : ℚ)-base)*(2*mean) := by ring
  simp only [term, sum_sub_distrib, sum_add_distrib, ← sum_mul, sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The exact rational score after multiplication by the common positive denominator
differs from the signed integer numerator by a candidate-independent constant. -/
theorem scaled_eq (D : ℕ) (T : B → ℕ) (A : B → G → ℕ) (base mean : B → ℚ)
    (hT : ∀ t, (D : ℚ)*(base t + mean t) = (T t : ℚ)) :
    ∃ K : ℚ, ∀ C : B → G → ℕ,
      (D : ℚ)*Fintype.card G * uniformScore A C base mean =
        K + ((positive D A C : ℕ) : ℚ) - ((negative T C : ℕ) : ℚ) := by
  let n : ℚ := Fintype.card G
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast (Fintype.card_pos (α := G)).ne'
  refine ⟨∑ t, (D : ℚ)*n*(n*mean t^2 - 2*((∑ g, (A t g : ℚ))-n*base t)*mean t), ?_⟩
  intro C
  rw [unshifted, positive, negative]
  simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [squareSum, ← hT t]
  change (D : ℚ)*n * (((∑ g, (C t g : ℚ)*(C t g : ℚ)) - 2*(∑ g, (C t g : ℚ))*mean t +
    n*mean t^2 - 2*((∑ g, (A t g : ℚ)) - n*base t)*mean t) +
    2*((∑ g, (C t g : ℚ))*((∑ g, (A t g : ℚ)) - n*base t)/n)) = _
  dsimp only [n] at hn ⊢
  field_simp
  ring

/-- Cross-addition of the two unsigned channels compares the complete rational scores. -/
theorem score_le_iff (D : ℕ) (hD : 0 < D) (T : B → ℕ) (A C C' : B → G → ℕ)
    (base mean : B → ℚ) (hT : ∀ t, (D : ℚ)*(base t+mean t) = T t) :
    uniformScore A C base mean ≤ uniformScore A C' base mean ↔
      positive D A C + negative T C' ≤ positive D A C' + negative T C := by
  obtain ⟨K,hK⟩ := scaled_eq D T A base mean hT
  have hn : (0:ℚ) < Fintype.card G := by exact_mod_cast (Fintype.card_pos (α := G))
  have hd : (0:ℚ) < D := by exact_mod_cast hD
  rw [← mul_le_mul_iff_right₀ (mul_pos hd hn), hK C, hK C']
  constructor
  · intro h
    exact_mod_cast (show ((positive D A C : ℕ) : ℚ) + negative T C' ≤
      ((positive D A C' : ℕ) : ℚ) + negative T C by linarith)
  · intro h
    have h' : ((positive D A C : ℕ) : ℚ) + negative T C' ≤ ((positive D A C' : ℕ) : ℚ) + negative T C := by
      exact_mod_cast h
    linarith

end PackedDeckCandidate

end BorderVNP
end Computability
end OAI
