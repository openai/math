import OAI.Computability.BorderVNP.PackedDeckCandidateMath
import OAI.Computability.BorderVNP.PackedDeckMeanMath
import OAI.Computability.BorderVNP.ShortenEpochConcentration

/-! # The true score increment controls the next pack's contribution to (6.2)

The candidate selector and the deck refinement together give an increment no
larger than the full one-pack expectation. Averaging the cross term cancels it
against the actual pack mean, even though all cable bits of the pack move
together. The squared norm of the mean is then subtracted from the raw budget.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckEnergy

open CoverDeck PackedDeckCandidate Finset

variable {B G J : Type*} [Fintype B] [Fintype G] [Group G] [Fintype J]

/-- Squared norm on the tile and relative-bin arrays, in exact rational arithmetic. -/
def energy (f : B → G → ℚ) : ℚ := ∑ b, ∑ g, (f b g)^2

/-- Squared norm of the current centered counts in the physical bank. -/
def bankEnergy (A : B → G → ℕ) (base : B → ℚ) := energy (fun b g => (A b g : ℚ) - base b)

/-- One pack's raw second-moment budget, using only the finite candidates. Deck translation
preserves each candidate's raw squared norm. -/
def rawBudget (prob : J → ℚ) (C : J → B → G → ℕ) : ℚ :=
  ∑ j, prob j * energy (fun b g => (C j b g : ℚ))

private def sampleWeight (prob : J → ℚ) (s : J × G) : ℚ := prob s.1 / Fintype.card G

private theorem mass (prob : J → ℚ) (hp : ∑ j, prob j = 1) : ∑ s : J × G, sampleWeight prob s = 1 := by
  have hn : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  simpa [sampleWeight, Fintype.sum_prod_type, nsmul_eq_mul, mul_div_cancel₀ _ hn, hn] using hp

omit [Fintype B] in
private theorem firstMoment (prob : J → ℚ) (C : J → B → G → ℕ) (b : B) (x : G) :
    (∑ s : J × G, sampleWeight prob s * C s.1 b (s.2*x)) = PackedDeckMean.mean prob C b 1 := by
  rw [PackedDeckMean.mean_eq prob C b 1, ← PackedDeckMean.mean_eq prob C b x]
  simp only [sampleWeight, Fintype.sum_prod_type, ← Finset.mul_sum, div_eq_mul_inv, PackedDeckMean.mean]
  apply sum_congr rfl
  intro j _
  ring

private theorem scalarVariance {S : Type*} [Fintype S] (p f : S → ℚ) (μ z : ℚ)
    (hp : ∑ s, p s = 1) (hf : ∑ s, p s*f s = μ) :
    (∑ s, p s*((f s-μ)^2 + 2*z*(f s-μ))) = (∑ s, p s*(f s)^2) - μ^2 := by
  have ht (s : S) : p s*((f s-μ)^2+2*z*(f s-μ)) =
      p s*(f s)^2 + (p s*f s)*(2*z-2*μ) + p s*(μ^2-2*z*μ) := by ring
  simp only [ht, sum_add_distrib, ← sum_mul, hf, hp, one_mul]
  ring

private theorem translate_energy (C : B → G → ℕ) (h : G) :
    energy (fun b g => (C b (h*g) : ℚ)) = energy (fun b g => (C b g : ℚ)) := by
  unfold energy
  apply sum_congr rfl
  intro b _
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => (C b g : ℚ)^2)

/-- The expected rational increment is the raw budget minus exactly the squared pack mean.
In particular, prior centered counts make no contribution to this expectation. -/
theorem average_increment (prob : J → ℚ) (hp : ∑ j, prob j = 1) (A : B → G → ℕ)
    (C : J → B → G → ℕ) (base : B → ℚ) :
    let μ := fun b => PackedDeckMean.mean prob C b 1
    (∑ j, prob j * uniformScore A (C j) base μ) = rawBudget prob C - energy (fun (b : B) (_ : G) => μ b) := by
  intro μ
  let p := sampleWeight (G := G) prob
  let f (s : J × G) (b : B) (x : G) : ℚ := C s.1 b (s.2*x)
  let z (b : B) (x : G) : ℚ := (A b x : ℚ) - base b
  have average (g : J × G → ℚ) :
      (∑ j, prob j*((∑ h, g (j,h)) / Fintype.card G)) = ∑ s, p s*g s := by
    simp only [Fintype.sum_prod_type, p, sampleWeight, ← mul_sum, div_eq_mul_inv]
    apply sum_congr rfl
    intro j _
    ring
  let inc (s : J × G) := increment z (fun b g => (C s.1 b g : ℚ)) μ s.2
  change (∑ j, prob j*((∑ h, inc (j,h)) / Fintype.card G)) = _
  rw [average inc]
  change (∑ s, p s * ∑ b, ∑ x, ((f s b x-μ b)^2+2*z b x*(f s b x-μ b))) = _
  have cent (b : B) (x : G) := scalarVariance p (fun s => f s b x) (μ b) (z b x)
    (mass prob hp) (firstMoment prob C b x)
  calc
    _ = ∑ b, ∑ x, ∑ s, p s*((f s b x-μ b)^2 + 2*z b x*(f s b x-μ b)) := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = ∑ b, ∑ x, ((∑ s, p s*(f s b x)^2) - μ b^2) := by simp only [cent]
    _ = (∑ s, p s*energy (f s)) - energy (fun (b : B) (_ : G) => μ b) := by
      simp only [energy, sum_sub_distrib, mul_sum]
      congr 1
      rw [sum_comm (f := fun s : J × G => fun b : B => ∑ x : G, p s * f s b x ^ 2)]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = _ := by
      simp only [f, translate_energy, Fintype.sum_prod_type, p, sampleWeight, sum_const, card_univ,
        nsmul_eq_mul, rawBudget]
      have hn : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
      congr 1
      apply sum_congr rfl
      intro j _
      field_simp

/-- Applying a selected candidate and translation to the physical count bank changes its squared
deviation by the exact score increment. -/
theorem bank_step (A C : B → G → ℕ) (base μ : B → ℚ) (h : G) :
    bankEnergy (fun b x => A b x + C b (h*x)) (fun b => base b+μ b) =
      bankEnergy A base + increment (fun b g => (A b g : ℚ)-base b) (fun b g => (C b g : ℚ)) μ h := by
  simp only [bankEnergy, energy, increment, Nat.cast_add, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  exact sum_congr rfl fun _ _ => by ring

/-- The actual motion chosen by the finite-list and digit circuits spends at most this pack's
raw energy budget. The hypothesis is their verified one-pack score comparison. -/
theorem bank_step_le (prob : J → ℚ) (hp : ∑ j, prob j = 1) (A : B → G → ℕ)
    (C : J → B → G → ℕ) (base : B → ℚ) (j : J) (h : G)
    (picked : increment (fun b g => (A b g : ℚ)-base b) (fun b g => (C j b g : ℚ))
        (fun b => PackedDeckMean.mean prob C b 1) h ≤
      ∑ u, prob u * uniformScore A (C u) base (fun b => PackedDeckMean.mean prob C b 1)) :
    bankEnergy (fun b x => A b x+C j b (h*x)) (fun b => base b+PackedDeckMean.mean prob C b 1) ≤
      bankEnergy A base + rawBudget prob C := by
  rw [bank_step]
  apply add_le_add_right
  exact picked.trans ((average_increment prob hp A C base).le.trans (sub_le_self _
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)))

end PackedDeckEnergy

end BorderVNP
end Computability
end OAI
