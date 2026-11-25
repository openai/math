import OAI.Computability.BorderVNP.PackedDeckEnergyRun

/-! # Recovering the normalized bin arrays and motion means in equation (6.2) -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckEnergy

open CoverDeck PackedDeckCandidate Epoch Finset

variable {B G J : Type*} [Fintype B] [Fintype G] [Group G] [Fintype J] {K : ℕ}

/-- Physical moved counts on the tile-by-bin grid for one candidate and deck posttranslation. -/
def moved (C : Fin K → J → B → G → ℕ) (i : Fin K) (s : J × G) (a : G × B) : ℝ :=
  C i s.1 a.2 (s.2*a.1)

/-- Candidate probability times the uniform probability of its deck translation. -/
noncomputable def motionWeight (prob : Fin K → J → ℚ) (i : Fin K) (s : J × G) : ℝ :=
  (prob i s.1 : ℝ) / Fintype.card G

omit [Fintype B] in

/-- The rational accumulator mean is exactly the real motionMean of the placed pack. -/
theorem mean_cast (prob : Fin K → J → ℚ) (C : Fin K → J → B → G → ℕ) (i : Fin K) (a : G × B) :
    ((PackedDeckMean.mean (prob i) (C i) a.2 1 : ℚ) : ℝ) =
      motionMean (motionWeight prob) (moved C) i a := by
  rw [PackedDeckMean.mean_eq _ _ _ 1, ← PackedDeckMean.mean_eq _ _ _ a.1]
  simp only [PackedDeckMean.mean, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
    motionMean, motionWeight, moved, Fintype.sum_prod_type, ← mul_sum]
  apply sum_congr rfl
  intro j _
  ring

omit [Group G] in

/-- The unshifted count matrix in the geometric single-pack bound has the same energy as
the cast of its exact rational energy. -/
theorem energy_cast_counts (f : B → G → ℕ) :
    ((energy (fun b g => (f b g : ℚ)) : ℚ) : ℝ) =
      binEnergy (fun a : G × B => (f a.2 a.1 : ℝ)) := by
  simp only [energy, binEnergy, Rat.cast_sum, Rat.cast_pow, Rat.cast_natCast, Fintype.sum_prod_type]
  rw [sum_comm]

omit [Fintype B] in

/-- For every coordinate, the final centered bank is the sum of the chosen counts minus
the sum of the true independent-motion means. -/
theorem centered_final (prob : Fin K → J → ℚ) (C : Fin K → J → B → G → ℕ)
    (bank : ℕ → B → G → ℕ) (base : ℕ → B → ℚ) (choice : Fin K → J) (deck : Fin K → G)
    (start : ∀ b g, (bank 0 b g : ℚ) = base 0 b)
    (update : ∀ (i : Fin K) b g, bank (i.val+1) b g = bank i.val b g + C i (choice i) b (deck i*g))
    (means : ∀ (i : Fin K) b, base (i.val+1) b = base i.val b + PackedDeckMean.mean (prob i) (C i) b 1)
    (a : G × B) :
    (bank K a.2 a.1 : ℝ) - (base K a.2 : ℝ) =
      (∑ i, moved C i (choice i,deck i) a) - ∑ i, motionMean (motionWeight prob) (moved C) i a := by
  let diff (i : Fin K) := moved C i (choice i,deck i) a - motionMean (motionWeight prob) (moved C) i a
  let term (j : ℕ) := if h : j < K then diff ⟨j,h⟩ else 0
  have hb (t : ℕ) (ht : t ≤ K) : (bank t a.2 a.1 : ℝ) - (base t a.2 : ℝ) = ∑ j ∈ range t, term j := by
    induction t with
    | zero =>
      have he : (bank 0 a.2 a.1 : ℝ) = (base 0 a.2 : ℝ) := by exact_mod_cast start a.2 a.1
      simp [he]
    | succ t ih =>
      let i : Fin K := ⟨t,ht⟩
      have ha := update i a.2 a.1
      have hμ := means i a.2
      change bank (t+1) a.2 a.1 = bank t a.2 a.1 + C i (choice i) a.2 (deck i*a.1) at ha
      change base (t+1) a.2 = base t a.2 + PackedDeckMean.mean (prob i) (C i) a.2 1 at hμ
      rw [ha,hμ,Nat.cast_add,Rat.cast_add,mean_cast _ _ i a, sum_range_succ, ← ih (by omega)]
      have hs : term t = diff i := by simp [term, i, show t < K from ht]
      rw [hs]
      dsimp only [diff,moved]
      ring
  rw [hb K le_rfl, ← Fin.sum_univ_eq_sum_range term, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by simp [term,diff,i.isLt]

/-- The left side of (6.2) in the independent-motion convention is precisely the normalized
final-bank energy controlled by the actual greedy run. -/
theorem normalized_array (prob : Fin K → J → ℚ) (C : Fin K → J → B → G → ℕ)
    (bank : ℕ → B → G → ℕ) (base : ℕ → B → ℚ) (choice : Fin K → J) (deck : Fin K → G)
    (start : ∀ b g, (bank 0 b g : ℚ) = base 0 b)
    (update : ∀ (i : Fin K) b g, bank (i.val+1) b g = bank i.val b g + C i (choice i) b (deck i*g))
    (means : ∀ (i : Fin K) b, base (i.val+1) b = base i.val b + PackedDeckMean.mean (prob i) (C i) b 1) :
    binEnergy (fun a : G × B => (bank K a.2 a.1 : ℝ)/K - (base K a.2 : ℝ)/K) =
      binEnergy (fun a => (∑ i, moved C i (choice i,deck i) a)/K -
        (∑ i, motionMean (motionWeight prob) (moved C) i a)/K) := by
  apply congrArg binEnergy
  funext a
  rw [← sub_div, ← sub_div, centered_final prob C bank base choice deck start update means a]

end PackedDeckEnergy

end BorderVNP
end Computability
end OAI
