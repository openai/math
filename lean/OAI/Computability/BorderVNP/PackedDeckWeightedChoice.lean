import OAI.Computability.BorderVNP.PackedDeckMean
import OAI.Computability.BorderVNP.PackedDeckCandidateBounds

/-!
# Finite motion choice with its actual rational mean

The finite motion candidates are averaged with their rational probabilities
and the subsequent deck translation is uniform. The Boolean frame updates
the running bin means before scoring the candidates. Its output exposes the
updated banks and the ordinal of the first minimizing candidate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckMean

open PackedDeckCandidate PackedDeckScore
open VPVNP.VerifierNetwork (Frame)

/-- All gates in the mean update and finite-motion choice at one pack. -/
def candidateCost (B G : Type*) [Fintype B] [Fintype G] (m w U t C e M z : ℕ) :=
  (1 + Fintype.card B * meanCost G m w U t) + (1 + m*2*channelCost B G w C e M z +
    m*m*(sumBits B w+1)*(16*(sumBits B w+1)+22) + m*((15*(sumBits B w+1)+3)*m+1))

/-- Positive common-denominator weights specialize the mean updater and
score network to the given distribution. The gate constants are independent
of the finite index types, weights, cover size, and working width. -/
theorem weightedChoice_frames :
    ∃ U t C e M z : ℕ, ∀ (m : ℕ) (prob : Fin m → ℚ) (_ : ∀ c, 0 ≤ prob c) (_ : ∑ c, prob c = 1),
      ∃ P : ℕ, 0 < P ∧ ∀ (B G : Type) [Fintype B] [Fintype G] [Group G] (w : ℕ), P < 2^w →
      ∃ f : Frame (Input B G m w) (Input B G m w ⊕ Fin m),
        f.size ≤ candidateCost B G m w U t C e M z ∧
        (∀ x j, f.eval x (.inl (.inl j)) = x (.inl j)) ∧
        ∀ (x : Input B G m w → Bool) (base : B → ℚ) (K A : ℕ),
          (∀ b, ((P * Fintype.card G : ℕ) : ℚ) * base b = meanNumerator x b) →
          (∀ b, meanNumerator x b ≤ A) →
          (∀ s b g, inputCounts x s b g ≤ K) →
          choiceBits (Fintype.card G) (P * Fintype.card G) K (A+P*(Fintype.card G*K)) ≤ w →
          let μ := fun b => mean prob (fun c => inputCounts x (some c)) b 1
          (∀ b, ((P * Fintype.card G : ℕ) : ℚ) * (base b + μ b) =
            meanNumerator (f.eval x ∘ Sum.inl) b) ∧
          ∀ i, f.eval x (.inr i) = true ↔ (List.finRange m).argmin
            (fun j => uniformScore (inputCounts x none) (inputCounts x (some j)) base μ) = some i := by
  obtain ⟨U,t,makeUpdate⟩ := updateFrames
  obtain ⟨C,e,M,z,makeChoice⟩ := exists_choice
  refine ⟨U,t,C,e,M,z,?_⟩
  intro m prob hn hsum
  obtain ⟨P,pnum,hP,hnum,hprob,hmax⟩ := common_probability_denominator prob hn hsum
  refine ⟨P,hP,?_⟩
  intro B G instB instG groupG w hwidth
  have hw : 0 < w := by cases w with | zero => simp at hwidth; omega | succ _ => omega
  let n := Fintype.card G
  let D := P*n
  have hD : 0 < D := Nat.mul_pos hP Fintype.card_pos
  obtain ⟨upd,hu,bank,hup⟩ := makeUpdate B G m w hw pnum (fun c => (hmax c).trans_lt hwidth)
  obtain ⟨select,hs,hselect⟩ := makeChoice B G m w D hD
  let f := select.withInput.subst upd
  refine ⟨f,by simpa [f,candidateCost] using Nat.add_le_add hu hs,?_,?_⟩
  · intro x j
    simp [f,bank]
  · intro x base K A hbase hold hcount hbits
    let μ := fun b => mean prob (fun c => inputCounts x (some c)) b 1
    let L := A+P*(n*K)
    let y := upd.eval x
    have hcounts (s : Option (Fin m)) : inputCounts y s = inputCounts x s := by
      funext b g
      simp [y,inputCounts,bank]
    have htotal (c : Fin m) (b : B) : ∑ g, inputCounts x (some c) b g ≤ n*K := by
      simpa [n] using Finset.sum_le_sum (s := Finset.univ) (fun g _ => hcount (some c) b g)
    have hnext (b : B) : nextNumerator pnum x b ≤ L := by
      apply Nat.add_le_add (hold b)
      simpa [hnum] using weighted_le pnum (fun c => inputCounts x (some c)) b (fun c => htotal c b)
    have hfit : L < 2^w := (fields_fit n D K L).2.trans_le (Nat.pow_le_pow_right (by decide) hbits)
    have hnum' (b : B) : meanNumerator y b = nextNumerator pnum x b := hup x b ((hnext b).trans_lt hfit)
    have hscale (b : B) : (D : ℚ)*(base b+μ b) = meanNumerator y b := by
      rw [hnum']
      exact scaled_update hP hprob (fun c => inputCounts x (some c)) (meanNumerator x) base hbase b 1
    have hcharge : ∀ i neg b, charge D y i neg b < 2^w :=
      charge_fits D K L y (fun s b g => by rw [hcounts]; exact hcount s b g)
        (fun b => (hnum' b).le.trans (hnext b)) hbits
    have hfirst : f.eval x ∘ Sum.inl = y := by funext i; simp [f,y]
    refine ⟨fun b => by rw [hfirst]; exact hscale b,?_⟩
    intro i
    simpa [f,y,hcounts] using hselect y base μ hscale hcharge i

end PackedDeckMean

end BorderVNP
end Computability
end OAI
