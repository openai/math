import OAI.Computability.BorderVNP.ShortenPackMotions
import OAI.Computability.BorderVNP.ShortenEpochMixingError

/-!
# The finite-motion law on the actual charged cables

The bin mean used to choose whole-pack motions equals the weighted sum of the
marginal laws of the original charged cables. Uncharged cables stay in the
network and contribute zero to all bin counts. A single motion acts on every
cable of a given pack; the identity uses linearity of the finite sums.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PackMotions

open Crossing Epoch SeedIntervals Packing
open scoped BigOperators Classical

variable {D copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K) {A M : Type} [Fintype M]
variable (charged : ∀ i, (input i).layout.Edge → Bool)
variable (movedBin : ∀ i, M → (input i).layout.Edge → Option A)
variable (prob : Fin copies → M → ℝ)

/-- Charged input cables, tagged by the pack which moves them together. -/
abbrev Active := Σ i : Fin copies, {e : (input i).layout.Edge // charged i e = true}

/-- An active cable's actual bit width divided by the number of packs. -/
noncomputable def normalizedWidth (w : Active input charged) : ℝ :=
  ((input w.1).layout.width w.2.val : ℝ) / copies

/-- Marginal probability of one actual moved cable arriving in an address. -/
noncomputable def finiteWireLaw (w : Active input charged) (a : A) : ℝ :=
  ∑ m, if movedBin w.1 m w.2.val = some a then prob w.1 m else 0

private theorem sum_active {E R : Type*} [Fintype E] [AddCommMonoid R] (tag : E → Bool) (f : E → R)
    (hf : ∀ e, tag e ≠ true → f e = 0) :
    (∑ e, f e) = ∑ e : {e : E // tag e = true}, f e.val := by
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun e => tag e = true) f]
  have h : (∑ e : {e : E // ¬ tag e = true}, f e.val) = 0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  rw [h, add_zero]

private theorem wire_mean (hmask : ∀ i m e, (movedBin i m e).isSome = charged i e)
    (i : Fin copies) (a : A) :
    motionMean prob (fun l m b => (count (input l).layout (movedBin l m) b : ℝ)) i a =
      ∑ e : {e : (input i).layout.Edge // charged i e = true},
        ((input i).layout.width e.val : ℝ) * finiteWireLaw input charged movedBin prob ⟨i,e⟩ a := by
  unfold motionMean
  simp only [count_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  let f := fun e : (input i).layout.Edge => ∑ m, prob i m *
    (if movedBin i m e = some a then ((input i).layout.width e : ℝ) else 0)
  change ∑ e, f e = _
  rw [sum_active (charged i) f]
  · apply Finset.sum_congr rfl
    intro e _
    change (∑ m, prob i m * (if movedBin i m e.val = some a then _ else 0)) = _
    rw [finiteWireLaw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    by_cases he : movedBin i m e.val = some a <;> simp [he, mul_comm]
  · intro e h
    apply Finset.sum_eq_zero
    intro m _
    have hn : movedBin i m e ≠ some a := by
      intro hsome
      apply h
      rw [← hmask i m e, hsome]
      rfl
    simp [hn]

/-- The actual mean of moved sorted bin populations is the sum of the normalized single-wire laws. -/
theorem binMean_eq_binCounts (hmask : ∀ i m e, (movedBin i m e).isSome = charged i e) :
    binMean input movedBin prob =
      binCounts (normalizedWidth input charged) (finiteWireLaw input charged movedBin prob) := by
  funext a
  rw [binMean, Finset.sum_div, binCounts, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [wire_mean input charged movedBin prob hmask, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  unfold normalizedWidth
  ring

/-- If a marginal probability is nonzero, at least one motion actually put that cable in the bin. -/
theorem finiteWireLaw_support (w : Active input charged) (a : A)
    (hw : finiteWireLaw input charged movedBin prob w a ≠ 0) :
    ∃ m, movedBin w.1 m w.2.val = some a := by
  by_contra! h
  apply hw
  simp [finiteWireLaw, h]

/-- The true marginal wire laws are probabilities when each active wire is assigned to a bin. -/
theorem finiteWireLaw_sum [Fintype A] (hmask : ∀ i m e, (movedBin i m e).isSome = charged i e)
    (hp : ∀ i, ∑ m, prob i m = 1) (w : Active input charged) :
    ∑ a, finiteWireLaw input charged movedBin prob w a = 1 := by
  unfold finiteWireLaw
  rw [Finset.sum_comm, ← hp w.1]
  apply Finset.sum_congr rfl
  intro m _
  have hm : (movedBin w.1 m w.2.val).isSome = true := (hmask _ _ _).trans w.2.property
  cases h : movedBin w.1 m w.2.val with
  | none => simp [h] at hm
  | some b => simp

variable {Q : Type*} [PseudoMetricSpace Q]
variable (place : ∀ i, M → (input i).layout.Site → Q)

omit [Fintype M] in
/-- Normalized charged length of the actual moved union is the sum over the original tagged
cables of their normalized widths times their motion-invariant lengths. -/
theorem normalized_joint_length (ω : Fin copies → M) (wireLength : Active input charged → ℝ)
    (hmask : ∀ i m e, (movedBin i m e).isSome = charged i e)
    (hmove : ∀ (w : Active input charged) m, dist (place w.1 m ((input w.1).layout.src w.2.val))
      (place w.1 m ((input w.1).layout.dst w.2.val)) = wireLength w) :
    chargedLength (parallelPacks input).layout (fun v => place v.1 (ω v.1) v.2)
        (fun c => (jointBin input movedBin ω c).isSome) / copies =
      ∑ w : Active input charged, normalizedWidth input charged w * wireLength w := by
  rw [joint_length input movedBin, Finset.sum_div, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  unfold chargedLength
  simp_rw [hmask]
  let f := fun e : (input i).layout.Edge => if charged i e then
    ((input i).layout.width e : ℝ) * dist (place i (ω i) ((input i).layout.src e))
      (place i (ω i) ((input i).layout.dst e)) else 0
  change (∑ e, f e) / copies = _
  rw [sum_active (charged i) f (fun e h => by simp [f,h]), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  simp only [f, e.property, ite_true]
  rw [hmove ⟨i,e⟩ (ω i)]
  unfold normalizedWidth
  ring

/-- The first half-mean inequality of (6.3) for the actual input union, proved from the finite
law's single-wire variation estimates and the ideal wire laws' symmetry and length support. -/
theorem half_binMean [NeZero D] [Fintype A] (ω : Fin copies → M) (perm : Fin D → Equiv.Perm A)
    (length : A → ℝ) (wireLength : Active input charged → ℝ) (ideal : Active input charged → A → ℝ)
    (hmask : ∀ i m e, (movedBin i m e).isSome = charged i e)
    (hmove : ∀ (w : Active input charged) m, dist (place w.1 m ((input w.1).layout.src w.2.val))
      (place w.1 m ((input w.1).layout.dst w.2.val)) = wireLength w)
    (hwire : ∀ w, 0 ≤ wireLength w) (hbin : ∀ a, 0 ≤ length a)
    (hlen : ∀ j a, length (perm j a) = length a)
    (htag : ∀ (w : Active input charged) m a, movedBin w.1 m w.2.val = some a → length a = wireLength w)
    (hprob : ∀ w, ∑ a, ideal w a = 1)
    (hsupp : ∀ w a, ideal w a ≠ 0 → length a = wireLength w)
    (hinv : ∀ w j a, ideal w (perm j a) = ideal w a)
    (hclose : ∀ w, ∑ a, |finiteWireLaw input charged movedBin prob w a - ideal w a| ≤ 1 / (2 * D)) :
    (chargedLength (parallelPacks input).layout (fun v => place v.1 (ω v.1) v.2)
        (fun c => (jointBin input movedBin ω c).isSome) / copies) / 2 ≤
      matchedLength perm length (binMean input movedBin prob) := by
  rw [normalized_joint_length input charged movedBin place ω wireLength hmask hmove,
    binMean_eq_binCounts input charged movedBin prob hmask]
  apply half_mean_length_of_wire_mixing perm (normalizedWidth input charged) wireLength length
    (finiteWireLaw input charged movedBin prob) ideal (fun w => by unfold normalizedWidth; positivity)
    hwire hbin hlen hprob _ hsupp hinv
  · simpa only [Fintype.card_fin] using hclose
  · intro w a h
    obtain ⟨m,hm⟩ := finiteWireLaw_support input charged movedBin prob w a h
    exact htag w m a hm

end Shortening.PackMotions

end BorderVNP
end Computability
end OAI
