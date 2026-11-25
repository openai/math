import OAI.Computability.NearSquareRoot.FixedLayerEffective
import OAI.Computability.NearSquareRoot.FixedCandidateArena

/-! # The two effective transforms of a fixed candidate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint DigitPacking ShortFourier.BatchWord

noncomputable section
set_option maxHeartbeats 1800000

/-- Choose both certified numerical words, together with their finite-register
command families, on the same admitted domain and the same input cutoff. -/
theorem effectivePlansAt {P : Type} [Primcodable P] (K : P → ℕ) (hK : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (hd : ∀ p (i : LargeInput (K p)), 4 ≤ (box i.val.width).length)
    (hk : ∀ p (i : LargeInput (K p)), 1024 ≤ addressBits i.val.width)
    (arena clock : P → ℕ → ℕ)
    (fit : ∀ p (i : LargeInput (K p)), i.val.width ≤ arena p i.val.width)
    (lin : ∀ p (i : LargeInput (K p)), arena p i.val.width ≤ clock p i.val.width) (hl : ∀ p (i : LargeInput (K p)), phaseClock i.val.width ≤ clock p i.val.width)
    (perm : ∀ b : Bool, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => b) hd arena clock .permutation)
    (walsh : ∀ b : Bool, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => b) hd arena clock .walsh) :
    ∃ plans : ∀ p (i : LargeInput (K p)), FixedCandidate.Plan (hv p i),
      FixedCandidate.EffectiveTransformAt K hv arena (fun p => wordClock (clock p))
        (fun p i => eval (hv p i) (plans p i).forward) ∧
      FixedCandidate.EffectiveTransformAt K hv arena (fun p => wordClock (clock p))
        (fun p i => eval (hv p i) (plans p i).inverse) := by
  let n (p : P) (i : LargeInput (K p)) := i.val.width
  have guard p (i : LargeInput (K p)) : 2 ≤ n p i := (hK p).trans i.property
  obtain ⟨f,ef,cf⟩ := effectiveTransformAt n hv false hd guard hk arena clock fit lin hl (perm false) (walsh false)
  obtain ⟨j,ej,cj⟩ := effectiveTransformAt n hv true hd guard hk arena clock fit lin hl (perm true) (walsh true)
  exact ⟨fun p i => ⟨f p i,j p i,ef p i,ej p i⟩,cf,cj⟩

/-- Both linear-workspace transform families of the fixed multiplication candidate. -/
theorem effectivePlans {P : Type} [Primcodable P] (K : P → ℕ) (hK : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (hd : ∀ p (i : LargeInput (K p)), 4 ≤ (box i.val.width).length)
    (hk : ∀ p (i : LargeInput (K p)), 1024 ≤ addressBits i.val.width)
    (clock : P → ℕ → ℕ) (hl : ∀ p (i : LargeInput (K p)), phaseClock i.val.width ≤ clock p i.val.width)
    (perm : ∀ b : Bool, EffectiveImplements (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => b) hd clock .permutation)
    (walsh : ∀ b : Bool, EffectiveImplements (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => b) hd clock .walsh) :
    ∃ plans : ∀ p (i : LargeInput (K p)), FixedCandidate.Plan (hv p i),
      FixedCandidate.EffectiveTransform K hv (fun p => wordClock (clock p))
        (fun p i => eval (hv p i) (plans p i).forward) ∧
      FixedCandidate.EffectiveTransform K hv (fun p => wordClock (clock p))
        (fun p i => eval (hv p i) (plans p i).inverse) :=
  effectivePlansAt K hK hv hd hk (fun _ n => n) clock (fun _ _ => le_rfl)
    (fun p i => (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)).trans (hl p i))
    hl perm walsh

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
