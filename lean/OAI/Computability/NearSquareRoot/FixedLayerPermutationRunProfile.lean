import OAI.Computability.NearSquareRoot.FixedLayerPermutationRunDataEffective
import OAI.Computability.NearSquareRoot.FixedLayerPermutationRunOrderClock

/-! # The effective Fourier permutation row on all parameter guesses -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer
open Filter IntegerMultiplication Code FixedCandidate DigitPacking SynchronizedPermutationBudget

variable {P : Type} [Primcodable P] {I : P → Type}
  (n : (p : P) → I p → ℕ) (h : ∀ p i, Directory (n p i)) (dir : (p : P) → I p → Bool)
  (D : P → ℕ) (eff : Computable D)
  (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
  (big : ∀ p i, BoxPasses (addressBits (n p i)) (D p) 2)

include eff hn big

/-- Every candidate executes the generated permutation. An eventually accurate
candidate attains its own native exponent at the row level, with time for every
switch batch and the surrounding tape scans. -/
theorem effectivePermutationMeasuredProfile (η : P → ℝ) (good : P → ℕ → Prop)
    (t s : (p : P) → NativePass (D p) → ℕ) (native : NativeMeasured D t s)
    (T S : P → ℕ)
    (ht : ∀ p (z : BatchState n h dir p), good p (n p z.1.val.instanceIndex) →
      let u := BatchState.sample n h dir D hd big z
      t p u ≤ T p*(nativeWork (η p) u.val.1+1))
    (hs : ∀ p (z : BatchState n h dir p), good p (n p z.1.val.instanceIndex) →
      let u := BatchState.sample n h dir D hd big z
      s p u ≤ S p*(u.val.1.volumeB+1)) :
    ∃ arena clock : P → ℕ → ℕ, EffectiveImplementsAt n h dir hd arena clock .permutation ∧
      (∀ p N, N ≤ arena p N ∧ arena p N ≤ clock p N) ∧
      ∀ p, (∀ᶠ N in atTop, good p N) → 0 ≤ η p →
        (∀ᶠ N in atTop, arena p N = N) ∧ RowClock (η p) (clock p) := by
  obtain ⟨tick,arena,nativeRows,space,profiles⟩ :=
    placedBatchProfiles n h dir D hd hn big η good t s native T S ht hs
  let clock p := permProfileClock (tick p) (arena p)
  have includes p N : arena p N ≤ clock p N := permProfile_arena _ _ _
  refine ⟨arena,clock,?_,fun p N => ⟨space p N,includes p N⟩,?_⟩
  · apply effectivePermutationFromPlacedBatchesAt n h dir D eff hd hn (fun p i => (big p i).fits)
      arena clock tick (fun p i => space p (n p i))
      (fun p i => (space p (n p i)).trans (includes p (n p i))) (fun _ => 1) _ nativeRows
    intro p i
    simpa only [Nat.one_mul] using
      (permProfile_rate (tick p) (arena p) (h p i) (big p i).fits).trans (Nat.le_succ _)
  · intro p selected positive
    have holds := selected.mono (fun N proof => profiles p N proof)
    exact ⟨holds.mono (fun _ z => z.2),permProfile_rowClock positive holds⟩

/-- Width-independent native measurements may be released only above a cutoff
depending on the guessed parameters. All smaller and inaccurate instances still
execute the same emitted file. -/
theorem effectivePermutationNativeProfile (η : P → ℝ) (good : P → Prop)
    (positive : ∀ p, good p → 0 ≤ η p)
    (t s : (p : P) → NativePass (D p) → ℕ) (native : NativeMeasured D t s)
    (release : ∀ p, good p → ∃ T S K : ℕ, ∀ u : NativePass (D p), K ≤ u.val.1.k →
      t p u ≤ T*(nativeWork (η p) u.val.1+1) ∧ s p u ≤ S*(u.val.1.volumeB+1)) :
    ∃ arena clock : P → ℕ → ℕ, EffectiveImplementsAt n h dir hd arena clock .permutation ∧
      (∀ p N, N ≤ arena p N ∧ arena p N ≤ clock p N) ∧
      ∀ p, good p → (∀ᶠ N in atTop, arena p N = N) ∧ RowClock (η p) (clock p) := by
  classical
  have pick p : ∃ T S K : ℕ, good p → ∀ u : NativePass (D p), K ≤ u.val.1.k →
      t p u ≤ T*(nativeWork (η p) u.val.1+1) ∧ s p u ≤ S*(u.val.1.volumeB+1) := by
    by_cases ok : good p
    · obtain ⟨T,S,K,bounds⟩ := release p ok
      exact ⟨T,S,K,fun _ => bounds⟩
    · exact ⟨0,0,0,fun hp => (ok hp).elim⟩
  choose T S K price using pick
  let eligible p N := good p ∧ K p ≤ addressBits N
  obtain ⟨arena,clock,machine,space,fast⟩ := effectivePermutationMeasuredProfile n h dir D eff hd hn big
    η eligible t s native T S (fun p z q => (price p q.1 (BatchState.sample n h dir D hd big z) q.2).1)
    (fun p z q => (price p q.1 (BatchState.sample n h dir D hd big z) q.2).2)
  refine ⟨arena,clock,machine,space,fun p ok => fast p ?_ (positive p ok)⟩
  exact (addressBits_tendsto_atTop.eventually_ge_atTop (K p)).mono (fun _ bound => ⟨ok,bound⟩)

end FixedLayer

end NearSquareRoot
end Computability
end OAI
