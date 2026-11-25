import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepNative
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRetain

/-! # Effective native record frames for grouped permutation kernels -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReservePack

open IntegerMultiplication Code Adic Strip Packed Loom Dims Space EffectiveBoundedTask

noncomputable section

/-- A single polynomial suffix allowance is selected before the family of
candidate parameters. Fixed tape programs group and restore all selected
instances around the generated command, with both restoration rulers parked. -/
theorem aroundFamilyOnAt {X Z : Type} [Codec Z] {r : Regime X} {U : X → Type}
    (u : (x : X) → Series (U x)) (n B m : X → ℕ)
    (f g : (x : X) → Block 2 (n x+B x) → U x → Z)
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (hn : r.Has (tally ∘ n)) (hB : r.Has (tally ∘ B))
    {head : X → Tree} (hh : r.Small head) (C : ℕ)
    (symbolF : ∀ x a j, (send (f x a j)).count ≤ C)
    (symbolG : ∀ x a j, (send (g x a j)).count ≤ C) :
    ∃ d : ℕ, ∀ {P : Type} [Primcodable P] {Y : P → Type} (select : ∀ p, Y p → X)
      (Q T S : ∀ p, Y p → ℕ), (∀ p y, r.scale (select p y) ≤ Q p y) →
      (∀ p y, payloadBits d (Q p y) ≤ B (select p y)) →
      (∀ p y, volume n B m (select p y) ≤ S p y) →
      Family T S
        (fun p => together head (grouped u n B f) ∘ select p) (fun p => grouped u n B g ∘ select p) →
      Family (fun p y => volume n B m (select p y) + T p y) S
        (fun p => together r.header (raw u n B f) ∘ select p) (fun p => raw u n B g ∘ select p) := by
  obtain ⟨d,prep⟩ := prepareBoundedOn u n B f m hm hu hn hB hh C symbolF
  refine ⟨d,fun {P} _ {Y} select Q T S scale room space mid => ?_⟩
  let V p := volume n B m ∘ select p
  let rules p := restoreRulers u n B ∘ select p
  have small p (y : Y p) : (rules p y).count ≤ 7*V p y := by
    let x := select p y
    have hpos : 0 < volume n B m x :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) (hm x))
    have card : 2^n x * 2^B x ≤ volume n B m x := by
      unfold volume records packed
      rw [← Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ (hm x)
    have width : (u x).count ≤ volume n B m x :=
      (hu x).trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans
        (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))
    change size (tally ((line 2 (n x)).cart (line 2 (B x))).count) +
      size (tally (u x).count) + 1 ≤ 7*volume n B m x
    simp only [size_tally,tally_length,Series.count_cart,lineSize]
    omega
  let all (z : Sigma Y) := select z.1 z.2
  have start : Family V V (fun p => together r.header (raw u n B f) ∘ select p)
      (fun p => together (restoreRulers u n B) (together head (grouped u n B f)) ∘ select p) :=
    Family.joint (prep all (fun z => Q z.1 z.2) (fun z => scale z.1 z.2) (fun z => room z.1 z.2))
  have finish : Family V V (fun p => together (restoreRulers u n B) (grouped u n B g) ∘ select p)
      (fun p => raw u n B g ∘ select p) :=
    Family.joint ((restoreBounded u n B g m hm hu C symbolG).on all)
  obtain ⟨cmd,R,he,hR,run⟩ := (start.compose (mid.right rules)).compose finish
  refine ⟨cmd,R,he,hR,fun p => ⟨(run p).1,(run p).2.bound 10 8 ?_ ?_⟩⟩
  · intro y
    have cap := small p y
    change V p y + ((rules p y).count + T p y) + V p y + 1 ≤ 10*(V p y+T p y+1)
    omega
  · intro y
    have cap := small p y
    have fit : V p y ≤ S p y := space p y
    change max (max (V p y) (S p y+(rules p y).count)) (V p y)+1 ≤ 8*(S p y+1)
    omega


/-- Group and restore a candidate-selected native array with linear space. -/
theorem aroundFamilyOn {X Z : Type} [Codec Z] {r : Regime X} {U : X → Type}
    (u : (x : X) → Series (U x)) (n B m : X → ℕ)
    (f g : (x : X) → Block 2 (n x+B x) → U x → Z)
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (hn : r.Has (tally ∘ n)) (hB : r.Has (tally ∘ B))
    {head : X → Tree} (hh : r.Small head) (C : ℕ)
    (symbolF : ∀ x a j, (send (f x a j)).count ≤ C)
    (symbolG : ∀ x a j, (send (g x a j)).count ≤ C) :
    ∃ d : ℕ, ∀ {P : Type} [Primcodable P] {Y : P → Type} (select : ∀ p, Y p → X)
      (Q T : ∀ p, Y p → ℕ), (∀ p y, r.scale (select p y) ≤ Q p y) →
      (∀ p y, payloadBits d (Q p y) ≤ B (select p y)) →
      Family T (fun p => volume n B m ∘ select p)
        (fun p => together head (grouped u n B f) ∘ select p) (fun p => grouped u n B g ∘ select p) →
      Family (fun p y => volume n B m (select p y) + T p y) (fun p => volume n B m ∘ select p)
        (fun p => together r.header (raw u n B f) ∘ select p) (fun p => raw u n B g ∘ select p) := by
  obtain ⟨d,stage⟩ := aroundFamilyOnAt u n B m f g hm hu hn hB hh C symbolF symbolG
  exact ⟨d,fun pick Q T scale room => stage pick Q T (fun p => volume n B m ∘ pick p)
    scale room (fun _ _ => le_rfl)⟩

end
end Controlled.ReservePack

end NearSquareRoot
end Computability
end OAI
