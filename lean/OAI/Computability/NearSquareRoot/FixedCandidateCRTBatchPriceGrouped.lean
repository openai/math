import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveMask

/-! # Encoded volume of the grouped CRT bit-mask stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTKernel
open IntegerMultiplication Code Adic Strip Packed Loom Dims Controlled

private theorem stripe_count_uniform {A : Type} (s : Series A) (f : A → Tree) (c : ℕ)
    (hc : ∀ a, (f a).count = c) : (stripe s f).count = s.count * (c + 1) + 1 := by
  have sum (l : List A) : costSum (fun a => (f a).count) l = l.length * c := by
    induction l with
    | nil => simp
    | cons a l h =>
      rw [costSum_cons, h, hc, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [stripe_simple, Task.forest_count, sum]
  simp [Series.count, Nat.mul_add, Nat.add_comm]

variable {X : Type} {U : X → Type} (n B : X → ℕ) (u : (x : X) → Series (U x))

/-- The regrouped row puts all suffix slots and their payloads on one bead
stripe. Each row and its enclosing list carry their own terminator. -/
theorem groupedCloth_count
    (f : (x : X) → Block 2 (n x) → Block 2 (B x) × U x → Bead) (x : X) :
    (cloth (fun y => line 2 (n y)) (fun y => (line 2 (B y)).cart (u y)) f x).count =
      2 ^ n x * (2 * (2 ^ B x * (u x).count) + 2) + 1 := by
  let mid := (line 2 (B x)).cart (u x)
  have row (a : Block 2 (n x)) : (strip mid (f x a)).count = 2 * mid.count + 1 := by
    simpa only [Nat.mul_comm mid.count 2] using
      stripe_count_uniform mid (fun j => send (f x a j)) 1 (fun _ => rfl)
  change (stripe (line 2 (n x)) (fun a => strip mid (f x a))).count = _
  rw [stripe_count_uniform _ _ _ row, lineSize]
  have hm : mid.count = 2 ^ B x * (u x).count := by
    change ((line 2 (B x)).cart (u x)).count = _
    rw [Series.count_cart, lineSize]
  rw [hm]

/-- Uniform bound allowing an empty payload. -/
theorem groupedCloth_size
    (f : (x : X) → Block 2 (n x) → Block 2 (B x) × U x → Bead) (x : X) :
    (cloth (fun y => line 2 (n y)) (fun y => (line 2 (B y)).cart (u y)) f x).count ≤
      5 * (2 ^ (n x + B x) * ((u x).count + 1)) := by
  rw [groupedCloth_count, pow_add]
  have hp : 0 < 2 ^ n x := Nat.two_pow_pos _
  have hq : 0 < 2 ^ B x := Nat.two_pow_pos _
  have h := Nat.le_mul_of_pos_right (2 ^ n x) hq
  nlinarith only [hp, h, Nat.zero_le ((2 ^ n x * 2 ^ B x) * (u x).count)]

/-- For positive payloads both the native and the grouped encoding fit within
five times the actual bit volume. -/
theorem groupedCloth_size_pos
    (f : (x : X) → Block 2 (n x) → Block 2 (B x) × U x → Bead)
    (x : X) (hu : 0 < (u x).count) :
    (cloth (fun y => line 2 (n y)) (fun y => (line 2 (B y)).cart (u y)) f x).count ≤
      5 * (2 ^ (n x + B x) * (u x).count) := by
  rw [groupedCloth_count, pow_add]
  have hp := Nat.two_pow_pos (n x)
  have h := (Nat.le_mul_of_pos_right (2 ^ n x) (Nat.two_pow_pos (B x))).trans
    (Nat.le_mul_of_pos_right _ hu)
  nlinarith only [hp, h]

theorem groupedRows_size_pos
    (f : (x : X) → Block 2 (n x + B x) → U x → Bead) (x : X) (hu : 0 < (u x).count) :
    (ReservePack.grouped u n B f x).count ≤ 5 * (2 ^ (n x + B x) * (u x).count) :=
  groupedCloth_size_pos n B u _ x hu

end FixedCandidate.CRTKernel

end NearSquareRoot
end Computability
end OAI
