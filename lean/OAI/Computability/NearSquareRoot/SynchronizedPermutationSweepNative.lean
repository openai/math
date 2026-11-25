import OAI.Computability.NearSquareRoot.CRTControlledReservePack
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetSuffix
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # Regroup the low addresses for the bounded prepared mask and restore every record -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReservePack
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Packed IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims NearSquareRoot.Space

noncomputable section

/-- Preparing the restoration rulers, applying a bounded kernel to the packed
records and restoring the original row boundaries costs one linear pass at
either end. Both rulers are parked beyond the kernel's active data. -/
theorem aroundBoundedOn {X Z : Type} [Codec Z] {r : Regime X} {U : X → Type}
    (u : (x : X) → Series (U x)) (n B m : X → ℕ)
    (f g : (x : X) → Block 2 (n x+B x) → U x → Z)
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (hn : r.Has (tally ∘ n)) (hB : r.Has (tally ∘ B))
    {head : X → Tree} (hh : r.Small head) (C : ℕ)
    (symbolF : ∀ x a j, (send (f x a j)).count ≤ C)
    (symbolG : ∀ x a j, (send (g x a j)).count ≤ C) :
    ∃ d : ℕ, ∀ {Y : Type} (select : Y → X) (Q T : Y → ℕ),
      (∀ y, r.scale (select y) ≤ Q y) → (∀ y, payloadBits d (Q y) ≤ B (select y)) →
      BoundedTask T (volume n B m ∘ select) (together head (grouped u n B f) ∘ select)
        (grouped u n B g ∘ select) →
      BoundedTask (fun y => volume n B m (select y)+T y) (volume n B m ∘ select)
        (together r.header (raw u n B f) ∘ select) (raw u n B g ∘ select) := by
  obtain ⟨d,prep⟩ := prepareBoundedOn u n B f m hm hu hn hB hh C symbolF
  refine ⟨d,fun select Q T scale room mid => ?_⟩
  let V := volume n B m ∘ select
  let rules := restoreRulers u n B ∘ select
  have small (y) : (rules y).count ≤ 7*V y := by
    let x := select y
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
  have end_ := (restoreBounded u n B g m hm hu C symbolG).on select
  have run := ((prep select Q scale room).compose (mid.right rules)).compose end_
  apply run.bound 10 8 <;> intro y
  · have cap := small y
    change V y+((rules y).count+T y)+V y+1 ≤ _
    change _ ≤ 10*(V y+T y+1)
    omega
  · have cap := small y
    change max (max (V y) (V y+(rules y).count)) (V y)+1 ≤ 8*(V y+1)
    omega

end
end Controlled.ReservePack

end NearSquareRoot
end Computability
end OAI
