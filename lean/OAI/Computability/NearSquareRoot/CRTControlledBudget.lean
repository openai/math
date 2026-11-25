import OAI.Computability.NearSquareRoot.CRTControlledXor
import OAI.Computability.NearSquareRoot.Asymptotic

/-! # Charging control-table work to aligned payloads

A P192 `Breeze` may spend a polynomial in the descriptor scale at *each* record. We keep
the number of packed low bits variable through the proof of the program. After obtaining
its fixed polynomial degree, collapsing sufficiently many unchanged positions into the
payload pays for this work without increasing total stream volume.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Code

/-- Number of trailing address positions sufficient to cover a degree-`D` polynomial. -/
def payloadBits (D k : ℕ) : ℕ := D * Nat.clog 2 (k+1)

theorem payload_capacity (D k R : ℕ) (hR : 0 < R) :
    (k+1)^D ≤ 2^(payloadBits D k) * R := by
  unfold payloadBits
  rw [Nat.mul_comm D, Nat.pow_mul]
  exact (Nat.pow_le_pow_left (Nat.le_pow_clog (b := 2) (by decide) (k+1)) D).trans
    (Nat.le_mul_of_pos_right _ hR)

/-- The chosen degree precedes specialization of the input family. All accepted cases use
the same finite program, regardless of the original width of the records. -/
theorem physicalPayloadBound {X : Type} {r : Regime X} {n width : X → ℕ} {rate : X → ℝ}
    {p q : X → Tree} (h : Breeze rate r n width p q) :
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (k R : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ k y) → (∀ y, 0 < R y) →
      (∀ y, 2^(payloadBits D (k y)) * R y ≤ width (pick y)) →
      Carries (fun y => 2 * (n (pick y) : ℝ) * width (pick y) * rate (pick y))
        (p ∘ pick) (q ∘ pick) := by
  obtain ⟨hrate,D,run⟩ := h
  refine ⟨D, ?_⟩
  intro Y pick k R hs hR hw
  apply (run.slide pick).larger
  intro y
  have hs' : (r.scale (pick y)+1)^D ≤ width (pick y) :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ (hs y)) D).trans
      ((payload_capacity D (k y) (R y) (hR y)).trans (hw y))
  have hb : (r.scale (pick y)+1:ℝ)^D ≤ width (pick y) := by exact_mod_cast hs'
  change (n (pick y) : ℝ) * (width (pick y) + (r.scale (pick y)+1:ℝ)^D) * rate (pick y) ≤ _
  apply mul_le_mul_of_nonneg_right _ ((zero_le_one' ℝ).trans (hrate _))
  have e := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) (n (pick y)))
  linarith

/-- Collapsing whole address slots changes neither the number nor the order of payload bits. -/
theorem collapsed_volume (k s R : ℕ) (hs : s ≤ k) :
    2^(k-s) * (2^s * R) = 2^k * R := by
  rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hs]

end Controlled

end NearSquareRoot
end Computability
end OAI
