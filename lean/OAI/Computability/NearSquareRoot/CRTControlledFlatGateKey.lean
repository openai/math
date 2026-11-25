import OAI.Computability.NearSquareRoot.CRTControlledElementaryRun
import OAI.Computability.IntegerMultiplication.Carry.Wide

/-! # Physical dimension markers for a two-position gate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits NearSquareRoot.Space

/-- Expand a unary bit count to a unary field cardinality. The shifted binary
one occupies only a linear number of bits before unary expansion. -/
theorem expandGateWidth {I : Type*} (d V : I → ℕ) (h : ∀ i, 2 ^ d i ≤ V i) :
    Carries (fun i => (V i : ℝ)) (fun i => send (tally (d i)))
      (fun i => send (tally (2 ^ d i))) := by
  let field := fun t : Tally => shift (t, [true])
  have easy : Easy field := easy_shift (Easy.identity.pair (Easy.const [true]))
  have val (i : I) : value (field (tally (d i))) = 2 ^ d i := by simp [field]
  have len (i : I) : (field (tally (d i))).length = d i + 1 := by
    simp [field, shift, fill_eq]
  have pos (i : I) : 1 ≤ (V i : ℝ) := by
    exact_mod_cast (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ d i).trans_le (h i)
  have vol : Volume (fun i => (V i : ℝ)) (fun i => send (tally (d i))) := by
    refine ⟨3,fun i => ?_⟩
    change (size (tally (d i)) : ℝ) ≤ _
    rw [size_tally,tally_length]
    change ((2 * d i + 1 : ℕ) : ℝ) ≤ 3 * (V i : ℝ)
    have hd := (Nat.lt_two_pow_self (n := d i)).trans_le (h i)
    exact_mod_cast (by omega : 2 * d i + 1 ≤ 3 * V i)
  have binary := Carries.func pos vol field easy
  apply binary.sequence
  have expand := Sized.natural (Carry.rice.on (fun i => field (tally (d i))))
  simp only [val] at expand
  apply expand.adapts pos 5
  intro i
  simp only [size_word,len]
  have h₁ := h i
  have h₂ := (Nat.lt_two_pow_self (n := d i)).trans_le h₁
  exact_mod_cast (by omega : 2 * (d i + 1) + 1 + 2 ^ d i + 1 ≤ 5 * V i)

/-- Read the three bit counts in the gate descriptor and materialize each
dimension, keeping the record stream alongside the descriptor. -/
theorem prepareFlatGateKey {I : Type} (p g b V : I → ℕ) (payload : I → Tree)
    (area : ∀ i, 2 ^ p i * 2 ^ g i * 2 ^ b i ≤ V i)
    (inputCap : ∀ i, (payload i).count ≤ V i) :
    BoundedTask V V (fun i => .fork (send (elementRulers p g b i)) (payload i))
      (fun i => .fork (send (elementRulers (fun i => 2 ^ p i)
        (fun i => 2 ^ g i) (fun i => 2 ^ b i) i)) (payload i)) := by
  have hp (i : I) : 0 < 2 ^ p i := Nat.pow_pos (by decide)
  have hg (i : I) : 0 < 2 ^ g i := Nat.pow_pos (by decide)
  have hb (i : I) : 0 < 2 ^ b i := Nat.pow_pos (by decide)
  have P := expandGateWidth p V (fun i =>
    ((Nat.le_mul_of_pos_right _ (hg i)).trans (Nat.le_mul_of_pos_right _ (hb i))).trans (area i))
  have G := expandGateWidth g V (fun i =>
    ((Nat.le_mul_of_pos_left _ (hp i)).trans (Nat.le_mul_of_pos_right _ (hb i))).trans (area i))
  have B := expandGateWidth b V (fun i =>
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (hp i) (hg i))).trans (area i))
  have inner := (G.first B.small).chain (B.second G.out)
  have outer := (P.first inner.small).chain (inner.second P.out)
  apply boundedOfCarries
  apply outer.first
  exact ⟨1,fun i => by simpa only [Nat.cast_one, one_mul] using Nat.cast_le.mpr (inputCap i)⟩

/-- Convert ordered little-endian positions into the three inactive ranges of
a flat gate, listed from the most significant end. -/
def flatGatePositionWidths (u : Tally × Tally × Tally) : Tally × Tally × Tally :=
  ((cutLists (() :: u.2.1, u.1)).2, (cutLists (() :: u.2.2, u.2.1)).2, u.2.2)

theorem flatGatePositionWidths_easy : Easy flatGatePositionWidths := by
  unfold flatGatePositionWidths
  exact ((easy_cut (show Easy (fun u : Tally × Tally × Tally => (() :: u.2.1, u.1)) by
    fun_prop)).sndCompose).pair (((easy_cut (show Easy (fun u : Tally × Tally × Tally =>
      (() :: u.2.2, u.2.1)) by fun_prop)).sndCompose).pair Easy.snd.sndCompose)

theorem flatGatePositionWidths_values (k hi lo : ℕ) :
    flatGatePositionWidths (tally k, tally hi, tally lo) =
      (tally (k-hi-1),tally (hi-lo-1),tally lo) := by
  simp [flatGatePositionWidths,cutLists,tally,Nat.sub_sub]

/-- Starting from the register width and ordered little-endian positions,
generate the gate markers while preserving the entire record stream. -/
theorem prepareFlatGatePositions {I : Type} (k hi lo V : I → ℕ) (payload : I → Tree)
    (ordered : ∀ i, lo i < hi i) (fits : ∀ i, hi i < k i)
    (area : ∀ i, 2 ^ k i ≤ V i) (inputCap : ∀ i, (payload i).count ≤ V i) :
    BoundedTask V V (fun i => .fork (send (elementRulers k hi lo i)) (payload i))
      (fun i => .fork (send (elementRulers (fun i => 2 ^ (k i - hi i - 1))
        (fun i => 2 ^ (hi i - lo i - 1)) (fun i => 2 ^ lo i) i)) (payload i)) := by
  have hk i := (Nat.lt_two_pow_self (n := k i)).trans_le (area i)
  have hv (i : I) : (1 : ℝ) ≤ V i := by exact_mod_cast Nat.zero_lt_of_lt (hk i)
  have hd : Volume (fun i => (V i : ℝ)) (fun i => send (elementRulers k hi lo i)) := by
    refine ⟨12,fun i => ?_⟩
    change (size (elementRulers k hi lo i) : ℝ) ≤ 12 * (V i : ℝ)
    have bound : size (elementRulers k hi lo i) ≤ 12 * V i := by
      simp only [elementRulers,size_prod,size_tally,tally_length]
      have := hk i
      have := ordered i
      have := fits i
      omega
    exact_mod_cast bound
  have hp := Carries.func hv hd flatGatePositionWidths flatGatePositionWidths_easy
  have saved : Volume (fun i => (V i : ℝ)) payload :=
    ⟨1,fun i => by simpa only [Nat.cast_one,one_mul] using Nat.cast_le.mpr (inputCap i)⟩
  have pre := boundedOfCarries (hp.first saved)
  simp only [elementRulers,flatGatePositionWidths_values] at pre
  have cap (i : I) : 2 ^ (k i-hi i-1) * 2 ^ (hi i-lo i-1) * 2 ^ lo i ≤ V i := by
    rw [← pow_add, ← pow_add]
    apply (Nat.pow_le_pow_right (by decide : 0 < 2) ?_).trans (area i)
    have := ordered i
    have := fits i
    omega
  have expand := prepareFlatGateKey _ _ _ V payload cap inputCap
  exact (pre.compose expand).bound 2 1 (fun i => by omega) (fun i => by simp)

end Controlled

end NearSquareRoot
end Computability
end OAI
