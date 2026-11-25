import OAI.Computability.BorderVNP.CoverDeckDigitRead
import OAI.Computability.BorderVNP.PackedDeckScoreCost

/-!
# Bit costs of conditional digit selection on the product cover

The sparse key embedding bounds the logarithms in the histogram circuit.
Surjective reduction bounds each intermediate volume by the number of
full-depth product tiles. These two bounds give a single linear volume
factor for the entire search.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckScore

private abbrev Tiles (q l : ℕ) := Fin q → Deck l

private theorem card_mono (q : ℕ) {d l : ℕ} (h : d ≤ l) :
    Fintype.card (Tiles q d) ≤ Fintype.card (Tiles q l) :=
  Fintype.card_le_of_surjective _ (productReduction_surjective q h)

private theorem key_width (q : ℕ) {d l w : ℕ} (h : d ≤ l) :
    keyWidth q d ≤ (90*q)*(l+w+1) := by
  change q*(30*(d+1)*3) ≤ _
  calc
    _ = (90*q)*(d+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

private def widthFactor (b q : ℕ) := 270*q+b+5

private theorem digitWidths (B : Type*) [Fintype B] (q : ℕ) {d l : ℕ} (h : d ≤ l) (w : ℕ) :
    workBits B (Tiles q l) (Tiles q d) (keyWidth q d) w ≤
      widthFactor (Fintype.card B) q * (l+w+1) ∧
    scoreBits B (Tiles q d) w ≤ widthFactor (Fintype.card B) q * (l+w+1) := by
  let b := Fintype.card B
  let K := keyWidth q l
  let S := l+w+1
  have hG : Fintype.card (Tiles q l) ≤ 2^K := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (productKey q l).injective
  have hH := (card_mono q h).trans hG
  have a : batchBits (Tiles q l) (Tiles q d) ≤ K+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    omega
  have b' : batchBits (B × Tiles q d) Unit ≤ b+K := by
    apply Nat.clog_le_of_le_pow
    rw [Fintype.card_prod,Fintype.card_unit,pow_add]
    change b * _ + 1 ≤ _
    calc
      _ ≤ b * 2^K + 2^K := Nat.add_le_add (Nat.mul_le_mul_left _ hH) Nat.one_le_two_pow
      _ = (b+1)*2^K := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ b.lt_two_pow_self
  have hl : K ≤ 90*q*S := key_width q (le_refl l)
  have hd : keyWidth q d ≤ 90*q*S := key_width q h
  have h270 : 270*q*S = 3*(90*q*S) := by ring
  have hw : w+1 ≤ S := by dsimp [S]; omega
  have hb : b ≤ b*S := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change _ ≤ widthFactor b q * S ∧ _ ≤ widthFactor b q * S
  constructor
  · unfold workBits widthFactor
    rw [Nat.add_mul, Nat.add_mul]
    omega
  · have hs : scoreBits B (Tiles q d) w = 2*w+batchBits (B × Tiles q d) Unit := by
      simp [sumBits,batchBits]
    rw [hs]
    unfold widthFactor
    rw [Nat.add_mul, Nat.add_mul]
    omega

private def childFactor (b A C : ℕ) :=
  2 + 1800*b*A^3 + b*C + 2400*(b+2)*A^3

private theorem child_cost_bound (B : Type*) [Fintype B] (q : ℕ) {d l : ℕ} (h : d ≤ l)
    (w C e p : ℕ) (he : e ≤ p) (hp : 3 ≤ p) :
    childCost B (Tiles q l) (Tiles q d) (keyWidth q d) w C e ≤
      Fintype.card (Tiles q l) * childFactor (Fintype.card B) (widthFactor (Fintype.card B) q) C *
        (l+w+1)^p := by
  let V := Fintype.card (Tiles q l)
  let b := Fintype.card B
  let A := widthFactor b q
  let S := l+w+1
  let P := S^p
  have hV : 1 ≤ V := Fintype.card_pos
  have hP : 1 ≤ P := Nat.pow_pos (Nat.succ_pos _)
  have hH : Fintype.card (Tiles q d) ≤ V := card_mono q h
  have hc : Fintype.card (Tiles q l)+Fintype.card (Tiles q d)+1 ≤ 3*V := by
    change V+_+1 ≤ _; omega
  have hb : b*Fintype.card (Tiles q d)+2 ≤ (b+2)*V := by
    rw [add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hH) (by omega)
  have hx : workBits B (Tiles q l) (Tiles q d) (keyWidth q d) w ^3 ≤ A^3*P := by
    apply (Nat.pow_le_pow_left (digitWidths B q h w).1 3).trans
    rw [mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) hp)
  have hw : (w+1)^e ≤ P :=
    (Nat.pow_le_pow_left (show w+1 ≤ S by dsimp [S]; omega) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) he)
  have hvp : 1 ≤ V*P := Nat.mul_pos hV hP
  apply (childCost_le B (Tiles q l) (Tiles q d) _ w C e).trans
  calc
    _ ≤ 2*(V*P) + 600*b*(3*V)*(A^3*P) + b*V*C*P + 2400*((b+2)*V)*(A^3*P) := by
      change 2 + 600*b*_ * _ + b*_ * C * _ + 2400*(b*_+2)*_ ≤ _
      gcongr
      · omega
    _ = V * childFactor b A C * P := by unfold childFactor; ring

/-- All levels of the tower use a common gate bound linear in the full
product-cover volume and polynomial in the depth and numerical bit width. -/
theorem digitCost_uniform (B : Type*) [Fintype B] (q U t C e : ℕ) :
    ∃ D p : ℕ, ∀ l w d : ℕ, 1 ≤ d → d+1 ≤ l →
      digitCost B q d l w U t C e ≤ Fintype.card (Fin q → Deck l) * D * (l+w+1)^p := by
  let b := Fintype.card B
  let K := 90*q
  let M := 7^(3*q)
  let A := widthFactor b q
  let E := childFactor b A C
  let p := t+e+3
  let D := 3*K+1+5*M*K+1+M*q*(90+U)+(1+M*E+M*((15*A+3)*M+1))+K*(4*M+1)
  refine ⟨D,p,?_⟩
  intro l w d hd hl
  let V := Fintype.card (Tiles q l)
  let S := l+w+1
  let P := S^p
  have hV : 1 ≤ V := Fintype.card_pos
  have hS : 1 ≤ S := Nat.succ_pos _
  have hP : S ≤ P := by
    simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ p by dsimp [p]; omega)
  have h1 : 1 ≤ P := hS.trans hP
  have hVP : 1 ≤ V*P := Nat.mul_pos hV h1
  have hPV : P ≤ V*P := Nat.le_mul_of_pos_left _ hV
  have hH : Fintype.card (Tiles q (d+1)) ≤ V := card_mono q hl
  have hF : Fintype.card (Tiles q d) ≤ V := card_mono q (by omega)
  have hM : childCount q d ≤ M := childCount_le q d hd
  have hkd : keyWidth q d ≤ K*P :=
    (key_width q (show d ≤ l by omega)).trans (Nat.mul_le_mul_left _ hP)
  have hk : keyWidth q (d+1) ≤ K*P :=
    (key_width q hl).trans (Nat.mul_le_mul_left _ hP)
  have hku : keyWidth q (d+1) ≤ K*(V*P) := hk.trans (Nat.mul_le_mul_left _ hPV)
  have hW : width (d+1) ≤ 30*P :=
    Nat.mul_le_mul_left _ ((show d+1+1 ≤ S by dsimp [S]; omega).trans hP)
  have ht : (d+1+1)^t ≤ P :=
    (Nat.pow_le_pow_left (show d+1+1 ≤ S by dsimp [S]; omega) _).trans
      (Nat.pow_le_pow_right hS (show t ≤ p by dsimp [p]; omega))
  have hscore : scoreBits B (Tiles q (d+1)) w ≤ A*(V*P) :=
    (digitWidths B q hl w).2.trans (Nat.mul_le_mul_left _ (hP.trans hPV))
  have hchild : childCost B (Tiles q l) (Tiles q (d+1)) (keyWidth q (d+1)) w C e ≤ V*E*P :=
    child_cost_bound B q hl w C e p (by dsimp [p]; omega) (by dsimp [p]; omega)
  have hf : (childrenFrame q d).size ≤ V*(3*(K*P)+P)+(M*(K*P))*(V*4+V) := by
    apply (childrenFrame_size q d).trans
    gcongr
  unfold digitCost
  calc
    _ ≤ (V*(3*(K*P)+P)+(M*(K*P))*(V*4+V)) + (V*P) +
        (M*(V*q))*(3*(30*P)+U*P) +
        (V*P+M*(V*E*P)+M*((15*(A*(V*P))+3*(V*P))*M+(V*P))) +
        (K*(V*P))*(4*M+1) := by
      gcongr
      · omega
    _ = V*D*P := by unfold D; ring

/-- Summing the valid digit budgets through level `l` preserves one volume
factor, with one extra power of the common depth/bit-width bound. -/
theorem digitCost_sum (B : Type*) [Fintype B] (q U t C e : ℕ) :
    ∃ D p : ℕ, ∀ l w : ℕ,
      ∑ d ∈ (Finset.range l).filter (1 ≤ ·), digitCost B q d l w U t C e ≤
        Fintype.card (Fin q → Deck l) * D * (l+w+1)^p := by
  obtain ⟨D,p,h⟩ := digitCost_uniform B q U t C e
  refine ⟨D,p+1,?_⟩
  intro l w
  let budget := Fintype.card (Tiles q l) * D * (l+w+1)^p
  calc
    _ ≤ ∑ _d ∈ (Finset.range l).filter (1 ≤ ·), budget := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdl,hd⟩ := Finset.mem_filter.mp hd
      exact h l w d hd (Finset.mem_range.mp hdl)
    _ ≤ l * budget := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le ..).trans_eq (Finset.card_range _)
    _ ≤ (l+w+1)*budget := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by unfold budget; rw [pow_succ]; ring

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
