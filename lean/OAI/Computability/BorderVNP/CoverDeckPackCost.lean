import OAI.Computability.BorderVNP.CoverDeckDigitFrames
import OAI.Computability.BorderVNP.PackedDeckCandidateCost
import OAI.Computability.BorderVNP.PackedDeckWeightedChoice
import OAI.Computability.RationalHitting.Feasibility

/-!
# Linear-volume cost of the finite pack choice

The high cover contributes one lane per actual product tile. Only its binary
key width enters the polynomial factors in the sorting and scoring costs.
The number of candidates and the number of relative bins are fixed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting PackedDeckScore

private theorem log_lanes (m q l : ℕ) :
    Nat.clog 2 (m*Fintype.card (Fin q → Deck l)+2) ≤ m+2+keyWidth q l := by
  have h : Fintype.card (Fin q → Deck l) ≤ 2^(keyWidth q l) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (productKey q l).injective
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  calc
    _ ≤ m*2^(keyWidth q l)+2*2^(keyWidth q l) := Nat.add_le_add (Nat.mul_le_mul_left m h)
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    _ = (m+2)*2^(keyWidth q l) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (m+2).lt_two_pow_self.le

private def keyBound (q : ℕ) : TimeBound := .const (90*q) * TimeBound.variable

private theorem key_le (q l w : ℕ) : keyWidth q l ≤ (keyBound q).eval (l+w+1) := by
  change q*(30*(l+1)*3) ≤ 90*q*(l+w+1)
  calc
    _ = 90*q*(l+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

private def channelBound (B : Type*) [Fintype B] (q C e M z : ℕ) : TimeBound :=
  let X := TimeBound.variable
  let L := .const (batchBits B Unit) + (keyBound q+3) + X + 1
  let b := Fintype.card B
  1 + .const b * (2 + 7200*3*L^3 + .const C*X^e + 9*(.const M*X^z+X*(16*X+22)+1)) +
    2400 * .const (b+2) * L^3

private theorem channel_le (B : Type*) [Fintype B] (q l w C e M z : ℕ) :
    PackedDeckCandidate.channelCost B (Fin q → Deck l) w C e M z ≤
      Fintype.card (Fin q → Deck l) * (channelBound B q C e M z).eval (l+w+1) := by
  let G := Fin q → Deck l
  let V := Fintype.card G
  let b := Fintype.card B
  let S := l+w+1
  let L := batchBits B Unit + ((keyBound q).eval S+3) + S + 1
  have hv : 1 ≤ V := Fintype.card_pos
  have hw : w+1 ≤ S := by dsimp [S]; omega
  have hw' : w ≤ S := by omega
  have hkey := key_le q l w
  have hlog := log_lanes 1 q l
  have hg : batchBits G Unit ≤ (keyBound q).eval S+3 := by
    change Nat.clog 2 (V+1) ≤ _
    have hl : Nat.clog 2 (V+1) ≤ Nat.clog 2 (V+2) := Nat.clog_mono_right _ (by omega)
    simp only [one_mul] at hlog
    dsimp [S,V,G] at *; omega
  have hL : PackedDeckCandidate.workBits B G w ≤ L := by
    dsimp only [PackedDeckCandidate.workBits,L]; omega
  have hcount : V+2 ≤ 3*V := by omega
  have hscalar : 9*(M*(w+1)^z+w*(16*w+22)+1) ≤ V*(9*(M*S^z+S*(16*S+22)+1)) :=
    (show _ ≤ 9*(M*S^z+S*(16*S+22)+1) by gcongr).trans (Nat.le_mul_of_pos_left _ hv)
  have hsum : 2400*(b+2)*PackedDeckCandidate.workBits B G w^3 ≤ V*(2400*(b+2)*L^3) :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 3)).trans (Nat.le_mul_of_pos_left _ hv)
  apply (PackedDeckCandidate.channelCost_le B G w C e M z).trans
  calc
    _ ≤ V + b*(2*V+7200*(3*V)*L^3+V*(C*S^e)+V*(9*(M*S^z+S*(16*S+22)+1))) +
        V*(2400*(b+2)*L^3) := by
      change 1+b*(2+7200*(V+2)*_+V*(C*(w+1)^e)+9*(M*(w+1)^z+w*(16*w+22)+1))+
        2400*(b+2)*_ ≤ _
      gcongr
      omega
    _ = V*(channelBound B q C e M z).eval S := by
      simp only [channelBound,L,b,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,
        TimeBound.eval_const,TimeBound.eval_numeral,TimeBound.eval_variable]; ring

private def meanBound (m q U t : ℕ) : TimeBound :=
  let X := TimeBound.variable
  let A := .const (m+2) + keyBound q + X + 1
  .const (m+1)*(2*X) + (1 + .const (m+1)*(.const U*X^t) + 2400*.const (m+2)*A^3)

private theorem mean_le (m q l w U t : ℕ) :
    PackedDeckMean.meanCost (Fin q → Deck l) m w U t ≤
      Fintype.card (Fin q → Deck l) * (meanBound m q U t).eval (l+w+1) := by
  let V := Fintype.card (Fin q → Deck l)
  let S := l+w+1
  let A := m+2 + (keyBound q).eval S + S + 1
  have hV : 1 ≤ V := Fintype.card_pos
  have hW : w+1 ≤ S := by dsimp [S]; omega
  have hw : w ≤ S := by omega
  have hn : m*V+1 ≤ (m+1)*V := by rw [add_mul,one_mul]; omega
  have hn' : m*V+1+1 ≤ (m+2)*V := by rw [add_mul]; omega
  have hb : Nat.clog 2 (m*V+1+1)+w+1 ≤ A := by
    change Nat.clog 2 (m*V+2)+w+1 ≤ A
    have h := log_lanes m q l
    have hk := key_le q l w
    dsimp only [A,S,V] at *; omega
  apply (PackedDeckMean.meanCost_le (Fin q → Deck l) m w U t).trans
  calc
    _ ≤ ((m+1)*V)*(2*S) + (V+((m+1)*V)*(U*S^t)+2400*((m+2)*V)*A^3) := by
      change (m*V+1)*(2*w)+(1+(m*V+1)*(U*(w+1)^t)+2400*(m*V+1+1)*_ ) ≤ _
      gcongr
    _ = V*(meanBound m q U t).eval S := by
      simp only [meanBound,A,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,
        TimeBound.eval_numeral,TimeBound.eval_const,TimeBound.eval_variable]; ring

/-- The motion scoring, mean update, and two selected count banks together
cost one factor of actual product-tile volume times a polynomial in the sum
of the cover depth and count width. The polynomial is common to every pack. -/
theorem packCost_uniform (B : Type*) [Fintype B] (q m U t C e M z : ℕ) :
    ∃ D p : ℕ, ∀ l w : ℕ,
      PackedDeckMean.candidateCost B (Fin q → Deck l) m w U t C e M z +
        Fintype.card (CountBits B q l w)*(4*m+1) ≤
          Fintype.card (Fin q → Deck l)*D*(l+w+1)^p := by
  let b := Fintype.card B
  let X := TimeBound.variable
  let A : TimeBound := X + .const (Nat.clog 2 (b+1)) + 1
  let choice : TimeBound := .const (m*m)*A*(16*A+22) + .const m*((15*A+3)*.const m+1)
  let budget := (1 + .const b * meanBound m q U t) +
    (1 + .const (m*2)*channelBound B q C e M z + choice) + .const (2*b)*X*.const (4*m+1)
  obtain ⟨D,p,_,_,hg⟩ := budget.growth
  refine ⟨D,p,?_⟩
  intro l w
  let G := Fin q → Deck l
  let V := Fintype.card G
  let S := l+w+1
  have hV : 1 ≤ V := Fintype.card_pos
  have hw : w ≤ S := by dsimp [S]; omega
  have ha : sumBits B w + 1 ≤ A.eval S := by
    change w + Nat.clog 2 (b+1) + 1 ≤ S + Nat.clog 2 (b+1) + 1; omega
  have hsel : m*m*(sumBits B w+1)*(16*(sumBits B w+1)+22) +
        m*((15*(sumBits B w+1)+3)*m+1) ≤ V*choice.eval S := by
    apply (Nat.le_mul_of_pos_left _ hV).trans'
    change _ ≤ m*m*A.eval S*(16*A.eval S+22)+m*((15*A.eval S+3)*m+1)
    gcongr
  have hcard : Fintype.card (CountBits B q l w) = 2*b*V*w := by
    simp only [CountBits,b,V,G,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]; ring
  have hm := mean_le m q l w U t
  have hc := channel_le B q l w C e M z
  calc
    _ ≤ (V+b*(V*(meanBound m q U t).eval S)) +
        (V + m*2*(V*(channelBound B q C e M z).eval S) + V*choice.eval S) +
        2*b*V*S*(4*m+1) := by
      rw [hcard]
      unfold PackedDeckMean.candidateCost
      rw [Nat.add_assoc (1+m*2*_) (m*m*_ *_) (m*_)]
      gcongr
    _ = V*budget.eval S := by
      simp only [budget,X,TimeBound.eval_mul,TimeBound.eval_add,TimeBound.eval_const,
        TimeBound.eval_variable,TimeBound.eval_numeral]; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using Nat.mul_le_mul_left V (hg S (by dsimp [S]; omega))

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
