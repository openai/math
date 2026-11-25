import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentStackScale

namespace OAI
/-! # Choosing the integral initial grain of the actual stage schedule -/

namespace Hierarchy.DescentCompiler
open Filter

/-- The factor at the right end of the first stage is retained in the initial
population. The chosen grain is therefore divisible as required at every
ordinary step, while its ratio to the physical word width is bounded. -/
theorem AtomSchedule.open_grain_width (t b ℓ a B : ℕ) (bpos : 0<b)
    (cap : b≤2^ℓ) (pos : 0<B) (room : 2*a+ℓ*(t+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ S : AtomSchedule, S.rounds=t → S.height=J →
      ∀ q : ℕ, 0<q → q≤2^(a*(J+1)) →
        let U:=b^(t*J)*b
        let p:=h/(16*(q*U))
        0<p ∧ 0<S.firstWidth b p ∧ S.firstWidth b p≤h ∧
          16*(q*S.firstWidth b p)≤h ∧ h≤32*(q*S.firstWidth b p) := by
  filter_upwards [age_room B pos] with h paid
  let J:=Nat.log 2 h/(2*B)
  change 0<J ∧ 32*(2^J)^B≤h at paid
  dsimp only
  intro S period age q hq socket
  let U:=b^(t*J)*b
  let p:=h/(16*(q*U))
  have capU : U≤(2^ℓ)^(t*J+1) := by
    dsimp only [U]
    rw [←pow_succ]
    exact Nat.pow_le_pow_left cap _
  have budget : q*U ≤ (2^J)^B := calc
    _ ≤ 2^(a*(J+1))*(2^ℓ)^(t*J+1) := Nat.mul_le_mul socket capU
    _ = 2^(a*(J+1)+ℓ*(t*J+1)) := by rw [←pow_mul,←pow_add]
    _ ≤ 2^(J*(2*a+ℓ*(t+1))) := by
      apply Nat.pow_le_pow_right (by decide : 0<2)
      have mulA:=Nat.le_mul_of_pos_right a paid.1
      have mulL:=Nat.le_mul_of_pos_right ℓ paid.1
      nlinarith only [mulA,mulL]
    _ ≤ _ := by
      rw [←pow_mul]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left J room)
  have size : 32*(q*U)≤h := (Nat.mul_le_mul_left 32 budget).trans paid.2
  have hU : 0<U := Nat.mul_pos (Nat.pow_pos bpos) bpos
  obtain ⟨positive,start,low,high⟩ := packing_width hU hq size
  have equal : S.firstWidth b p = p*U := by
    rw [firstWidth,grain_initial,period,age]
    exact Nat.mul_assoc ..
  change 0<p ∧ 0<S.firstWidth b p ∧ S.firstWidth b p≤h ∧
    16*(q*S.firstWidth b p)≤h ∧ h≤32*(q*S.firstWidth b p)
  rw [equal]
  have lift : p*U≤q*(p*U) := Nat.le_mul_of_pos_left _ hq
  exact ⟨positive,start,lift.trans ((by omega : q*(p*U)≤16*(q*(p*U))).trans low),low,high⟩

end Hierarchy.DescentCompiler

end OAI
