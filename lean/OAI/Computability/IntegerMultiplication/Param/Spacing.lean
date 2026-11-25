import OAI.Computability.IntegerMultiplication.Param.Saves
import Mathlib.Data.Nat.Prime.Basic

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Nat URL-gap construction from project independent variant Docs/Roadmap. -/
namespace Param

structure Margin (d t s : ℕ) : Prop where
  above : (8*d-2)*t ≤ (8*d)*s
  below : (8*d)*s ≤ (8*d-1)*t
-- basic facts
namespace Margin
variable {d t s:ℕ}
theorem strict (m : Margin d t s) (v : 1≤ t) (e : 1≤d) :
    s < t := by
  by_contra! h
  have w := m.below
  have p : 8*d=(8*d-1)+1 := by omega
  nlinarith [Nat.mul_le_mul_left (8*d) h]

theorem far (m : Margin d t s) (e : 1≤d) :
    t ≤ 2*s := by
  have p : 8*d=(8*d-2)+2 := by omega
  have w := m.above
  by_contra! h
  have z := Nat.mul_le_mul_left (8*d-2) (by omega : 2*s+1≤t)
  nlinarith [Nat.mul_le_mul_left s e]

theorem ratio (m : Margin d t s) (v : 1≤d) :
    ((1:ℝ)+1/(8*d))*(s:ℕ)≤(t:ℝ) := by
  have d₀ : (1:ℝ)≤d := by exact_mod_cast v
  have P : (8:ℝ)*d*s ≤ (8*d-1)*t := by
    have u := m.below
    have q : 1≤ 8*d := by omega
    have : ((8*d:ℕ):ℝ)*s ≤ ((8*d-1:ℕ):ℝ)*t := by exact_mod_cast u
    push_cast [q] at this
    exact this
  have t₁ : s ≤ t := by
    rcases t with _ | n
    · simp only [mul_zero, Nat.cast_zero, Nat.le_zero] at *
      by_contra! h
      have z : (0:ℝ)<s := by exact_mod_cast (by omega : 0<s)
      nlinarith [mul_pos (by linarith : 0<(8:ℝ)*d) z]
    · exact Nat.le_of_lt (m.strict (by omega) v)
  have A : 0<(8:ℝ)*(d:ℝ) := by linarith
  apply le_of_mul_le_mul_left (a:=(8:ℝ)*(d:ℝ)) ?_ A
  have q : (8:ℝ)*d*((1+1/(8*d))*s)=(8*(d:ℝ)+1)*s := by field_simp
  rw [q]
  have z : (s:ℝ)≤t := by exact_mod_cast t₁
  nlinarith
end Margin

-- short odd square
def high8 (d : ℕ) := 8*d
def seed (d t : ℕ) := ((high8 d-1)*t)/(high8 d)
def root_ d t := 2*(Nat.sqrt (seed d t)/2)-1

theorem square_{d t : ℕ} (v : 1 ≤ d) (w:(256*d)^2≤ t) :
    let J := root_ d t
    Odd J ∧ 64*d ≤ J ∧ Margin d t (J^2) := by
  let D := high8 d
  let u := seed d t
  let q := Nat.sqrt u
  let J := root_ d t
  change Odd J ∧ 64*d ≤ J ∧ Margin d t (J^2)
  have d₁ : 8 ≤ D := by unfold D high8; omega
  have d₂ : D-1+1=D := by omega
  have hp : (66*d)^2 ≤ u := by
    unfold u seed
    apply (Nat.le_div_iff_mul_le (by omega : 0<D)).mpr
    change _*D ≤ (D-1)*t
    have a : 2*(66*d)^2 ≤ t := le_trans (by nlinarith : _ ≤ (256*d)^2) w
    calc
      _ ≤ (66*d)^2*(2*(D-1)) := by gcongr; omega
      _ = (D-1)*(2*(66*d)^2) := by ring
      _ ≤ _ := by gcongr
  have hq : 66*d ≤ q := Nat.le_sqrt'.mpr hp
  have hj : J≤q ∧ q≤J+2 := by unfold J root_; change _ ≤ q ∧ q ≤ 2*(q/2)-1+2; change 2*(q/2)-1≤ q ∧ _; omega
  have hJ : 64*d≤ J := by omega
  have s0 : J^2≤u := le_trans (Nat.pow_le_pow_left hj.1 2) (Nat.sqrt_le' _)
  have s1 : u < (J+3)^2 := (Nat.lt_succ_sqrt' u).trans_le (Nat.pow_le_pow_left (by change q+1 ≤ _; omega) 2)
  have v0 : D*J^2 ≤ (D-1)*t := by
    apply le_trans (Nat.mul_le_mul_left D s0)
    unfold u seed; change D*(_/D)≤_; rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have v1 : (D-1)*t < D*(J+3)^2 := by
    unfold u seed at s1
    rw [Nat.div_lt_iff_lt_mul (show 0<D by omega)] at s1
    rw [mul_comm D]
    exact s1
  -- D*(6J+9) ≤ t
  have a : J^2 ≤ t := by
    refine s0.trans ?_
    -- u ≤ ((D)*t)/D
    unfold u seed
    change (D-1)*t/D ≤ _
    calc
     _ ≤ D*t/D := Nat.div_le_div_right (by gcongr; omega)
     _ = _ := Nat.mul_div_cancel_left t (by omega)
    -- rw t everywhere!
  have e : D*(6*J+9) ≤ t := by
    refine le_trans ?_ a
    have h : 6*J+9 ≤ 7*J := by omega
    calc
     _ ≤ D*(7*J) := by gcongr
     _ = (7*D)*J := by ring
     _ ≤ _ := by rw [pow_two]; apply Nat.mul_le_mul_right; unfold D high8; omega
  refine ⟨?_,hJ,⟨?_,v0⟩⟩
  · refine ⟨q/2-1,?_⟩
    unfold J root_
    change 2*(q/2)-1=_
    omega
  change (D-2)*t≤ _
  change (D-2)*t≤ D*J^2
  have c : D-1=(D-2)+1 := by omega
  rw [show (J+3)^2=J^2+(6*J+9) by ring,Nat.mul_add] at v1
  nlinarith

end Param

end IntegerMultiplication
end Computability
end OAI
