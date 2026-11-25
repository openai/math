import OAI.Computability.IntegerMultiplication.Cone.Stroke

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Scale IntegerMultiplication.Fourier Finset Param

variable {n:ℕ}
-- A local-pass witness covering output, ideal norm, and local compute error plus table assumptions.
noncomputable def flare (n:ℕ) : ℝ:=4*weight n
noncomputable section
variable {I:Type} (s:Finset I)
variable (x w:I→G n) (c:I→ℂ)
variable {B:ℝ} (N:1≤ B) (v:B≤ hi n 800) (p:∀ i∈s,‖look n (x i)‖≤B)
variable (q:∀ i∈s,‖c i‖≤ wash n)
variable (e:∀ i∈s,‖look n (w i)-c i‖ ≤ err n)
variable (H:(s.card:ℝ)≤ wash n)
theorem flare1 (n):1≤flare n := by unfold flare; linarith [weight1 n]
theorem flareBound (n): flare n^ lanes n ≤ hi n 26 := by
  unfold flare; rw [mul_pow]
  have g : (4:ℝ)^lanes n ≤ hi n 2 := by
    unfold hi; rw [show (4:ℝ)=(2:ℝ)^(2:ℕ) by norm_num,← pow_mul]
    have p : lanes n ≤ Scale.P n:= Nat.le_self_pow (by decide) _
    gcongr; norm_num
  calc
    _ ≤ hi n 2 * hi n 24 := by
      apply mul_le_mul g (weightPay _) (pow_nonneg (by linarith [weight1 n]) _) (by linarith [hi1 n 2])
    _ = _ := by rw [Scale.heightA]

include N p v q e H
theorem ember :
    let u:=∑ i∈s, punch (x i) (w i)
    ‖look n u‖ ≤ B*flare n ∧
    ‖look n u-∑ i∈s,c i*look n (x i)‖≤ err n*(B*flare n) := by
  classical
  have g i (v_:i∈s):=gentle N (p i v_) (q i v_) (e i v_) v
    (le_trans (wash_le _) (hi_mono n (by decide :24≤32)))
  let t i:= look n (punch (x i) (w i))
  let z:=∑ i∈s,t i
  have A:=wash1 n; have Q:=weight1 n
  have P : ‖z‖≤ B*flare n := by
    have e₁:= norm_sum_le_of_le s (f:=t) (n:=fun _=>B*(wash n+2)) (fun i h=>(g i h).2)
    simp only [sum_const,nsmul_eq_mul] at e₁
    apply e₁.trans
    unfold flare
    rw [← wash_sq]
    nlinarith [mul_le_mul_of_nonneg_right H
      (show 0≤B*(wash n+2) by positivity),
      mul_le_mul_of_nonneg_left (show wash n+2≤4*wash n by linarith) (show 0≤B*wash n by positivity)]
  have j : ‖z‖ * 2^Scale.F n < (2:ℝ)^Scale.W n := by
    have i : flare n≤ hi n 26 :=
      (le_self_pow₀ (flare1 n) (by have v:=lanes_pos n; omega)).trans (flareBound n)
    have t:=model n
    calc
      _ ≤ (B*flare n)*2^Scale.F n := by gcongr
      _ ≤ (hi n 800*hi n 26)*2^Scale.F n := by gcongr <;> linarith [flare1 n,hi1 n 800]
      _ < _ := by
        rw [heightA]
        have e:=hi_mono n (by decide : 800+26 ≤1000)
        nlinarith [mul_le_mul_of_nonneg_right e (show 0≤(2:ℝ)^Scale.F n by positivity)]
  have C: look n (∑ i∈s,punch (x i) (w i))= z :=
    joined s (fun i=>punch (x i) (w i)) j
  dsimp only; rw [C,show z=∑ i∈s,t i from rfl,← sum_sub_distrib]
  refine ⟨P,?_⟩
  have e0:= invp n
  have E:=norm_sum_le_of_le s (f:=fun i=>t i - c i*look n (x i)) (n:=fun _=>2*err n*B)
    (fun i h=> by rw [mul_comm]; exact (g i h).1)
  simp only [sum_const,nsmul_eq_mul] at E
  apply E.trans
  unfold flare; rw [← wash_sq]
  calc
    _ ≤ wash n*(2*err n*B) := by gcongr
    _ = err n*(B*(2*wash n)) := by ring
    _ ≤ _ := by gcongr <;> nlinarith
end
end Cone

end IntegerMultiplication
end Computability
end OAI
