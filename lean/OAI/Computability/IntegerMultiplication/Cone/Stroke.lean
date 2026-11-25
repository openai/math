import OAI.Computability.IntegerMultiplication.Echo.Stability

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Finset Scale IntegerMultiplication.Star Grid Dusk
variable {n:ℕ}
abbrev G (n:ℕ) := Grain (W n)
noncomputable def look (n) (x:G n): ℂ := meaning (Scale.F n) (W n) x
@[simp] theorem lookingZero (n):look n 0=0 := by
  unfold look meaning
  rw [← map_zero (wrapMap (W n)), Grid.recovers _ (show focus (W n) 0 from by
    unfold focus Grid.tiny; simp),map_zero, zero_div]

abbrev punch {n} (x u:G n):G n :=
  Grid.launch (x, Code.tally (Scale.F n),Dusk.mark u)
-- line column rounding lemma if magnitude ≤ hi800 and table factor ≤hi32.
theorem gentle {x u:G n} {c:ℂ} {B C:ℝ} (u_:1≤B)
    (b:‖look n x‖≤B) (q: ‖c‖≤C) (p:‖look n u-c‖ ≤ err n)
    (v:B ≤ hi n 800) (d:C≤hi n 32) :
    ‖look n (punch x u)-look n x*c‖ ≤ 2*err n*B ∧
    ‖look n (punch x u)‖≤ B*(C+2) := by
  let X:=look n x
  let U:=look n u
  let e:=err n
  have e₀ : 0≤e:=(invp n).le
  let Y:=look n (punch x u)
  have i : ‖U‖≤2*hi n 32 := by
    have h:=norm_add_le (U-c) c
    rw [sub_add_cancel] at h
    change ‖U-c‖≤_ at p
    linarith [hi1 n 32,err1 n]
  have h: ‖X*U‖*2^Scale.F n+2 < (2:ℝ)^W n := by
    apply lt_of_le_of_lt _ (model _)
    gcongr
    rw [norm_mul]
    have T : 0≤ hi n 800 := by linarith [hi1 n 800]
    calc
     _ ≤ hi n 800 * (2*hi n 32) :=
        mul_le_mul (b.trans v) i (norm_nonneg _) T
     _ = 2*(hi n 800*hi n 32) := by ring
     _ = 2*hi n (800+32) := by rw [heightA]
     _ ≤ _ := (overhead ..).trans (hi_mono n (by decide :800+32+1≤1000))
  have g:= Grid.confident (Scale.F n) x u h
  have E : ‖Y-X*U‖≤e :=
    calc
      _ ≤ (2:ℝ)/ 2^Scale.F n:=g
      _ ≤ 3*drop_ (Scale.F n) := by unfold drop_; rw [one_div,inv_pow, ← div_eq_mul_inv]; gcongr;norm_num
      _ ≤ _ := round_n n
  change ‖Y-X*c‖≤_ ∧ ‖Y‖≤_
  have z : ‖Y-X*c‖≤2*err n * B := by
    rw [show Y-X*c=(Y-X*U)+X*(U-c) from by ring]
    calc
     _ ≤ ‖Y-X*U‖+‖X*(U-c)‖ := norm_add_le _ _
     _ ≤ e+B*e := by rw [norm_mul]; exact add_le_add E (mul_le_mul b p (norm_nonneg _) (by linarith))
     _ ≤ _ := by change _ ≤ 2*e*B; nlinarith
  refine ⟨z,?_⟩
  have s:=norm_add_le (Y-X*c) (X*c)
  rw [sub_add_cancel,norm_mul] at s
  change ‖X‖≤B at b
  have g:= mul_le_mul b q (norm_nonneg _) (by linarith : 0≤B)
  nlinarith [mul_le_mul_of_nonneg_right (err1 n) (by linarith:0≤B)]

-- sum reliability via wrapping
theorem joined {I:Type} (s:Finset I) (X:I→G n)
    (h : ‖∑ i∈s, look n (X i)‖*(2:ℝ)^Scale.F n < (2:ℝ)^W n):
    look n (∑ i∈s,X i) = ∑ i∈s,look n (X i) := by
  classical
  let z : I→Cell:=fun i=>aspect (X i)
  let A:=∑ i∈s,z i
  have K: ∑ i∈s,X i=wrapMap (W n) A:= by unfold A z; rw [map_sum]; simp
  have Z : ∑ i∈s,look n (X i)= toC A/(2:ℂ)^Scale.F n := by
    unfold A look z meaning; rw [map_sum,Finset.sum_div]
  rw [Z] at h ⊢
  have p: focus (W n) A := by
    apply Grid.short _ (into _)
    simpa only [norm_div,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,
      div_mul_cancel₀ _ (by positivity : (2:ℝ)^Scale.F n≠0)] using h
  rw [look,K,meaning,Grid.recovers _ p]
end Cone

end IntegerMultiplication
end Computability
end OAI
