import OAI.Computability.IntegerMultiplication.Net.Festival
import OAI.Computability.IntegerMultiplication.Net.Triple

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
namespace Carnival
open Finset Place
variable {T C : Type} (z : Loom T C) [DecidableEq T] [Fintype T] [Fintype C]
def bulk (h : ℤ) : ℤ :=
  ∑ w, (net z).cost (fun _ => allowance h) w

-- cost per kind of wire, surcharge only opening xdata
omit [Fintype T] [Fintype C] in
theorem bulk_data (h : ℤ) (hh : 2 ≤ h) (a : Keys T) :
    (net z).cost (fun _ => allowance h) (xW a) = h^3 ∧
    (net z).cost (fun _ => allowance h) (yW a) = h^3-1 := by
  simp [cost_net z h hh, sink_net, init_net, boundary, tribute, xW, yW, charge, xEntry]

omit [Fintype T] [Fintype C] in
theorem bulk_aux (h : ℤ) (hh : 2 ≤ h) (j : S) (p : Sub T) :
    (∀ x : T×T, (net z).cost (fun _ => allowance h) (qW j p (.inl x)) = h^3) ∧
    (∀ c : C, (net z).cost (fun _ => allowance h) (qW j p (.inr c)) = h^3+2*h) := by
  fin_cases j <;>
    norm_num [S, cost_net z h hh, sink_net, init_net, boundary, qW, charge, tribute]

theorem sum_total (h : ℤ) (hh : 2 ≤ h) :
    bulk z h = (Fintype.card (Bank T C) : ℤ)*h^3-(Fintype.card T)^3 +
      2*h*3*(Fintype.card T)^2*(Fintype.card C) := by
  unfold bulk
  simp_rw [Fintype.sum_sum_type]
  simp_rw [show ∀ a, (net z).cost (fun _ => allowance h) (.inl a) = h^3 from fun a => (bulk_data z h hh a).1,
    show ∀ a, (net z).cost (fun _ => allowance h) (.inr (.inl a)) = h^3-1 from fun a => (bulk_data z h hh a).2]
  simp_rw [Fintype.sum_prod_type]
  -- Sum Aux now
  simp_rw [Fintype.sum_sum_type]
  simp_rw [show ∀ j p a, (net z).cost (fun _ => allowance h) (.inr (.inr (j,p,.inl a))) =
        h^3 from fun j p a => (bulk_aux z h hh j p).1 a,
    show ∀ j p a, (net z).cost (fun _ => allowance h) (.inr (.inr (j,p,.inr a))) =
        h^3+2*h from fun j p a => (bulk_aux z h hh j p).2 a]
  simp [Bank, Keys, S, Sub, Aux]
  ring

end Carnival

-- specialization
abbrev Core := Fin 100
abbrev Piece := Triple Core
theorem v : Fintype.card Piece = 161700 := by
  rw [Triple.count, Fintype.card_fin]
  -- avoid norm_num choose huge
  -- choose = descFactorial / factorial
  have hx := Nat.descFactorial_eq_factorial_mul_choose 100 3
  norm_num [Nat.descFactorial, Nat.factorial] at hx
  omega

theorem size (C : Type) [Fintype C] : Fintype.card (Bank Piece C) =
    2*4227952113000000 + 3*161700^2*(161700^2+Fintype.card C) := by
  simp only [Bank, Fintype.card_sum, Fintype.card_prod, Aux, Fintype.card_sum]
  simp only [S, Keys, Sub, Fintype.card_fun, v, Fintype.card_fin]
  ring

-- savings even with bit opening allowance and phase larger number of centers
def radix : ℕ := 1000000
noncomputable def sigma : ℝ := 1-(1:ℝ)/(2^64)
theorem sigma_range : 0 < sigma ∧ sigma < 1 := by norm_num [sigma]
theorem gap {C : Type} [Fintype C] (e : Fintype.card C ≤ 101) (z : Loom Piece C) :
    (Carnival.bulk z 100 : ℝ) / (Fintype.card (Bank Piece C)) <
      (radix:ℝ) ^ sigma := by
  -- (radix)^sigma ≥ radix*(1 - radix/2^64)
  have r0 : (0:ℝ) < radix := by norm_num [radix]
  have hg : (radix:ℝ) * (1-(radix:ℝ)/(2^64)) ≤ (radix:ℝ)^sigma := by
    have hb : -(radix:ℝ) / 2^64 ≤ Real.log (radix:ℝ) * (-(1:ℝ)/2^64) := by
      have hl := Real.log_le_sub_one_of_pos r0
      linarith
    have := Real.add_one_le_exp (Real.log radix * (-(1:ℝ)/2^64))
    unfold sigma
    simp only [sub_eq_add_neg]; rw [ Real.rpow_add r0, Real.rpow_one,
      Real.rpow_def_of_pos r0]
    apply mul_le_mul_of_nonneg_left _ r0.le
    linarith
  apply lt_of_lt_of_le _ hg
  rw [Carnival.sum_total z 100 (by decide), size, v]
  push_cast
  norm_num [radix]
  -- linarith
  rw [div_lt_iff₀ (by positivity)]
  have e2 : (Fintype.card C : ℝ) ≤ 101 := by exact_mod_cast e
  linarith
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
