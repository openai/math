import OAI.Computability.IntegerMultiplication.Param.Shape

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Two runtime scales budget, wall. Any polynomial in wall negligible vs n, and
any polynomial in budget negligible vs room. Even factorials of lanes slushed. -/
namespace Param
open Filter

theorem budget_grows : Tendsto budget atTop atTop :=
  limitAbove (f:=lanes) (g:=budget) (fun _=> Nat.le_self_pow (by decide) _) dim_grows
theorem room_grows : Tendsto room atTop atTop := by
  refine tendsto_atTop.2 fun b=>?_
  filter_upwards [budget_grows.eventually (eventually_ge_atTop b),room_hold 1] with n h z
  simpa only [pow_one] using h.trans (by simpa only [pow_one] using z : budget n≤ room n)
theorem wall_grows : Tendsto wall atTop atTop :=
  limitAbove room_le room_grows

theorem rooms (c k : ℕ) :
    Large fun n=> c*(budget n+1)^k ≤ room n := by
  filter_upwards [budget_grows.eventually (eventually_ge_atTop (c*2^k)),room_hold (k+1)]
    with n h z
  have w := budget_p n
  refine le_trans ?_ z
  rw [pow_succ]
  have v := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (show budget n+1≤2*budget n by omega) k)
  rw [mul_pow] at v
  nlinarith [Nat.mul_le_mul_left (budget n^k) h]

theorem loads (c k : ℕ) :
    Large fun n=> c*(wall n+1)^k ≤ load n := by
  filter_upwards [wall_grows.eventually (eventually_ge_atTop (max 1 (c*2^k))),load_dom (k+1)]
    with n h z
  have w : 1≤wall n := by omega
  have hh : c*2^k ≤ wall n := by omega
  refine le_trans ?_ z
  rw [pow_succ]
  have v := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (show wall n+1≤2*wall n by omega) k)
  rw [mul_pow] at v
  nlinarith [Nat.mul_le_mul_left (wall n^k) hh]

theorem walls (c k : ℕ) :
    Large fun n=> c*(wall n+1)^k ≤ n := by
  filter_upwards [loads (16*c) k,eventually_ge_atTop (1:ℕ)]
    with n h v
  have z := (load_below n)
  have a := amount_l n
  nlinarith

theorem factor_b (d : ℕ) :
    Nat.factorial d ≤ 2^(d^2) := calc
  _ ≤ d^d := Nat.factorial_le_pow d
  _ ≤ (2^d)^d := Nat.pow_le_pow_left ((Nat.lt_pow_self (a:=2) (n:=d) (by decide)).le) d
  _ = _ := by rw [← pow_mul,pow_two]

/-- factorial envelope: arbitrary fixed multiple and any fixed power, absorbed even into the
smallest axis RAM values; underscores poly setup of s table. -/
theorem room_facts (c k:ℕ) :
    Large fun n=> c*(lanes n+1)^k*(Nat.factorial (lanes n))^k ≤ room n := by
  filter_upwards [cut_large,dim_grows.eventually (eventually_ge_atTop
    (max 2 (c+k+k)))] with n hh hn
  let d := lanes n
  have a : max 2 (c+k+k)≤ d := hn
  have b : d+1 ≤ 2^d := Nat.lt_pow_self (a:=2) (by decide)
  change c*(d+1)^k*(Nat.factorial d)^k ≤ _
  calc
    _ ≤ (2^d)*(2^d)^k*(2^(d^2))^k := by gcongr; omega; exact factor_b _
    _ = 2^(d+d*k+d^2*k) := by rw [← pow_mul,← pow_add,← pow_mul,← pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      refine le_trans ?_ ((Nat.pow_le_pow_right (by omega : 0<d) (by decide : 4 ≤ 29)).trans hh.1)
      have A : k ≤ d := by omega
      have B : 2≤d := by omega
      have t := Nat.mul_le_mul_left d A
      have i := Nat.mul_le_mul_left (d^2) A
      have j : d≤d^2 := Nat.le_self_pow (by decide) _
      have s : 2*d^2≤d^2*d := Nat.mul_le_mul_right _ B |>.trans (by rw [mul_comm])
      nlinarith [Nat.mul_le_mul_left (d^3) B]

end Param

end IntegerMultiplication
end Computability
end OAI
