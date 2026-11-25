import OAI.Computability.IntegerMultiplication.Param.Base

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param
open Filter

/-- upper division -/
def rise (n a:ℕ) := (n+a-1)/a

theorem rise_upper {a n} (h : 1≤a) : n ≤ a*rise n a := by
  let b := n+a-1
  have u : b%a + a*rise n a = b := Nat.mod_add_div b a
  have v : b%a<a := Nat.mod_lt _ (by omega)
  unfold b at *; omega
theorem rise_lower {a n} (h : 1≤a) : a*rise n a < n+a := by
  let b := n+a-1
  have u : b%a + a*rise n a = b := Nat.mod_add_div b a
  unfold b at *; omega
theorem rise_le {a n} (h : 1≤a) : rise n a ≤ n := by
  have v := rise_lower (a:=a) (n:=n) h
  by_contra! e
  have t : a*(n+1)≤ a*rise n a := Nat.mul_le_mul_left _ e
  nlinarith [Nat.mul_le_mul_right n h]
theorem rise_p {a n} (h : 1≤a) (t : 1≤n) : 1≤ rise n a := by
  have v := rise_upper (a:=a) (n:=n) h
  cases hh: rise n a with
  | zero => rw [hh] at v; simp at v; omega
  | succ => omega

def amount n := rise n (budget n)
def total n := Nat.clog 2 (4*amount n)
def span_ n := rise (total n) (lanes n)
def slack n := lanes n*span_ n-total n
def reach n := span_ n-slack n
def load n := (2:ℕ)^total n
def wall n := (2:ℕ)^span_ n
def room n := (2:ℕ)^reach n
-- load ≥ 4 digits. etc
theorem load_above (n) :
    4*amount n ≤ load n := Nat.le_pow_clog (by decide) _
theorem load_below (n) :
    load n ≤ 2*(4*amount n+1) := logBound _
theorem budget_times (n) :
    n ≤ budget n*amount n := rise_upper (budget_p n)
theorem full_volume :
    Large fun n=> budget n*load n ≤ 32*n := by
  filter_upwards [ringlet 1 1,eventually_gt_atTop (0:ℕ)] with n hn _
  simp only [pow_one,one_mul] at hn
  have ha : budget n*amount n < n+budget n := rise_lower (budget_p n)
  have h := Nat.mul_le_mul_left (budget n) (load_below n)
  nlinarith

theorem amount_l (n) : amount n ≤n := rise_le (budget_p n)

theorem total_below (n) : total n ≤ beta n+2 := by
  rw [total,Nat.clog_le_iff_le_pow (by decide),pow_add,mul_comm (2^_) (2^_)]
  have t : n ≤ 2^beta n := (Nat.le_pow_clog (b:=2) (by decide) n).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_right ..))
  exact Nat.mul_le_mul_left _ ((amount_l n).trans t)

theorem total_above (n) : beta n ≤ 32*height n+total n := by
  refine max_le (by have : 1≤height n := by unfold height; omega
                    omega) ((Nat.clog_le_iff_le_pow (by decide)).2 ?_)
  rw [pow_add,mul_comm (32:ℕ),← budget_shape]
  exact (budget_times n).trans (Nat.mul_le_mul_left (budget n) (le_trans
    (by omega : amount n ≤ 4*amount n) (load_above n)))

theorem split_hi (n) : total n ≤ lanes n*span_ n :=
  rise_upper (lanes_pos n)
theorem split_lo (n) : lanes n*span_ n < total n+lanes n :=
  rise_lower (lanes_pos n)
theorem slack_part (n) : total n + slack n = lanes n*span_ n :=
  Nat.add_sub_of_le (split_hi n)
theorem slack_lt (n) : slack n < lanes n := by
  have := slack_part n; have := split_lo n; omega
theorem log_lanes (n) : height n ≤ lanes n :=
  (Nat.lt_pow_self (a:=2) (n:=height n) (by decide)).le
theorem budget_le (n) : budget n ≤ 2^36 * (32*lanes n + lanes n*span_ n) :=
  (beyond n).trans (Nat.mul_le_mul_left _ ((total_above n).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (log_lanes n)) (split_hi n))))

theorem span_large :
    Large fun n=> lanes n^30 ≤ span_ n := by
  filter_upwards [dim_grows.eventually (eventually_ge_atTop (2^43:ℕ))] with n hn
  let d:=lanes n
  have v : 2^43 ≤ d := hn
  have v₁ : 0<d := lanes_pos n
  have p₁ : 1≤d^30 := Nat.one_le_pow _ _ v₁
  have h : d^31 ≤ 2^36 * (32+span_ n) := by
    refine Nat.le_of_mul_le_mul_left (show d*d^31≤d*(2^36*(32+span_ n)) from ?_) ?_
    · calc
       d*d^31 = budget n := by change d*d^31=d^32; ring
       _ ≤ _ := (budget_le n).trans (by unfold d; ring_nf; exact le_rfl)
    · exact v₁
  rw [show d^31=d^30*d by ring] at h
  change d^30≤_
  have e := Nat.mul_le_mul_left (d^30) v
  norm_num1 at *
  omega

theorem cut_large :
    Large fun n=> lanes n^29 ≤ reach n ∧ reach n+slack n=span_ n := by
  filter_upwards [dim_grows.eventually (eventually_ge_atTop 2),span_large] with n hn v
  let d:=lanes n
  have w : d ≤ d^29 := Nat.le_self_pow (by decide) _
  have z : 2*d^29 ≤ lanes n^30 := by
    change 2*d^29 ≤ d^30
    rw [show d^30=d*d^29 by ring]
    gcongr
  have t : slack n < d := slack_lt _
  unfold reach
  change d^29 ≤ _ ∧ _
  omega

theorem room_le (n) : room n ≤ wall n :=
   Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)

theorem span_le (n) : span_ n ≤ budget n+2 := calc
   _ ≤ total n := rise_le (lanes_pos _)
   _ ≤ _ := (total_below n).trans (by have h:=four_beta n; omega)
-- wall ≤2^p needs sharpen
theorem wall_small (n) : lanes n*span_ n ≤ budget n := by
  have h := split_lo n
  have b := total_below n
  have g := four_beta n
  -- prove 2*lanes ≤ budget, beta≥2 or height >=1 -> room
  have x : 1 ≤ height n := by unfold height; omega
  let d := lanes n
  have d₁ : 2≤ d :=
    (show 2≤2^(1:ℕ) by decide).trans (Nat.pow_le_pow_right (n:=2) (by decide) x)
  have y : 2*d ≤ budget n := by
    refine (Nat.mul_le_mul_right d d₁).trans ?_
    rw [← pow_two]; exact Nat.pow_le_pow_right (lanes_pos n) (by decide : 2≤32)
  have w : 16 ≤ budget n :=
    (show 16 ≤ (2:ℕ)^4 by decide).trans ((Nat.pow_le_pow_left d₁ 4).trans
      (Nat.pow_le_pow_right (lanes_pos n) (by decide : 4 ≤ 32)))
  unfold d at *; omega

theorem sp_le (n) : span_ n ≤ budget n :=
  le_trans (Nat.le_mul_of_pos_left _ (lanes_pos n)) (wall_small n)

theorem upright (n): wall n ≤ (2:ℕ)^budget n :=
  Nat.pow_le_pow_right (by decide) (sp_le n)

-- for table setup (2^ell)^c p^c inside 2^total
theorem aspect (n) (_h : 1≤span_ n) (_t : 2≤lanes n) : (lanes n-1)*span_ n ≤ total n + lanes n := by
  have j:= Nat.mul_le_mul_right (span_ n) (Nat.sub_le (lanes n) 1)
  have i:= split_lo n
  omega

theorem load_dom (c : ℕ) :
    Large fun n=> wall n^c ≤ load n := by
  filter_upwards [dim_grows.eventually (eventually_ge_atTop (2*(c+2))),span_large] with n hn v
  unfold wall load; rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  let d:=lanes n
  have h : 2≤ d := by dsimp [d]; omega
  have hm : 2 ≤ d^30 := (le_trans h (by exact Nat.le_self_pow (by decide) _))
  have t := split_lo n
  change d*_ < _+d at t
  have i := Nat.mul_le_mul_right (span_ n) hn
  change _ ≤ d*_ at i
  change d^30≤_ at v
  nlinarith [Nat.mul_le_mul_left d (by omega: 2≤span_ n)]
-- budget powers <=2^reach eventually via expose.
theorem room_hold (c : ℕ) :
    Large fun n=> budget n^c ≤ room n := by
  filter_upwards [cut_large,dim_grows.eventually (eventually_ge_atTop (max 2 (32*c))),
    dim_grows.eventually (beats 1 (32*c))] with n h d v
  simp only [one_mul] at v
  unfold budget
  rw [← pow_mul]
  exact v.trans (Nat.pow_le_pow_right (by decide) ((Nat.le_self_pow (by decide) _).trans h.1))

end Param

end IntegerMultiplication
end Computability
end OAI
