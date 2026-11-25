import OAI.Computability.IntegerMultiplication.Param.Space
import OAI.Computability.IntegerMultiplication.Param.Payout
import OAI.Computability.IntegerMultiplication.Fourier.Accuracy

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Scale
open IntegerMultiplication.Fourier Param Filter

def P(n:ℕ) := Param.budget n
def F(n:ℕ) := 4096*P n
def W(n:ℕ):= 8192*P n
-- a binary error envelope.
noncomputable def err (n:ℕ):ℝ:= 1/(2:ℝ)^(3000*P n)
abbrev Th := Nat
def H0:ℕ:=5000
def R(n:ℕ):=paramR (lanes n)
def L(n:ℕ):=paramL (lanes n)
def J(n:ℕ):=paramJ (lanes n)
def K(n:ℕ):=paramK (lanes n)
def D(n:ℕ) (i: Direction n):=paramD (lanes n) (moduli n i.val)
abbrev ell (n):=Param.span_ n
-- each row gain
def slope (n : ℕ) := 8*(ell n+R n+1)
noncomputable def weight (n:ℕ):ℝ := 2^slope n

/-- Structural assumptions throughout large case. Other eventual conditions may be adjoined.
Filter lift maps to obtain for variant indices. -/
structure Season (n:ℕ) : Prop where
  scatter : 64*(H0+20) ≤ lanes n
  budget_ i (v:i<lanes n): budget n ≤ moduli n i
  margin i (v:i<lanes n) : Margin (lanes n) (side n i) (moduli n i)
  odd i (v:i<lanes n) : Odd (moduli n i)
  volume : landscape n=load n
  enough : load n ≤ 2*modSize n
  wide : P n*load n≤32*n
  face : 1≤faces n
  batch : chunk n≤ span_ n ∧ batches n * chunk n + border n = span_ n
  safe : Phase.safe (scouts n) (chunk n) ∧ Phase.safe (scouts n) (border n) ∧
      Phase.safe (faces n) (chunk n)
  shortWidth : reach n+slack n=ell n
  warm : 1≤ reach n

theorem season : Large Season := by
  filter_upwards [dim_grows.eventually (eventually_ge_atTop (64*(H0+20))),axis_more,axis_margins,load_r,field_,full_volume,
    Param.faces_hold, Param.batch,Param.spar,cut_large] with n p q e f g w t y x s
  exact ⟨p,fun i t=> (q i t).1,fun i t=> (e i t).1,fun i t => (e i t).2,
    f,g,w,t.1,y,x,s.2, Nat.le_trans (Nat.pow_pos (lanes_pos n)) s.1⟩

namespace Season
variable {n:ℕ} (h:Season n)
include h
theorem dim : 3≤lanes n := by have t := h.scatter; unfold H0 at t; omega
theorem large : 1 ≤ n := by
  rcases n with _|n
  · have v := h.wide
    have p : 1≤load 0 := Nat.pow_pos (by decide)
    have x : 1≤P 0 := budget_p _
    nlinarith [Nat.mul_le_mul p x]
  · omega

omit h in
theorem posSide (i: Direction n) : 0<side n i.val := Nat.pos_of_ne_zero (NeZero.ne _)
theorem upper (i:Direction n):
    moduli n i.val ≤ side n i.val ∧ side n i.val ≤ 2^paramPrec (lanes n) :=
  ⟨((h.margin i i.isLt).strict (posSide i) (lanes_pos _)).le,
    (side_le n i).2.trans (upright _)⟩
theorem ratio (i:Direction n) :
    ((1:ℝ)+1/(8*lanes n))*(moduli n i.val:ℕ)≤(side n i.val:ℝ) :=
  (h.margin i i.isLt).ratio (lanes_pos _)
omit h in
theorem swath :
    K n * J n= lanes n^27 := by unfold K J paramK paramJ; ring
theorem grass (i:Direction n) :
    2*L n < moduli n i.val ∧ 2*(K n*J n) < moduli n i.val ∧
      J n ≤ 2*D n i ∧ moduli n i.val ≤ D n i :=
  param_geom (h.dim.trans' (by decide : 2≤3)) (h.budget_ i i.isLt)
theorem enoughBits :
    2*amount n ≤ modSize n := by
  have t := load_above n
  have p := h.enough
  omega
theorem mud i :
    ∀ j:Spot (moduli n (i:Direction n)),
    (Fourier.delta (moduli n i) (side n i) j).natAbs ≤ D n i := by
  intro j
  have e := delta_small _ (side n i) j
  have y := (h.grass i).2.2.2
  rw [← Int.natCast_natAbs] at e
  omega

-- error conversion
omit h in
private theorem tiny (x:ℕ) :
    Real.exp (-(x:ℝ)) ≤ 1/(2:ℝ)^x := by
  have t:2≤ Real.exp 1:=by linarith [Real.add_one_le_exp 1]
  rw [Real.exp_neg]
  have e := pow_le_pow_left₀ (by positivity) t x
  rw [← Real.exp_nat_mul,mul_one] at e
  rw [one_div]
  exact inv_anti₀ (by positivity) e

theorem error (i:Direction n)
    (d : moduli n i≤ side n i)
    {B:ℝ} {f : Arr (moduli n i) ℂ} (p:Bound f B) (e:0≤B) :
    Gap (restore d (D n i) (J n) (K n)
      (dft (side n i) (-(moduli n i:ℤ))
        (sample (moduli n i) (side n i) (D n i) (L n) f)))
      (dft (moduli n i) (side n i) f) (err n*B) := by
  have A:= Fourier.accuracy d (H:=(H0:ℕ)) (by positivity) (d:= lanes n) (by exact_mod_cast h.scatter)
    (h.budget_ i i.isLt) (h.upper i).2 (h.ratio i)
    p e
  apply A.mono
  gcongr
  have V : -(H0:ℝ)*(paramPrec (lanes n):ℝ)=-((H0*P n:ℕ):ℝ) := by unfold P budget paramPrec; push_cast; ring
  rw [V]
  refine (tiny (H0*P n)).trans ?_
  unfold err
  gcongr
  all_goals norm_num [H0]
end Season
end Scale

end IntegerMultiplication
end Computability
end OAI
