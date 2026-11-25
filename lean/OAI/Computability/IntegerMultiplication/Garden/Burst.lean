import OAI.Computability.IntegerMultiplication.Garden.Furrow

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open Code Brief IntegerMultiplication.Star Carry Grid IntegerMultiplication.Fourier Staff Strip Dusk
open scoped BigOperators Real

variable {I:Type} {r:Regime I} {D s t l m F W:I→ℕ}
variable [∀ i,NeZero (s i)] [∀ i,NeZero (t i)]
variable (d:Realizes r D) (S:Realizes r s) (T:Realizes r t) (L:Realizes r l) (M:Realizes r m)
variable {i j:(x:I)→Spot (s x)}
variable (p:Figure r (fun x=>(i x).val)) (q:Figure r (fun x=>(j x).val))
variable (v:∀ i0:I,∀ i:Spot (s i0),(delta (s i0) (t i0) i).natAbs ≤ D i0)
variable (F_:Realizes r F) (W0:Realizes r W)
include d S T M L p q v
noncomputable abbrev tuned (i j:(x:I)→Spot (s x)) (x:I):ℝ :=
  mixTable (t x) (D x) (nhood (l x)) (m x) (i x) (j x)

theorem inked : Blot r (tuned (D:=D) (t:=t) (m:=m) (l:=l) i j) := by
  let x(x:I):ℤ:= baseline (t x) (D x) (s x)
  let a(i_:I):ℤ:= (canon (t i_) (D i_) (l i_) (m i_) (j i_)).1 (i i_)
  have P:=individual (r:=r) d S T L M p q
  have H:= (multiplier d S T).power (M.plus (.fix 1))
  have ht i:0<t i:=Nat.pos_of_ne_zero (NeZero.ne _)
  have hx i:0<x i:=baseline_p (t i) (D i) (v i) (ht i)
  have hv i:0<(x i)^(m i+1):= pow_pos (hx i) _
  have e (u:I): (0:ℝ)<((((x u)^(m u+1):ℤ)):ℝ) := by exact_mod_cast hv u
  have W := (Blot.integer P).ratio (Blot.integer H) e
  have g (u:I):
      tuned (D:=D) (t:=t) (m:=m) (l:=l) i j u=(a u:ℝ)/(((x u)^(m u+1):ℤ):ℝ) := by
    rw [eq_div_iff (e u).ne']
    have r := (canon_results (t u) (D u) (v u) (ht u) (l u) (m u) (j u)).2 (i u)
    push_cast; exact (mul_comm ..).trans r.symm
  have G : (tuned (D:=D) (t:=t) (m:=m) (l:=l) i j)=(fun u=>(a u:ℝ)/(((x u)^(m u+1):ℤ):ℝ)) := funext g
  rw [G]; exact W

noncomputable def climate (y:Bool) (x:ℝ) (s:ℕ):ℂ :=
  bif y then ((x/(s:ℝ):ℝ):ℂ) else (x:ℂ)
include F_ W0
theorem sheeting (u : Bool)
    (h:∀ x:I,(‖tuned (D:=D) (s:=s) (t:=t) (l:=l) (m:=m) i j x‖) *2^F x + 2 < 2^W x) :
    ∃ b : (x:I)→Grain (W x), Satisfactory W r b ∧ ∀ x,
      ‖meaning (F x) (W x) (b x) - climate u
        (mixTable (t x) (D x) (nhood (l x)) (m x) (i x) (j x)) (s x)‖ ≤
        2*Star.drop_ (F x) := by
  let f x:=tuned (D:=D) (s:=s) (t:=t) (l:=l) (m:=m) i j x
  let g x:=climate u (f x) (s x)
  have Q:Blot r f:= inked d S T L M p q v
  have t (i:I) : (0:ℝ)<s i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (s i))
  have G:Curve r g := by
    cases u with
    | false=> exact Curve.real Q
    | true=>exact Curve.real (Q.ratio (Blot.natural (Figure.of_spoken S)) t)
  apply Star.stroke g F W F_ W0 G
  intro x
  have Z: (1:ℝ) ≤ s x := by
    have p := t x
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (s x)))
  have V : ‖g x‖≤‖f x‖ := by
    cases u with
    | true=>
      change ‖(↑(f x/(s x:ℝ)):ℂ)‖≤_
      rw [Complex.norm_real,norm_div,Real.norm_of_nonneg (show 0≤(s x:ℝ) by positivity)]
      exact div_le_self (norm_nonneg _) Z
    | false=> exact Complex.norm_real _ |>.le
  apply lt_of_le_of_lt ?_ (h x); change _ ≤ ‖f x‖*2^F x+2; gcongr
end Garden

end IntegerMultiplication
end Computability
end OAI
