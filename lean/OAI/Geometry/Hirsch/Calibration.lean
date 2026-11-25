import OAI.Geometry.Hirsch.Growth

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer.Growth

def exponent (K : ℕ) := 100*K*3^K+2

structure Plan where
  K : ℕ
  h : ℕ
  enough : 2 ≤ K

namespace Plan

variable (p : Plan)

def T := exponent p.K
def N := 16*(p.h+1)*p.K
def rounds := p.N*(p.T+1)

theorem two : (2 : ℝ) ≤ p.K := Nat.cast_le.mpr p.enough

theorem large : 100*(p.K : ℝ) ≤ p.T := by
  have h := Nat.le_mul_of_pos_right (100*p.K) (by positivity : 0 < 3^p.K)
  exact_mod_cast (show 100*p.K ≤ p.T by unfold T exponent; omega)

theorem npos : 0 < p.N := by have := p.enough; unfold N; positivity

def dial (r : ℕ) : Dials where
  K := p.K
  a := 2^r
  h := p.h
  J := 4*r+2
  cycles := p.rounds
  run := Nat.mul_pos p.npos (by omega)
  tests := thresholds p.K r (100*p.K) (by positivity)
  p := E r (-2*p.T)
  z := E r (-4/p.K)
  t := E r (-p.T)
  L := r*Real.log 2/p.N
  M := E r (3-p.T)
  A := E r (-32*p.K)
  theta := E r (-(p.T : ℝ)-4*p.K)
  gamma := E r (-1)

theorem aval (r : ℕ) : ((p.dial r).a : ℝ) = E r 1 := by simp [dial,one]
theorem umax (r : ℕ) : (p.dial r).U = E r (1-p.T) := by
  rw [Dials.U,p.aval]; exact mul ..
theorem end_test (r : ℕ) : (p.dial r).tests.value (p.dial r).K = E r (-100*p.K) := by
  simp [dial,thresholds]
theorem lambda (r : ℕ) (x : ℝ) : Real.exp (x*(p.dial r).L) = E r (x/p.N) := by
  unfold dial E; congr 1; ring
theorem neg_lambda (r : ℕ) : Real.exp (-(p.dial r).L) = E r (-1/p.N) := by
  simpa using p.lambda r (-1)

theorem start (r : ℕ) : (p.dial r).U ≤ (p.dial r).tests.value 0 := by
  rw [p.umax]
  apply mono
  simp only [T,exponent,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.sub_zero]
  linarith

theorem order_loss : Order (fun r => (p.dial r).loss) (-(p.T : ℝ)-20*p.K) := by
  exact (((Order.base (-32*p.K)).scale (p.K+1)).prod (Order.base (3-p.T))).up (by linarith [p.two])

theorem order_key : Order (fun r => (p.dial r).key) (-(p.T : ℝ)-20*p.K) := by
  have h := (Order.const 1).add ((Order.base (-32*p.K)).up (by linarith [p.two]))
  exact (h.prod (Order.base (-2*p.T))).up (by linarith [p.large,p.two])

theorem order_beta : Order (fun r => (p.dial r).beta) (-2*p.T-10*p.K) :=
  (((Order.base (3-p.T)).scale 2).prod ((p.order_key.add p.order_loss).scale p.K)).up (by linarith [p.two])

theorem order_err : Order (fun r => (p.dial r).err) (-(p.T : ℝ)-2*p.K) := by
  have hf : Order (fun r => Board.Ledger.factor (p.dial r).a p.h) 2 := by
    have h := (Order.base 1).scale 4
    have hh := (((h.prod h).scale p.h).scale 9).up (by norm_num : (1 : ℝ)+1 ≤ 2)
    have hsum := ((Order.const 1).up (by norm_num : (0 : ℝ) ≤ 2)).add hh
    simpa only [Board.Ledger.factor,Board.Ledger.Box,Fintype.card_prod,Fintype.card_fin,
      Nat.cast_mul,Nat.cast_ofNat,aval] using hsum
  exact ((hf.power p.K).prod (Order.base (-(p.T : ℝ)-4*p.K))).up (by linarith)

theorem order_error (k : ℕ) : Order (fun r => (p.dial r).error k) (-(p.T : ℝ)-1) := by
  have hK : (p.K : ℝ) ≠ 0 := by linarith [p.two]
  have h : Order (fun r => (p.dial r).U) (1-p.T) := by simp only [umax]; exact Order.base _
  have hh := (h.scale ((p.dial 0).capacity k)).prod ((Order.base (-4/p.K)).power p.K)
  exact (hh.up (by rw [div_mul_cancel₀ _ hK]; linarith)).add
    ((p.order_loss.scale (p.K+1)).up (by linarith [p.two]))

theorem small (k : ℕ) : ∀ᶠ r : ℕ in atTop,
    let u := p.dial r
    2*u.p + u.error k + u.err + u.K*u.p*u.M ≤ u.t/4 := by
  have h := Order.base (-2*(p.T : ℝ))
  have h' : -2*(p.T : ℝ) ≤ -(p.T : ℝ)-1 := by linarith [p.large,p.two]
  have lhs := (((h.up h').scale 2).add (p.order_error k)).add (p.order_err.up (by linarith [p.two]))
  have rhs := (h.scale p.K).prod (Order.base (3-p.T))
  have sum := (lhs.add (rhs.up (by linarith [p.large,p.two]))).scale 4
  filter_upwards [sum.lt (show -(p.T : ℝ)-1 < -(p.T : ℝ) by linarith)] with r hr
  change 4*(2*(p.dial r).p + (p.dial r).error k + (p.dial r).err + (p.dial r).K*(p.dial r).p*(p.dial r).M) < (p.dial r).t at hr
  dsimp only; linarith

theorem comparisons : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    3*u.beta < u.theta^2 ∧ u.key+u.loss ≤ u.theta ∧ u.err ≤ u.t/32 := by
  have hb := (p.order_beta.scale 3).lt (y := (-(p.T : ℝ)-4*p.K)*2) (by linarith [p.two])
  have hl := (p.order_key.add p.order_loss).lt (y := -(p.T : ℝ)-4*p.K) (by linarith [p.two])
  have he := (p.order_err.scale 32).lt (y := -(p.T : ℝ)) (by linarith [p.two])
  filter_upwards [hb,hl,he] with r hb hl he
  refine ⟨?_,hl.le,?_⟩
  · change _ < E r _ ^ 2
    rw [pow,Nat.cast_ofNat]; exact hb
  · change 32*(p.dial r).err < (p.dial r).t at he
    linarith

end Plan
end OAI.Geometry.Hirsch.Layer.Growth
