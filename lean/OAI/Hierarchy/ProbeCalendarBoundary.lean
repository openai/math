import OAI.Hierarchy.ProbeCappedBalance
import OAI.Hierarchy.ProbeOuterLedger

namespace OAI
/-! # Signed boundary charges from one observed calendar transition -/

namespace Hierarchy.AdaptiveProbe

open scoped BigOperators
noncomputable section

theorem regularCharge_nonneg {m w j : ℕ} {s₀ r scale : ℝ} (hm : 0 < m) (hw : m ≤ w)
    (hs : 0 < s₀) (hs₁ : s₀ ≤ 1) (hr : 0 < r) (hscale : 0 ≤ scale) (hj : j < m+m) :
    0 ≤ regularCharge m w s₀ r scale j := by
  by_cases early : j < m
  · simpa [regularCharge, phaseCharge, early] using
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (payloadSlice_bounds hm hw j).1)
  · have st := hs.trans_le (clock_bounds hs hs₁ hm (j-m) (by omega)).1
    simp only [regularCharge, phaseCharge, early, ite_false]
    have rate := le_min (by positivity : 0 ≤ 1/clockTime s₀ m (j-m)) (by positivity : 0 ≤ 1/r)
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hs₁) (by positivity)) (by positivity)

theorem crudeCharge_nonneg {m w : ℕ} {s₀ C D : ℝ} (hm : 0 < m) (hw : m ≤ w)
    (hs₁ : s₀ ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (j : ℕ) :
    0 ≤ crudeCharge m w s₀ C D j := by
  by_cases early : j < m <;> simp only [crudeCharge, phaseCharge, early, ite_true, ite_false]
  · exact mul_nonneg (payloadSlice_bounds hm hw j).1 (by positivity)
  · exact mul_nonneg (div_nonneg (sub_nonneg.mpr hs₁) (by positivity)) (by positivity)

namespace OuterBank

variable {I X : Type*} [Fintype I]

/-- The retained bits and paid cash measured at a particular feed or cooling boundary. -/
structure BoundaryRead (B : OuterBank I X) (m w cap j : ℕ) (x out : X) : Prop where
  stored : ∀ i, B.stock out i = min (B.requests w m j x i) (cap*w)
  charged : B.cash out ≤ B.cash x + pairing (bitStock w (spillBits cap w (B.requests w m j x))) B.box

namespace BoundaryRead

variable {B : OuterBank I X} {n m w cap j : ℕ} {x out : X} {s₀ V G C D : ℝ}

/-- An individual capped transition satisfies the scaled potential inequality
at its actual initial inventory and its actual final cash balance. -/
theorem move_receipt (read : B.BoundaryRead m w cap j x out) {L : ℝ} (cool : ℕ → ℝ)
    (hn : 0<n) (hm : 0<m) (hw : m≤w) (hs : 0<s₀) (hs₁ : s₀≤1)
    (hV : 0≤V) (hG : 0≤G) (lv : V≤B.a*m) (lg : G≤s₀*B.a*m)
    (bound : OuterBounds B n w m cap s₀ V G C D) (hj : j<m+m)
    (inj : j<m → pairing (fun i=>(B.payload i:ℝ))
      (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤L*n)
    (dec : ∀ k, j=m+k → score B.a B.M B.coefficient
      (maximizer B.a B.M (clockTime s₀ m k) B.coefficient B.box (B.units w x))≤cool k*n) :
    B.normalized w n m s₀ (j+1) out ≤ B.normalized w n m s₀ j x+
      phaseCharge m (fun u=>payloadSlice m w u*(L+1/2))
        (fun u=>(1-s₀)/(m:ℝ)*(cool u+1/2)) j := by
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have wp := hm.trans_le hw
  have divide {u v c : ℝ} (le : u≤v+c*n) : u/n≤v/n+c := by
    rw [div_le_iff₀ np, add_mul, div_mul_cancel₀ _ np.ne']
    exact le
  have capped {s : ℝ} (pos : 0<s) (top : s≤1) :=
    B.capped_balance out (B.requests w m j x) (B.cash x) wp bound.aPos bound.bNonneg
      bound.MNonneg pos (bound.capBound s pos top) read.stored read.charged
  have nonneg (i : I) : 0 ≤ B.units w x i := by unfold units; positivity
  by_cases early : j<m
  · have next : j+1-m=0 := by omega
    have old : j-m=0 := by omega
    have clipped := capped (s:=1) zero_lt_one le_rfl
    have stockEq : bitStock w (B.requests w m j x) =
        (fun i=>B.units w x i+payloadSlice m w j*(B.payload i:ℝ)) :=
      funext (B.requests_inject early x)
    rw [stockEq] at clipped
    have estimate := inject_scaled hm hw j B.coefficient B.box (B.units w x) (fun i=>(B.payload i:ℝ))
      bound.aPos bound.bNonneg bound.MNonneg nonneg bound.boxNonneg (fun _=>by positivity)
      hV lv bound.payloadSize (inj early)
    have costs : B.balance w 1 out ≤ B.balance w 1 x+payloadSlice m w j*(L+1/2)*n := by
      unfold balance at clipped ⊢
      linarith only [clipped, estimate]
    simpa [normalized, phaseCharge, early, phaseTime, next, old, clockTime] using divide costs
  · let k := j-m
    have lt : k<m := by dsimp [k]; omega
    have eq : j=m+k := by dsimp [k]; omega
    have limits := clock_bounds hs hs₁ hm (k+1) (by omega)
    have clipped := capped (hs.trans_le limits.1) limits.2
    have stockEq : bitStock w (B.requests w m j x) = B.units w x :=
      funext (B.requests_cool (show m≤j by omega) x)
    rw [stockEq] at clipped
    have estimate := cool_scaled hm k lt B.coefficient B.box (B.units w x) bound.aPos
      bound.bNonneg bound.MNonneg nonneg bound.boxNonneg hs hs₁ hG lg
      (bound.gradientSize k lt x) (dec k eq)
    have costs : B.balance w (clockTime s₀ m (k+1)) out ≤
        B.balance w (clockTime s₀ m k) x+(1-s₀)/(m:ℝ)*(cool k+1/2)*n := by
      unfold balance at clipped ⊢
      linarith only [clipped, estimate]
    have after : j+1-m=k+1 := by omega
    simpa [normalized, phaseCharge, early, phaseTime, after, k] using divide costs

/-- Low measured injection and cooling prices yield the regular calendar allowance. -/
theorem regular (read : B.BoundaryRead m w cap j x out) {r scale : ℝ}
    (hn : 0<n) (hm : 0<m) (hw : m≤w) (hs : 0<s₀) (hs₁ : s₀≤1)
    (hV : 0≤V) (hG : 0≤G) (lv : V≤B.a*m) (lg : G≤s₀*B.a*m)
    (bound : OuterBounds B n w m cap s₀ V G C D) (hj : j<m+m)
    (inj : j<m → pairing (fun i=>(B.payload i:ℝ))
      (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤(3/2:ℝ)*n)
    (dec : ∀ k, j=m+k → score B.a B.M B.coefficient
      (maximizer B.a B.M (clockTime s₀ m k) B.coefficient B.box (B.units w x))≤
        (scale*min (1/clockTime s₀ m k) (1/r)+1/2)*n) :
    B.normalized w n m s₀ (j+1) out ≤ B.normalized w n m s₀ j x + regularCharge m w s₀ r scale j := by
  have step := read.move_receipt (L:=(3/2:ℝ)) (fun k=>scale*min (1/clockTime s₀ m k) (1/r)+1/2)
    hn hm hw hs hs₁ hV hG lv lg bound hj inj dec
  simpa only [regularCharge, phaseCharge, show (3/2+1/2:ℝ)=2 by norm_num, add_assoc,
    show (1/2+1/2:ℝ)=1 by norm_num, mul_comm (payloadSlice m w j) 2] using step

/-- The uniform box estimates give the coarse calendar allowance on this same transition. -/
theorem coarse (read : B.BoundaryRead m w cap j x out)
    (hn : 0<n) (hm : 0<m) (hw : m≤w) (hs : 0<s₀) (hs₁ : s₀≤1)
    (hV : 0≤V) (hG : 0≤G) (lv : V≤B.a*m) (lg : G≤s₀*B.a*m)
    (bound : OuterBounds B n w m cap s₀ V G C D) (hj : j<m+m) :
    B.normalized w n m s₀ (j+1) out ≤ B.normalized w n m s₀ j x + crudeCharge m w s₀ C D j :=
  read.move_receipt (L:=C) (fun _=>D) hn hm hw hs hs₁ hV hG lv lg bound hj
    (fun _=>bound.payloadCrude x) (fun k eq=>bound.coolingCrude k (by omega) x)


end BoundaryRead
end OuterBank
end
end Hierarchy.AdaptiveProbe

end OAI
