import OAI.Hierarchy.GridDyadicScale
import Mathlib.Tactic.Positivity

namespace OAI
/-! # Controller, advice, and strict lens margins on the chosen dyadic grid -/

namespace Hierarchy.GridScale
open Filter
noncomputable section

structure WidthBudget (k A w a q H : ℕ) : Prop where
  fits : (100*k+300)*a ≤ w
  growth : 3 ≤ a
  poly : H ≤ 2^a
  qPos : 0 < q
  qTop : q ≤ 2^a
  bankLo : 2^(w-a) ≤ pairs A w q
  bankHi : pairs A w q ≤ 2^(w+a)

theorem budgets {Q : ℕ → ℕ} {D : ℕ → ℝ} (e : Envelopes Q D) (k A C d : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w →
    WidthBudget k A w (overhead Q D w) q (C*(w+1)^d) := by
  filter_upwards [bounds e, sublinear e (100*k+300), (tendsto_atTop.mp (grows e)) 3,
    polynomial e C d, polynomial e 1 A, eventually_ge_atTop 1] with w bound fit large h den hw
  intro q hq top
  let a := overhead Q D w
  change (100*k+300)*a ≤ w at fit
  have ha : a ≤ w := (Nat.le_mul_of_pos_left a (by positivity : 0<100*k+300)).trans fit
  have dfit : w^A ≤ 2^a := (Nat.pow_le_pow_left (Nat.le_succ w) A).trans (by simpa using den)
  have bank := pairs_bounds A ha hw dfit hq (top.trans bound.1)
  exact ⟨fit,large,h,hq,top.trans bound.1,bank.1,bank.2⟩

namespace WidthBudget
variable {k A w a q H : ℕ}

theorem weaker (b : WidthBudget k A w a q H) {h : ℕ} (cap : h ≤ H) :
    WidthBudget k A w a q h := ⟨b.fits,b.growth,cap.trans b.poly,b.qPos,b.qTop,b.bankLo,b.bankHi⟩

private theorem fit (b : WidthBudget k A w a q H) :
    4*a ≤ w ∧ (10*k+24)*a ≤ w := by
  constructor <;> apply le_trans (Nat.mul_le_mul_right a (by omega)) b.fits

/-- Density on a tick, density on a line, selector overhead, and loss spent
turning pointwise pins into exposed ports. -/
theorem density (b : WidthBudget k A w a q H) :
    H*q*pins w a ≤ pairs A w q ∧ H*pairs A w q ≤ side a*pins w a ∧
    H*selector k w a ≤ pins w a ∧ H*q*pins w a ≤ 2^(w-a) := by
  obtain ⟨pinFit,chooseFit⟩ := b.fit
  have qpins : H*q*pins w a ≤ 2^(w-a) := by
    calc
      _ ≤ 2^a*2^a*2^(w-4*a) := Nat.mul_le_mul_right _ (Nat.mul_le_mul b.poly b.qTop)
      _ = 2^(a+a+(w-4*a)) := by rw [pow_add,pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨qpins.trans b.bankLo, ?_, ?_, qpins⟩
  · calc
      _ ≤ 2^a*2^(w+a) := Nat.mul_le_mul b.poly b.bankHi
      _ = 2^(a+(w+a)) := (pow_add ..).symm
      _ ≤ 2^(10*a+(w-4*a)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := pow_add ..
  · calc
      _ ≤ 2^a*2^(w-(10*k+24)*a) := Nat.mul_le_mul_right _ b.poly
      _ = 2^(a+(w-(10*k+24)*a)) := (pow_add ..).symm
      _ ≤ _ := by
        unfold pins
        apply Nat.pow_le_pow_right (by decide)
        nlinarith only [Nat.sub_add_cancel chooseFit, Nat.sub_add_cancel pinFit,
          Nat.zero_le (k*a), chooseFit]

/-- All three losses in the lens are negligible against the same gap lower
bound, with arbitrary fixed polynomial multipliers in `H`. -/
theorem lens (b : WidthBudget k A w a q H) (hk : 0<k) :
    8*side a ≤ radius k a ∧
    H*pairs A w q*(side a)^(k-1)*(side a)^2 ≤ 2^(w-a)*radius k a ∧
    H*radius k a*(side a)^k ≤ 2^(w-a) ∧ H*radius k a*selector k w a ≤ 2^(w-a) := by
  have small : a ≤ w := by have := b.fit.1; omega
  have subtract := Nat.sub_add_cancel small
  have selectFit := Nat.sub_add_cancel b.fit.2
  have fits := b.fits
  have margin := b.growth
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 2^3*2^(10*a) ≤ 2^((10*k+16)*a)
    rw [←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [margin, Nat.zero_le (k*a)]
  · calc
      _ ≤ (2^a*2^(w+a))*((2^(10*a))^(k-1))*((2^(10*a))^2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul b.poly b.bankHi))
      _ = 2^(a+(w+a)+(10*a)*(k-1)+(10*a)*2) := by simp only [pow_add,pow_mul]
      _ ≤ 2^((w-a)+(10*k+16)*a) := by
        apply Nat.pow_le_pow_right (by decide)
        have shift := congrArg (fun n : ℕ => (10*a)*n) (Nat.sub_add_cancel hk)
        nlinarith only [shift, subtract]
      _ = _ := pow_add ..
  · calc
      _ ≤ 2^a*2^((10*k+16)*a)*(2^(10*a))^k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ b.poly)
      _ = 2^(a+(10*k+16)*a+(10*a)*k) := by simp only [pow_add,pow_mul]
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith only [fits, subtract, Nat.zero_le (k*a)]
  · calc
      _ ≤ 2^a*2^((10*k+16)*a)*2^(w-(10*k+24)*a) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ b.poly)
      _ = 2^(a+(10*k+16)*a+(w-(10*k+24)*a)) := by simp only [pow_add]
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith only [selectFit, subtract]

/-- The descriptor and allocation computation of size `V^(4/5)` fits in
each of the two near-volume capacities with any fixed polynomial overhead. -/
theorem descriptor (b : WidthBudget k A w a q H) :
    (H:ℝ)*((2:ℝ)^w)^(4/5:ℝ) ≤ (pins w a:ℝ) ∧
    (H:ℝ)*((2:ℝ)^w)^(4/5:ℝ) ≤ (pairs A w q:ℝ) := by
  have total : 300*a ≤ w := (Nat.mul_le_mul_right a (by omega : 300≤100*k+300)).trans b.fits
  have realTotal : 300*(a:ℝ) ≤ w := by exact_mod_cast total
  have p := b.fit.1
  have Hcap : (H:ℝ) ≤ dyad a := by rw [←dyad_nat]; exact_mod_cast b.poly
  have identity : ((2:ℝ)^w)^(4/5:ℝ) = dyad ((w:ℝ)*(4/5)) := by
    rw [←Real.rpow_natCast (2:ℝ) w]
    exact dyad_rpow _ _
  have res : (H:ℝ)*((2:ℝ)^w)^(4/5:ℝ) ≤ (pins w a:ℝ) := by
    rw [identity]
    calc
      _ ≤ dyad a * dyad ((w:ℝ)*(4/5)) := mul_le_mul_of_nonneg_right Hcap (dyad_pos _).le
      _ = _ := dyad_add _ _
      _ ≤ dyad (w-4*a:ℕ) := by
        apply dyad_mono
        rw [Nat.cast_sub p,Nat.cast_mul,Nat.cast_ofNat]
        linarith only [realTotal, Nat.cast_nonneg (α:=ℝ) a]
      _ = _ := (dyad_nat _).symm
  have rel : pins w a ≤ pairs A w q :=
    (Nat.pow_le_pow_right (by decide) (show w-4*a≤w-a by omega)).trans b.bankLo
  exact ⟨res,res.trans (by exact_mod_cast rel)⟩

/-- The two distinct sums used in the controller's output time and the number
of advice bits assigned per tick. -/
theorem transmission (C : ℕ) (hk : 0<k)
    (b : WidthBudget k A w a q (3*C*(2*k+w^2+2))) :
    C*(ticks k a q*pins w a+external k a (pairs A w q)+pairs A w q) ≤ (side a)^k*pairs A w q ∧
    C*(external k a (pairs A w q)+pairs A w q*w^2) ≤ ticks k a q*pins w a := by
  let B := pairs A w q
  let g := side a
  let P := pins w a
  let Z := g^(k-1)
  have hz : 0<Z := Nat.pow_pos (Nat.two_pow_pos _)
  have group : Z*g = g^k := by
    dsimp [Z]
    rw [←pow_succ, Nat.sub_add_cancel hk]
  have gp : g ≤ g^k := group ▸ Nat.le_mul_of_pos_left g hz
  have qt : g^k ≤ ticks k a q := Nat.le_mul_of_pos_right _ b.qPos
  have simple := b.weaker (h := 3*C) (by nlinarith [Nat.zero_le (C*k),Nat.zero_le (C*w^2)])
  have scaled := b.weaker (h := 3*C*(2*k)) (by nlinarith [Nat.zero_le (C*w^2)])
  have advice := b.weaker (h := 3*C*w^2) (by nlinarith [Nat.zero_le (C*k)])
  have capg : 2^a ≤ g := Nat.pow_le_pow_right (by decide) (show a≤10*a by omega)
  have send1 : 3*C*(g^k*q*P) ≤ g^k*B := by
    have h := Nat.mul_le_mul_left (g^k) simple.density.1
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
  have send2 : 3*C*(k*(2*Z*B)) ≤ g^k*B := by
    rw [←group]
    have h := Nat.mul_le_mul_right (Z*B) (scaled.poly.trans capg)
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
  have send3 := Nat.mul_le_mul_right B ((simple.poly.trans capg).trans gp)
  have get1 : 3*C*(k*(2*Z*B)) ≤ ticks k a q*P := by
    have h := Nat.mul_le_mul_left Z scaled.density.2.1
    change Z*(3*C*(2*k)*B) ≤ Z*(g*P) at h
    have h' : 3*C*(k*(2*Z*B)) ≤ Z*g*P := by
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
    rw [group] at h'
    exact h'.trans (Nat.mul_le_mul_right P qt)
  have get2 : 3*C*(B*w^2) ≤ ticks k a q*P := by
    have h := advice.density.2.1
    exact (show 3*C*(B*w^2) ≤ g*P by
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h).trans
        (Nat.mul_le_mul_right P (gp.trans qt))
  constructor
  · change C*(g^k*q*P+k*(2*Z*B)+B) ≤ g^k*B
    nlinarith only [send1,send2,send3]
  · change C*(k*(2*Z*B)+B*w^2) ≤ ticks k a q*P
    nlinarith only [get1,get2]

end WidthBudget

/-- Uniform little-oh estimates for the actual controller's settings and
distributed evaluator advice. Any fixed constant and polynomial may multiply
the two charges while retaining the stated bounds. -/
theorem controller_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D)
    (k A C d : ℕ) (hk : 0<k) : ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w →
    let a := overhead Q D w
    let B := pairs A w q
    let f := C*(w+1)^d
    f*(ticks k a q*pins w a+external k a B+B) ≤ (side a)^k*B ∧
      f*(external k a B+B*w^2) ≤ ticks k a q*pins w a := by
  filter_upwards [budgets H k A (3*C*(2*k+3)) (d+2)] with w available
  intro q hq htop
  apply WidthBudget.transmission _ hk ((available q hq htop).weaker ?_)
  have n : 2*k+w^2+2 ≤ (2*k+3)*(w+1)^2 := by
    nlinarith [Nat.zero_le (k*w), Nat.zero_le (k*w^2)]
  calc
    _ ≤ 3*(C*(w+1)^d)*((2*k+3)*(w+1)^2) := Nat.mul_le_mul_left _ n
    _ = _ := by rw [pow_add]; ring

/-- The strict numerical margin for the complete diagonal lens with the
actual external pair count and the chosen selector length. -/
theorem diagonal_slack {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D)
    (k A : ℕ) (hk : 0<k) : ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w →
    let a := overhead Q D w
    let E := external k a (pairs A w q)
    let R := radius k a
    8*side a ≤ R ∧
      (18:ℝ)*(k-1:ℕ)*E*(side a:ℝ)^2/R +
        (2:ℝ)*k*R*((selector k w a:ℝ)+(side a:ℝ)^k) < D w/2 := by
  filter_upwards [budgets H k A (512*(k+1)^2) 0, bounds H] with w budget saved
  intro q hq top
  let a := overhead Q D w
  let B := pairs A w q
  let g := side a
  let R := radius k a
  let ell := selector k w a
  let E := external k a B
  have b := budget q hq top
  have ll := ((b.weaker (h:=8*18*(k-1)*k*2) (by
    simp only [pow_zero,mul_one]
    nlinarith [Nat.mul_le_mul_right k (Nat.sub_le k 1)])).lens hk)
  have rr := ((b.weaker (h:=16*k) (by
    simp only [pow_zero,mul_one]
    nlinarith)).lens hk)
  have geom : 8*(18*(k-1)*E*g^2) ≤ 2^(w-a)*R := by
    simpa only [E,external,g,R,B,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using ll.2.1
  have cc : 16*k*R*g^k ≤ 2^(w-a) := rr.2.2.1
  have ss : 16*k*R*ell ≤ 2^(w-a) := rr.2.2.2
  have gm : (8:ℝ)*((18:ℝ)*(k-1:ℕ)*E*(g:ℝ)^2) ≤ (2:ℝ)^(w-a)*R := by exact_mod_cast geom
  have cr : (16:ℝ)*k*R*(g:ℝ)^k ≤ (2:ℝ)^(w-a) := by exact_mod_cast cc
  have sr : (16:ℝ)*k*R*ell ≤ (2:ℝ)^(w-a) := by exact_mod_cast ss
  have rpos : (0:ℝ)<R := by exact_mod_cast (Nat.two_pow_pos ((10*k+16)*a))
  have slope : (18:ℝ)*(k-1:ℕ)*E*(g:ℝ)^2/R ≤ (2:ℝ)^(w-a)/8 := by
    apply (div_le_iff₀ rpos).mpr
    linarith only [gm]
  have positive : (0:ℝ)<(2:ℝ)^(w-a) := by positivity
  refine ⟨ll.1, ?_⟩
  change (18:ℝ)*(k-1:ℕ)*E*(g:ℝ)^2/R+(2:ℝ)*k*R*((ell:ℝ)+(g:ℝ)^k) < D w/2
  linarith only [slope, cr, sr, saved.2.1, positive]

/-- The pin field is chosen before the tick and the actual positive `q`.
It fits every fixed pin-limit exponent and exposing `qP` pins costs at
most half the original pointwise gap even at the uniform envelope `Q`. -/
theorem pin_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k C d : ℕ) :
    ∀ᶠ w : ℕ in atTop, let a := overhead Q D w
      C*(w+1)^d*pins w a ≤ 2^w ∧ (4:ℝ)*k*(Q w:ℝ)*(pins w a:ℝ) ≤ D w := by
  filter_upwards [polynomial H C d, polynomial H (4*k) 0, bounds H, sublinear H 4] with w poly kt saved mature
  let a := overhead Q D w
  have cfit : 4*k ≤ 2^a := by simpa [a] using kt
  have budget : 4*a ≤ w := mature
  have p : 2^a*pins w a ≤ 2^w := by
    rw [pins,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have e : 4*k*Q w*pins w a ≤ 2^(w-a) := by
    calc
      _ ≤ 2^a*2^a*2^(w-4*a) := Nat.mul_le_mul_right _ (Nat.mul_le_mul cfit saved.1)
      _ = 2^(a+a+(w-4*a)) := by rw [pow_add,pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨(Nat.mul_le_mul_right _ poly).trans p,
    (show (4:ℝ)*k*(Q w:ℝ)*(pins w a:ℝ) ≤ (2:ℝ)^(w-a) by exact_mod_cast e).trans saved.2.1⟩

/-- The actual public lengths and bounds used for the diagonal each fit in
`2*w+1` bits. Every member except a directionless external set is positive. -/
theorem header_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A : ℕ) (hk : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w →
    let a := overhead Q D w
    ∀ x ∈ [pins w a,side a,radius k a,selector k w a,pairs A w q,ticks k a q,
      external k a (pairs A w q)], 0<x ∧ x<2^(2*w+1) := by
  filter_upwards [budgets H k A (2*k) 0] with w budget
  intro q hq top
  let a := overhead Q D w
  let B := pairs A w q
  have b := budget q hq top
  have mature := b.fits
  change (100*k+300)*a ≤ w at mature
  have ar : a ≤ w := by nlinarith only [mature,Nat.zero_le (k*a)]
  have kk : 2*k ≤ 2^a := by simpa [a] using b.poly
  have weak : 2^w ≤ 2^(2*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have tight : 2^(2*w) < 2^(2*w+1) := by rw [pow_succ]; have := Nat.two_pow_pos (2*w); omega
  have positiveB : 0<B := (Nat.two_pow_pos _).trans_le b.bankLo
  have uB : B ≤ 2^(2*w) := b.bankHi.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ug : side a ≤ 2^w := Nat.pow_le_pow_right (by decide)
    (show 10*a≤w by nlinarith only [mature,Nat.zero_le (k*a)])
  have ur : radius k a ≤ 2^w := Nat.pow_le_pow_right (by decide)
    (show (10*k+16)*a≤w by nlinarith only [mature,Nat.zero_le (k*a)])
  have ut : ticks k a q ≤ 2^w := by
    calc
      _ ≤ (2^(10*a))^k*2^a := Nat.mul_le_mul_left _ b.qTop
      _ = 2^((10*a)*k+a) := by simp only [pow_add,pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [mature,Nat.zero_le (k*a)])
  have ue : external k a B ≤ 2^(2*w) := by
    calc
      _ = 2*k*((2^(10*a))^(k-1))*B := by dsimp [external,side]; ring
      _ ≤ 2^a*((2^(10*a))^(k-1))*2^(w+a) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ kk) b.bankHi
      _ = 2^(a+(10*a)*(k-1)+(w+a)) := by simp only [pow_add,pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        nlinarith only [mature, Nat.mul_le_mul_left (10*a) (Nat.sub_le k 1),Nat.zero_le (k*a)])
  change ∀ x ∈ [pins w a,side a,radius k a,selector k w a,B,ticks k a q,external k a B],
    0<x ∧ x<2^(2*w+1)
  intro x mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Nat.two_pow_pos _,(Nat.pow_le_pow_right (by decide) (Nat.sub_le w _)).trans_lt (weak.trans_lt tight)⟩
  · exact ⟨Nat.two_pow_pos _,ug.trans_lt (weak.trans_lt tight)⟩
  · exact ⟨Nat.two_pow_pos _,ur.trans_lt (weak.trans_lt tight)⟩
  · exact ⟨Nat.two_pow_pos _,(Nat.pow_le_pow_right (by decide) (Nat.sub_le w _)).trans_lt (weak.trans_lt tight)⟩
  · exact ⟨positiveB,uB.trans_lt tight⟩
  · exact ⟨Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _)) hq,ut.trans_lt (weak.trans_lt tight)⟩
  · exact ⟨Nat.mul_pos hk (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (Nat.two_pow_pos _))) positiveB),
       ue.trans_lt tight⟩



end
end Hierarchy.GridScale

end OAI
