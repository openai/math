import OAI.Hierarchy.ProbeOuterAccount
import OAI.Hierarchy.ProbeOuterSchedule
import OAI.Hierarchy.ProbeBudget

namespace OAI
/-! # Budget for every history of the finite outer probing procedure -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {I X : Type*} [Fintype I]

/-- Uniform score and incidence bounds of the layout. Each squared norm is an
unnormalized sum over the actual commodities; its bound grows linearly in n. -/
structure OuterBounds (B : OuterBank I X) (n w m cap : ℕ) (s₀ V G C D : ℝ) : Prop where
  aPos : 0<B.a
  bNonneg : ∀ i,0≤B.coefficient i
  MNonneg : 0≤B.M
  boxNonneg : ∀ i,0≤B.box i
  payloadSize : (∑ i,(B.payload i:ℝ)^2) ≤ V*n
  gradientSize : ∀ j<m, ∀ x, (∑ i,(rowSlope B.a (B.coefficient i) B.M
    (maximizer B.a B.M (clockTime s₀ m j) B.coefficient B.box (B.units w x) i))^2)≤G*n
  capBound : ∀ s:ℝ, 0<s → s≤1 → ∀ i,s*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap
  payloadCrude : ∀ x, pairing (fun i=>(B.payload i:ℝ))
    (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤C*n
  coolingCrude : ∀ j<m, ∀ x, score B.a B.M B.coefficient
    (maximizer B.a B.M (clockTime s₀ m j) B.coefficient B.box (B.units w x))≤D*n

namespace OuterBank
variable (B : OuterBank I X)

def normalized (w n m : ℕ) (s₀ : ℝ) (j : ℕ) (x : X) := B.balance w (phaseTime s₀ m j) x/n

theorem move_receipt {n m w cap : ℕ} {s₀ V G C D L : ℝ} (cool : ℕ→ℝ)
    (hn : 0<n) (hm : 0<m) (hw : m≤w) (hs : 0<s₀) (hs₁ : s₀≤1)
    (hV : 0≤V) (hG : 0≤G) (lv : V≤B.a*m) (lg : G≤s₀*B.a*m)
    (bound : OuterBounds B n w m cap s₀ V G C D) (move : ℕ→X→X) (events : B.Caps m w cap move)
    (j : ℕ) (hj : j<m+m) (x : X)
    (inj : j<m → pairing (fun i=>(B.payload i:ℝ))
      (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤L*n)
    (dec : ∀ k, j=m+k → score B.a B.M B.coefficient
      (maximizer B.a B.M (clockTime s₀ m k) B.coefficient B.box (B.units w x))≤cool k*n) :
    B.normalized w n m s₀ (j+1) (move j x) ≤ B.normalized w n m s₀ j x+
      phaseCharge m (fun u=>payloadSlice m w u*(L+1/2))
        (fun u=>(1-s₀)/(m:ℝ)*(cool u+1/2)) j := by
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have divide {u v c : ℝ} (le : u≤v+c*n) : u/n≤v/n+c := by
    rw [div_le_iff₀ np,add_mul,div_mul_cancel₀ _ np.ne']; exact le
  by_cases early : j<m
  · have next : j+1-m=0 := by omega
    have old : j-m=0 := by omega
    have costs := B.inject_move hm hw early move events x bound.aPos bound.bNonneg
      bound.MNonneg bound.boxNonneg (bound.capBound 1 zero_lt_one le_rfl) hV lv bound.payloadSize (inj early)
    simpa [normalized,phaseCharge,early,phaseTime,next,old,clockTime] using divide costs
  · let k := j-m
    have lt : k<m := by dsimp [k]; omega
    have eq : j=m+k := by dsimp [k]; omega
    have limits := clock_bounds hs hs₁ hm (k+1) (by omega)
    have costs := B.cool_move hm (hm.trans_le hw) lt move events x bound.aPos bound.bNonneg
      bound.MNonneg bound.boxNonneg hs hs₁ (bound.capBound _ (hs.trans_le limits.1) limits.2)
      hG lg (bound.gradientSize k lt x) (dec k eq)
    have after : j+1-m=k+1 := by omega
    simpa [normalized,phaseCharge,early,phaseTime,after,←eq,k] using divide costs

theorem initial_balance {w n : ℕ} (x : X) (empty : ∀ i,B.stock x i=0)
    (ha : 0≤B.a) (hb : ∀ i,0≤B.coefficient i) (fee : B.cash x≤n) : B.balance w 1 x≤n := by
  have stock : B.units w x=fun _=>0 := by funext i; simp [units,empty]
  let chosen := maximizer B.a B.M 1 B.coefficient B.box (fun _=>0)
  have scorePos : 0≤score B.a B.M B.coefficient chosen :=
    Finset.sum_nonneg (fun i _=>add_nonneg (mul_nonneg ha (sq_nonneg _))
      (mul_nonneg (hb i) (sq_nonneg _)))
  unfold balance
  rw [stock]
  change B.cash x + (pairing (fun _=>0) chosen - 1*score B.a B.M B.coefficient chosen) ≤ n
  simp only [pairing,zero_mul,Finset.sum_const_zero,one_mul,zero_sub]
  linarith

theorem uniform_outer_fuel {C D gain : ℝ} (gainPos : 0<gain) :
    ∃ fuel : ℕ, 5-(fuel:ℝ)*gain≤ -(C+D+1) := by
  obtain ⟨f,bound⟩ := exists_repair_fuel (upper:=5) (floor:= -(C+D+1)) gainPos
  exact ⟨f,bound 5 le_rfl⟩

/-- The public meshes and repair fuel are fixed uniformly. The only analytic
inputs particular to a repaired phase are the strict local saving and the
two defining low-excess tests. The conservative arm keeps paying every
physical payload increment and cooling down to the same final time. -/
theorem outer_budget {n m w cap : ℕ} {s₀ r scale V G C D gain : ℝ}
    (hn : 0<n) (hm : 0<m) (hw : m≤w) (hs : 0<s₀) (hs₁ : s₀≤1)
    (hr : 0<r) (hr₁ : r≤1) (sc : 0≤scale) (intg : scale*(1-Real.log r)≤1)
    (hV : 0≤V) (hG : 0≤G) (hC : 0≤C) (hD : 0≤D) (hg : 0<gain)
    (lv : V≤B.a*m) (lg : G≤s₀*B.a*m) (bound : OuterBounds B n w m cap s₀ V G C D)
    (move : ℕ→X→X) (events : B.Caps m w cap move) (start : X)
    (startPrice : B.balance w 1 start≤n)
    (endScore : s₀*score B.a B.M B.coefficient B.box≤n)
    (good : ℕ→X→Bool) (repairStep : ℕ→ℕ→X→X)
    (payloadLow : ∀ j<m, ∀ x, good j x=true → pairing (fun i=>(B.payload i:ℝ))
      (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤(3/2:ℝ)*n)
    (coolLow : ∀ j<m, ∀ x, good (m+j) x=true → score B.a B.M B.coefficient
      (maximizer B.a B.M (clockTime s₀ m j) B.coefficient B.box (B.units w x))≤
        (scale*min (1/clockTime s₀ m j) (1/r)+1/2)*n)
    (saves : ∀ j<m+m, ∀ h x, good j x=false → -(C+D+1)<B.normalized w n m s₀ j x →
      B.normalized w n m s₀ j (repairStep j h x)+gain≤B.normalized w n m s₀ j x) :
    ∀ fuel : ℕ, 5-(fuel:ℝ)*gain≤ -(C+D+1) →
      let final := (outerRun repairStep good (B.normalized w n m s₀) (-(C+D+1)) fuel move start (m+m)).1
      B.cash final + pairing (B.units w final) B.box ≤ 6*n := by
  intro fuel fuelBound
  let price := B.normalized w n m s₀
  let final := (outerRun repairStep good price (-(C+D+1)) fuel move start (m+m)).1
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have wp := hm.trans_le hw
  have ends := clock_endpoints (s₀:=s₀) hm
  have startTime : phaseTime s₀ m 0=1 := by simp [phaseTime,ends.1]
  have endTime : phaseTime s₀ m (m+m)=s₀ := by simp [phaseTime,ends.2]
  have startPaid : price 0 start≤1 := by
    change B.balance w (phaseTime s₀ m 0) start/n≤1
    rw [startTime,div_le_iff₀ np,one_mul]; exact startPrice
  have paid := outer_run_paid repairStep good price move start (m+m) fuel
    (regularCharge m w s₀ r scale) (crudeCharge m w s₀ C D)
    (upper:=(5:ℝ)) (fallback:= -(C+D+1)) (gain:=gain) hg
    (by
      intro j hj
      by_cases early : j<m
      · simpa [regularCharge,phaseCharge,early] using
          (mul_nonneg (by norm_num : (0:ℝ)≤2) (payloadSlice_bounds hm hw j).1)
      · have klt : j-m≤m := by omega
        have st := hs.trans_le (clock_bounds hs hs₁ hm _ klt).1
        simp only [regularCharge,phaseCharge,early,ite_false]
        exact mul_nonneg (div_nonneg (sub_nonneg.mpr hs₁) (by positivity))
          (by have := le_min (by positivity : 0≤1/clockTime s₀ m (j-m)) (by positivity : 0≤1/r); positivity))
    (by
      intro j _
      by_cases early : j<m <;> simp only [crudeCharge,phaseCharge,early,ite_true,ite_false]
      · exact mul_nonneg (payloadSlice_bounds hm hw j).1 (by positivity)
      · exact mul_nonneg (div_nonneg (sub_nonneg.mpr hs₁) (by positivity)) (by positivity))
    (regular_spend hm wp hs hs₁ hr hr₁ sc intg) (crude_spend hm wp hs hD)
    (by linarith) (by linarith) fuelBound (fun j hj h _ x=>saves j hj h x)
    (by
      intro j hj x ok
      have step := B.move_receipt (L:=(3/2:ℝ)) (fun k=>scale*min (1/clockTime s₀ m k) (1/r)+1/2)
        hn hm hw hs hs₁ hV hG lv lg bound move events j hj x (fun h=>payloadLow j h x ok)
        (fun k eq=>by subst j; exact coolLow k (by omega) x ok)
      simpa only [price,regularCharge, phaseCharge,show (3/2+1/2:ℝ)=2 by norm_num,
        add_assoc,show (1/2+1/2:ℝ)=1 by norm_num,mul_comm (payloadSlice m w j) 2] using step)
    (by
      intro j hj x
      exact B.move_receipt (L:=C) (fun _=>D) hn hm hw hs hs₁ hV hG lv lg bound move events j hj x
        (fun _=>bound.payloadCrude x) (fun k eq=>bound.coolingCrude k (by omega) x))
  change B.balance w (phaseTime s₀ m (m+m)) final/n≤5 at paid
  rw [endTime,div_le_iff₀ np] at paid
  have finish := finish_at_core B.coefficient B.box (B.units w final) bound.aPos bound.bNonneg
    bound.MNonneg hs (fun _=>by unfold units; positivity) bound.boxNonneg
  change B.cash final + pairing (B.units w final) B.box ≤ _
  unfold balance at paid
  linarith

end OuterBank

/-- Returning the unused bits from each reserved catalyst pair restores its
baseline charge. The paid physical link widths then satisfy the shorter-call
budget stated by the probing principle. -/
theorem outer_termBudget {E : Type*} [Fintype E] (p q Q Λ : ℝ) (n w M Nc used : ℕ)
    (t len y : E→ℝ) (charge : ℝ) (positive : 0<n) (width : 0<w) (inside : used≤Nc)
    (paid : charge-2*(M:ℝ)*used/w≤6*n)
    (returnBits : (∑ e,(len e*y e+Λ*capacity p q Q (t e) (len e)))≤
      charge+2*(M:ℝ)*(Nc-used:ℕ)/w) : TermBudget p q Q Λ n w M Nc t len y := by
  have hn : (0:ℝ)<n := by exact_mod_cast positive
  have hw : (0:ℝ)<w := by exact_mod_cast width
  have split : 2*(M:ℝ)*(Nc-used:ℕ)/w = 2*(M:ℝ)*Nc/w-2*(M:ℝ)*used/w := by
    rw [Nat.cast_sub inside]; ring
  apply termBudget_of_normalized _ _ _ _ _ _ _ _ _ _ _ positive width
  apply (div_le_iff₀ hn).mpr
  have simpCredit : (2*(M:ℝ)*Nc/((n:ℝ)*w))*n=2*(M:ℝ)*Nc/w := by field_simp
  rw [add_mul,simpCredit]
  linarith [returnBits,split]

end
end Hierarchy.AdaptiveProbe

end OAI
