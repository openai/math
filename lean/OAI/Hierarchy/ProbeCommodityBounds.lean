import OAI.Hierarchy.ProbeOuterLedger
import OAI.Hierarchy.ProbeExcess

namespace OAI
/-! # Outer estimates from the cardinality of the physical commodity bank -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {P X : Type*} [Fintype P] {N k : ℕ}

/-- The outer injection introduces one unit at each payload and none at the altimeters. -/
def payloadUnit : Commodity P N k → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- There is one payload and exactly two directed readings per tile and axis. -/
theorem commodity_count : Fintype.card (Commodity P N k) = Fintype.card P*(1+2*N*k) := by
  simp [Commodity,Fintype.card_sum,Fintype.card_prod]
  ring

/-- The score ceiling applies to the terminal point of the box as well as to
every offer computed during the mesh. -/
theorem commodity_score_bound (a M beta A : ℝ) (b x : Commodity P N k → ℝ)
    (ha : 0≤a) (hM : 0≤M) (hb : 0≤beta) (hA : 0≤A)
    (coeff : ∀ i,b i≤beta) (box : ∀ i,x i ∈ Set.Icc 0 A) :
    score a M b x ≤ (a+beta)*A^2*(1+2*N*k:ℕ)*Fintype.card P := by
  have row (i) : rowScore a (b i) M (x i)≤(a+beta)*A^2 := by
    have hi := box i
    have ri : rise M (x i)≤A := max_le (by linarith [hi.2]) hA
    have f := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi.1 hi.2 2) ha
    have g := mul_le_mul (coeff i) (pow_le_pow_left₀ (rise_nonneg _ _) ri 2) (sq_nonneg _) hb
    unfold rowScore
    linarith
  calc
    _ ≤ ∑ _i : Commodity P N k,(a+beta)*A^2 := Finset.sum_le_sum (fun i _=>row i)
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,commodity_count]; push_cast; ring

theorem commodity_terminal_score (a M beta A s₀ : ℝ) (b x : Commodity P N k → ℝ)
    (ha : 0≤a) (hM : 0≤M) (hb : 0≤beta) (hA : 0≤A) (hs : 0≤s₀)
    (coeff : ∀ i,b i≤beta) (box : ∀ i,x i ∈ Set.Icc 0 A)
    (chosen : s₀*((a+beta)*A^2*(1+2*N*k:ℕ))≤1) :
    s₀*score a M b x≤Fintype.card P := by
  calc
    _ ≤ s₀*((a+beta)*A^2*(1+2*N*k:ℕ)*Fintype.card P) :=
      mul_le_mul_of_nonneg_left (commodity_score_bound a M beta A b x ha hM hb hA coeff box) hs
    _ ≤ _ := by simpa [←mul_assoc] using
        mul_le_mul_of_nonneg_right chosen (Nat.cast_nonneg (α:=ℝ) (Fintype.card P))

/-- The constants for the entire outer schedule are independent of the bank size
and the word width. The one-unit injection only uses the payload coordinates. -/
theorem commodity_outer_bounds (bank : OuterBank (Commodity P N k) X)
    (w m : ℕ) (s₀ A beta : ℝ) (hm : 0<m) (hs : 0<s₀) (hs₁ : s₀≤1)
    (ha : 0<bank.a) (hM : 0≤bank.M) (positiveA : 0≤A) (posBeta : 0≤beta)
    (box : ∀ i,bank.box i ∈ Set.Icc 0 A)
    (coeff : bank.coefficient=bonus beta) (unit : bank.payload=payloadUnit) :
    let R : ℝ := (1+2*N*k : ℕ)
    let cap := ⌈2*(bank.a+beta)*A⌉₊
    OuterBounds bank (Fintype.card P) w m cap s₀ 1 ((cap:ℝ)^2*R) A
      ((bank.a+beta)*A^2*R) := by
  classical
  let cap := ⌈2*(bank.a+beta)*A⌉₊
  let R : ℝ := (1+2*N*k : ℕ)
  change OuterBounds bank _ _ _ cap _ _ ((cap:ℝ)^2*R) _ ((bank.a+beta)*A^2*R)
  have bNon : ∀ i,0≤bank.coefficient i := by
    intro i; rw [coeff]; cases i <;> simp [bonus,posBeta]
  have bMax : ∀ i,bank.coefficient i≤beta := by
    intro i; rw [coeff]; cases i <;> simp [bonus,posBeta]
  have ub {s : ℝ} (h : s≤1) (i) : s*rowSlope bank.a (bank.coefficient i) bank.M (bank.box i)≤cap :=
    outer_box_cap bank.coefficient bank.box ha.le bNon hM (fun j=>(box j).1)
      bMax (fun j=>(box j).2) h i
  have capAt (i) : rowSlope bank.a (bank.coefficient i) bank.M (bank.box i)≤cap := by
    simpa using ub (s:=1) le_rfl i
  have card : (Fintype.card (Commodity P N k):ℝ)=(Fintype.card P:ℝ)*R := by
    dsimp [R]
    exact_mod_cast (commodity_count (P:=P) (N:=N) (k:=k))
  have grad {s : ℝ} (positive : 0<s) (x : X) := outer_gradient_box bank.coefficient bank.box
    (bank.units w x) cap ha bNon hM positive (fun i=>by unfold OuterBank.units; positivity)
    (fun i=>(box i).1) capAt
  refine ⟨ha,bNon,hM,fun i=>(box i).1,?_,?_,fun _ _ h i=>ub h i,?_,?_⟩
  · simp [unit,Commodity,payloadUnit,Fintype.sum_sum_type]
  · intro j lt x
    have lower := (clock_bounds hs hs₁ hm j lt.le).1
    calc
      _ ≤ (cap:ℝ)^2*Fintype.card (Commodity P N k) := (grad (hs.trans_le lower) x).2.2
      _ = _ := by rw [card]; ring
  · intro x
    let price := maximizer bank.a bank.M 1 bank.coefficient bank.box (bank.units w x)
    change (∑ i, (bank.payload i:ℝ)*price i)≤_
    rw [unit,Fintype.sum_sum_type]
    simp only [payloadUnit,Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,Finset.sum_const_zero,add_zero]
    calc
      _ ≤ ∑ _i : P,A := Finset.sum_le_sum fun i _=>
        ((grad zero_lt_one x).1 (Sum.inl i)).2.trans (box _).2
      _ = _ := by simp [mul_comm]
  · intro j lt x
    let t := clockTime s₀ m j
    let price := maximizer bank.a bank.M t bank.coefficient bank.box (bank.units w x)
    have positive : 0<t := hs.trans_le (clock_bounds hs hs₁ hm j lt.le).1
    exact commodity_score_bound bank.a bank.M beta A bank.coefficient price ha.le hM
      posBeta positiveA bMax (fun i=>⟨((grad positive x).1 i).1,((grad positive x).1 i).2.trans (box i).2⟩)

end
end Hierarchy.AdaptiveProbe

end OAI
