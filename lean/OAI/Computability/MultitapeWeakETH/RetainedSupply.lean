import OAI.Computability.MultitapeWeakETH.ShiftLaw
import OAI.Computability.MultitapeWeakETH.Balance

/-! # Averaging field-slice entropy over every folded shift -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open Finset
open scoped BigOperators Classical
noncomputable section

def gamma := 1-1/Real.sqrt 2
def rho : ℝ := 11/1000
def quadConstant (γ : ℝ) := 1+1/(2-(2:ℝ)^γ)
def retainedInfo (n B : ℕ) := (gamma-4*rho)*n-2*gamma*B-Real.logb 2 (quadConstant gamma)
def maskCost (n b : ℕ) := ((n ⌈/⌉ b : ℕ):ℝ)*(4*b:ℕ)*entropyBits (1/100)

theorem gamma_range : 0 < gamma ∧ gamma < 1 := by
  have h : 1 < Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
  constructor
  · exact sub_pos.mpr ((div_lt_one (by positivity)).mpr h)
  · unfold gamma
    linarith [show (0:ℝ) < 1/Real.sqrt 2 by positivity]

theorem quadConstant_pos : 0 < quadConstant gamma := by
  have lt : (2:ℝ)^gamma < 2 := by simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) gamma_range.2
  unfold quadConstant
  positivity

variable {n b N : ℕ} [NeZero N] [NeZero b] {K X : Type} [Field K] [PseudoMetricSpace X]
    (G : Network n b) (tables : Word n → (v : Fin G.vertices) → G.View v → K)

private theorem retained_shift (realizable : VPVNP.WireGeometry.RealizableConfigurations K X)
    (p : Site G N → X) (o : X) (a : ℝ) (ha : 0 ≤ a)
    (densityBound : (2:ℝ)^(-rho*n) ≤ density (G.FieldGood tables))
    (info : 0 < retainedInfo n (N*b)) (t : Fin N) :
    ∃ (Q s : ℕ) (logDensity : ℝ) (rate : Fin (Q*(N*b)) → ℝ) (h : Site G N → ℝ),
      0 < Q ∧ Q*(N*b) ≤ n ∧ (∀ j, 0 ≤ rate j ∧ rate j ≤ 1) ∧
      (∀ v, 0 ≤ h v ∧ h v ≤ 4*b) ∧ (Q*(N*b):ℕ)+logDensity ≤ ∑ j, rate j ∧
      retainedInfo n (N*b) ≤ gamma*(Q*(N*b):ℕ)+logDensity ∧
      (∑ v, h v) ≤ (Q*(N*b):ℕ)+maskCost n b ∧
      (∑ j, rate j*(a*dist (p (terminal G (foldedTerminal s j)))
        (p (terminal G (foldedTerminal s j+t))))) ≤
        supplyCost G p a + ∑ v, h v*(a*dist (p v) o) := by
  let u := t.val*b
  let B := N*b
  have hB : 0 < B := Nat.mul_pos (NeZero.pos _) (NeZero.pos _)
  have hu : u < B := Nat.mul_lt_mul_of_pos_right t.isLt (NeZero.pos _)
  obtain ⟨c,shift,quad⟩ := exists_field_columns G tables u gamma_range.2
  let s := trailing n (c 0-c 1).val
  let Q := (n-s-u)/B
  obtain ⟨hq,val⟩ := retained_payload hB hu gamma_range.1 quadConstant_pos densityBound quad
  change retainedInfo n B ≤ gamma*(B*Q:ℕ)+Real.logb 2 (rowMass G tables c) at val
  obtain ⟨len,fits,_⟩ := payload_fits (n:=n) (B:=B) (s:=s) (u:=u) hq (rowMass_le_one G tables c) (info.trans_le val)
  change 0 < B*Q at len
  change s+u+B*Q ≤ n at fits
  rw [Nat.mul_comm B Q] at val len fits
  obtain ⟨d,odd,factor⟩ := trailing_odd_factor (x:=(c 0-c 1).val) (n:=n) (by change s < n; omega)
  obtain ⟨rate,h,hr,hh,source,pins,demand⟩ := shift_law G tables realizable p o a ha s d t c
    factor odd shift fits hq
  exact ⟨Q,s,_,rate,h,Nat.pos_of_mul_pos_right len,by change Q*B ≤ n; omega,hr,hh,source,val,pins,demand⟩

/-- The root bound and the error-mask budget pay for all advice. The
independent terminal-pair deviation is charged only after averaging shifts. -/
theorem retained_supply (realizable : VPVNP.WireGeometry.RealizableConfigurations K X)
    (p : Site G N → X) (o : X) (a E : ℝ) (ha : 0 ≤ a)
    (densityBound : (2:ℝ)^(-rho*n) ≤ density (G.FieldGood tables))
    (info : 0 < retainedInfo n (N*b))
    (center : ∀ h : Site G N → ℝ, (∀ v, 0 ≤ h v ∧ h v ≤ 4*b) →
      (∑ v, h v*(a*dist (p v) o)) ≤ (∑ v, h v)/Real.sqrt 2 +
        Real.sqrt (4*b*∑ v, h v)*Real.sqrt E) :
    let d (i j : Fin N) := a*dist (p (terminal G i)) (p (terminal G j))
    retainedInfo n (N*b) - maskCost n b / Real.sqrt 2 -
      Real.sqrt (4*b*(n+maskCost n b))*Real.sqrt E -
      (n:ℝ)*(𝔼 i, 𝔼 j, |d i j-1|) ≤ supplyCost G p a := by
  intro d
  choose Q s logDensity rate h pos len range hbounds source valuation pins demand using
    retained_shift G tables realizable p o a ha densityBound info
  let cost (t : Fin N) := ∑ v, h t v*(a*dist (p v) o)
  apply supply_from_entropy Q s pos len d rate range logDensity cost _ _ source _ demand
  intro t
  have charged := center _ (hbounds t)
  have sumBound := pins t
  have lenBound : ((Q t*(N*b):ℕ):ℝ) ≤ n := by exact_mod_cast len t
  have maxSum := sumBound.trans (add_le_add lenBound (le_refl _))
  have errBound := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left maxSum (by positivity : (0:ℝ) ≤ 4*b))) (Real.sqrt_nonneg E)
  have linear := div_le_div_of_nonneg_right sumBound (Real.sqrt_nonneg 2)
  rw [add_div] at linear
  have val := valuation t
  simp only [gamma,sub_mul,one_mul,one_div,inv_mul_eq_div] at val
  dsimp only [cost]
  linarith only [charged,errBound,linear,val]

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
