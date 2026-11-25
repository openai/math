import OAI.Computability.MultitapeWeakETH.SparseClock
import OAI.Computability.MultitapeWeakETH.SearchWidth
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-! # Charging the traversal and the sparse searches to the original variable count -/

namespace OAI.Computability.MultitapeWeakETH.VariableClock

open IntegerMultiplication Code
noncomputable section

def volume (cut K n s : ℕ) := cut+2*n+8*(n*(4*K^2*s^4))+1

def depth (d N : ℕ) := ⌊(N:ℝ)^(1-1/(d:ℝ))⌋₊

def exponent (cut K d q n : ℕ) :=
  let s := sparseBudget q n
  n/s+depth d (volume cut K n s)

/-- One uniform exponent bound includes the finite small-volume padding. -/
theorem exponent_bound (cut K d : ℕ) (hd : 1<d) :
    ∃ q : ℕ, 1<q ∧ ∃ A C : ℕ, ∀ n : ℕ,
      (exponent cut K d q n:ℝ) ≤ A+C*(n:ℝ)^(1-(q:ℝ)⁻¹) := by
  have h : (1:ℝ)<d := by exact_mod_cast hd
  let δ := 1/(d:ℝ)
  have pos : 0<δ := by dsimp [δ]; positivity
  have small : δ<1 := (div_lt_one (by linarith)).mpr h
  obtain ⟨q,hq,clock⟩ := sparse_clock pos small
  let k := cut+32*K^2+3
  obtain ⟨C,hC⟩ := exists_nat_ge (2+(k:ℝ)^(1-δ))
  refine ⟨q,hq,exponent cut K d q 0,C,?_⟩
  intro n
  by_cases hn : n=0
  · subst n; exact le_add_of_nonneg_right (by positivity)
  let s := sparseBudget q n
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (by dsimp [s,sparseBudget]; positivity)
  have h1 : 1 ≤ n*s^4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : n ≤ n*s^4 := Nat.le_mul_of_pos_right n (by positivity)
  have v : volume cut K n s ≤ k*n*s^4 := by
    have a := Nat.mul_le_mul_left cut h1
    dsimp [volume,k]
    nlinarith only [a,h1,h2]
  have vr : (volume cut K n s : ℝ) ≤ (k:ℝ)*n*(s:ℝ)^4 := by exact_mod_cast v
  have dlim : (depth d (volume cut K n s):ℝ) ≤ ((k:ℝ)*n*(s:ℝ)^4)^(1-δ) :=
    (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow (by positivity) vr (by linarith))
  have nlim : ((n/s:ℕ):ℝ) ≤ (n:ℝ)/s := by
    apply (le_div_iff₀ (by exact_mod_cast hs : (0:ℝ)<s)).mpr
    exact_mod_cast Nat.div_mul_le_self n s
  change ((n/s+depth d (volume cut K n s):ℕ):ℝ) ≤ _
  rw [Nat.cast_add]
  apply (add_le_add nlim dlim).trans
  apply (clock k (by positivity) n (by omega)).trans
  exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans (le_add_of_nonneg_left (by positivity))

/-- A polynomial in the charged integer scale gives exactly the multiplicative
input-length factor and variable-count running time in deterministic Weak ETH. -/
theorem charge {I : Type} {n base exp time : I → ℕ} (eta : ℝ) (A C : ℕ)
    (baseTwo : ∀ i, 2 ≤ base i)
    (cost : Dom (fun i => base i+2^(exp i)) time)
    (saving : ∀ i, (exp i:ℝ) ≤ A+C*(n i:ℝ)^(1-eta)) :
    ∃ c d : ℕ, ∀ i, (time i:ℝ) ≤ (2:ℝ)^(c*(n i:ℝ)^(1-eta)) * (base i:ℝ)^d := by
  obtain ⟨D,U,lim⟩ := cost
  let P := U*3^D*2^(D*A)
  refine ⟨D*C,P+D,?_⟩
  intro i
  let b := base i
  let e := exp i
  have hb : 2≤b := baseTwo i
  have power : 1≤2^e := Nat.one_le_two_pow
  have cap : b+2^e+1 ≤ 3*b*2^e := by nlinarith [Nat.mul_le_mul_left b power,Nat.mul_le_mul_right (2^e) hb]
  have t := (lim i).trans (Nat.mul_le_mul_left U (Nat.pow_le_pow_left cap D))
  have u : time i ≤ U*3^D*b^D*2^(D*e) := by
    simpa only [mul_pow,← pow_mul,Nat.mul_comm e D,mul_assoc] using t
  let v := (n i:ℝ)^(1-eta)
  have h := mul_le_mul_of_nonneg_left (saving i) (Nat.cast_nonneg D)
  have expBound : (2:ℝ)^(D*e) ≤ (2:ℝ)^(D*A)*(2:ℝ)^(((D*C:ℕ):ℝ)*v) := by
    rw [← Real.rpow_natCast (2:ℝ) (D*e),← Real.rpow_natCast (2:ℝ) (D*A),← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    dsimp [e,v]
    linarith only [h]
  have absorb : P ≤ b^P :=
    (Nat.lt_two_pow_self (n:=P)).le.trans (Nat.pow_le_pow_left hb P)
  calc
    (time i:ℝ) ≤ (U:ℝ)*3^D*(b:ℝ)^D*(2:ℝ)^(D*e) := by exact_mod_cast u
    _ ≤ (U:ℝ)*3^D*(b:ℝ)^D*((2:ℝ)^(D*A)*(2:ℝ)^(((D*C:ℕ):ℝ)*v)) := by gcongr
    _ = (2:ℝ)^(((D*C:ℕ):ℝ)*v)*(P:ℝ)*(b:ℝ)^D := by dsimp [P]; push_cast; ring
    _ ≤ (2:ℝ)^(((D*C:ℕ):ℝ)*v)*(b:ℝ)^P*(b:ℝ)^D := by gcongr; exact_mod_cast absorb
    _ = _ := by rw [pow_add]; ring

end
end OAI.Computability.MultitapeWeakETH.VariableClock
