import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

/-! The coordinatewise conditional-gradient search from Section 2. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The lower corner of the test box for coordinate `i`. -/
def fwLower (i j : Fin n) : K := if j = i then 1 / 4 else 0

def InLabelBox (i : Fin n) (x : Fin n → K) : Prop :=
  ∀ j, fwLower i j ≤ x j ∧ x j ≤ 1

private theorem fwLower_bounds (i j : Fin n) :
    0 ≤ fwLower (K := K) i j ∧ fwLower (K := K) i j ≤ 1 := by
  unfold fwLower
  split <;> constructor <;> norm_num

/-- A deterministic corner minimizing the linear function with coefficients `g`. -/
def fwCorner (i : Fin n) (g : Fin n → K) (j : Fin n) : K :=
  if 0 ≤ g j then fwLower i j else 1

theorem fwCorner_mem (i : Fin n) (g : Fin n → K) : InLabelBox i (fwCorner i g) := by
  intro j
  unfold fwCorner
  split <;> simpa using (fwLower_bounds (K := K) i j).2

theorem fwCorner_min (i : Fin n) (g w : Fin n → K) (hw : InLabelBox i w) :
    g ⬝ᵥ fwCorner i g ≤ g ⬝ᵥ w := by
  apply Finset.sum_le_sum
  intro j _
  unfold fwCorner
  split
  · exact mul_le_mul_of_nonneg_left (hw j).1 ‹0 ≤ g j›
  · exact mul_le_mul_of_nonpos_left (hw j).2 (le_of_not_ge ‹¬ 0 ≤ g j›)

def fwEnergy (Q : Matrix (Fin n) (Fin n) K) (z : Fin n → K) : K :=
  (Q *ᵥ z) ⬝ᵥ (Q *ᵥ z)

/-- One step of size `a` towards the minimizing corner, with residual matrix `Q = I-P`. -/
def fwStep (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (z : Fin n → K) (a : K) : Fin n → K :=
  z + a • (fwCorner i ((Q *ᵥ z) ᵥ* Q) - z)

/-- The successive test points, starting at the lower corner of the box. -/
def fwIterate (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) : ℕ → (Fin n → K)
  | 0 => fwLower i
  | p + 1 => fwStep Q i (fwIterate Q i p) (2 / (p + 2 : K))

private theorem fwMix_mem (i : Fin n) (z c : Fin n → K) (hz : InLabelBox i z)
    (hc : InLabelBox i c) (a : K) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    InLabelBox i (z + a • (c - z)) := by
  intro j
  change fwLower i j ≤ z j + a * (c j - z j) ∧ z j + a * (c j - z j) ≤ 1
  rcases hz j with ⟨hz₀, hz₁⟩
  rcases hc j with ⟨hc₀, hc₁⟩
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha₁) (sub_nonneg.mpr hz₀),
                mul_nonneg ha₀ (sub_nonneg.mpr hc₀)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha₁) (sub_nonneg.mpr hz₁),
                mul_nonneg ha₀ (sub_nonneg.mpr hc₁)]

theorem fwIterate_mem (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (p : ℕ) :
    InLabelBox i (fwIterate Q i p) := by
  induction p with
  | zero => exact fun j => ⟨le_rfl, (fwLower_bounds i j).2⟩
  | succ p ih =>
    apply fwMix_mem i _ _ ih (fwCorner_mem i _) _ (by positivity)
    exact (div_le_one (by positivity)).mpr (by have : (0:K) ≤ p := Nat.cast_nonneg _; linarith)

private theorem fwDot_nonneg (u : Fin n → K) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun j _ => mul_self_nonneg (u j)

/-- An orthogonal projection is nonexpansive for the squared Euclidean norm. -/
theorem fwEnergy_le_norm_sq (Q : Matrix (Fin n) (Fin n) K) (hs : Qᵀ = Q) (he : Q * Q = Q)
    (u : Fin n → K) : fwEnergy Q u ≤ u ⬝ᵥ u := by
  have h := fwDot_nonneg (u - Q *ᵥ u)
  have hdot : (Q *ᵥ u) ⬝ᵥ (Q *ᵥ u) = u ⬝ᵥ (Q *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, mulVec_mulVec, he, dotProduct_comm]
  simp only [sub_dotProduct, dotProduct_sub, hdot, dotProduct_comm (Q *ᵥ u) u] at h
  unfold fwEnergy
  linarith

private theorem fwDiameter (i : Fin n) (z c : Fin n → K) (hz : InLabelBox i z)
    (hc : InLabelBox i c) : (c - z) ⬝ᵥ (c - z) ≤ (n : K) := by
  calc
    (c-z) ⬝ᵥ (c-z) ≤ ∑ _j : Fin n, (1:K) := by
      apply Finset.sum_le_sum
      intro j _
      change (c j - z j) * (c j - z j) ≤ 1
      have hz₀ := le_trans (fwLower_bounds i j).1 (hz j).1
      have hc₀ := le_trans (fwLower_bounds i j).1 (hc j).1
      have h₁ : 0 ≤ 1 + (c j - z j) := by linarith [(hz j).2]
      have h₂ : 0 ≤ 1 - (c j - z j) := by linarith [(hc j).2]
      nlinarith [mul_nonneg h₁ h₂]
    _ = n := by simp

private theorem fwEnergy_initial (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ = Q) (he : Q * Q = Q) : fwEnergy Q (fwLower i) ≤ n := by
  apply (fwEnergy_le_norm_sq Q hs he _).trans
  calc
    _ ≤ ∑ _j : Fin n, (1:K) := by
      apply Finset.sum_le_sum
      intro j _
      rcases fwLower_bounds (K := K) i j with ⟨h₀,h₁⟩
      exact (mul_le_mul h₁ h₁ h₀ zero_le_one).trans_eq (one_mul _)
    _ = n := by simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem fwExpand (Q : Matrix (Fin n) (Fin n) K) (z d : Fin n → K) (a : K) :
    fwEnergy Q (z + a • d) = fwEnergy Q z + 2*a*((Q *ᵥ z) ᵥ* Q ⬝ᵥ d) + a^2 * fwEnergy Q d := by
  unfold fwEnergy
  rw [mulVec_add, mulVec_smul, ← dotProduct_mulVec]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
             dotProduct_comm (Q *ᵥ d) (Q *ᵥ z)]
  ring

/-- A one-step comparison against every point of the box. -/
theorem fwStep_gap (Q : Matrix (Fin n) (Fin n) K) (hs : Qᵀ = Q) (he : Q * Q = Q)
    (i : Fin n) (z w : Fin n → K) (hz : InLabelBox i z) (hw : InLabelBox i w)
    (a : K) (ha : 0 ≤ a) :
    fwEnergy Q (fwStep Q i z a) - fwEnergy Q w ≤
      (1-a) * (fwEnergy Q z - fwEnergy Q w) + n*a^2 := by
  let g := (Q *ᵥ z) ᵥ* Q
  let c := fwCorner i g
  have hc := fwCorner_min i g w hw
  have hd := (fwEnergy_le_norm_sq Q hs he (c-z)).trans (fwDiameter i z c hz (fwCorner_mem i _))
  have hlin : 2*(g ⬝ᵥ (w-z)) ≤ fwEnergy Q w - fwEnergy Q z := by
    have h := fwExpand Q z (w-z) 1
    rw [one_smul, add_sub_cancel] at h
    have hnn := fwDot_nonneg (Q *ᵥ (w-z))
    change 0 ≤ fwEnergy Q (w-z) at hnn
    dsimp only [g]
    linarith
  have h₁ : 2*(g ⬝ᵥ (c-z)) ≤ fwEnergy Q w - fwEnergy Q z := by
    rw [dotProduct_sub] at hlin ⊢
    change g ⬝ᵥ c ≤ g ⬝ᵥ w at hc
    linarith
  change fwEnergy Q (z + a • (c-z)) - _ ≤ _
  rw [fwExpand]
  change fwEnergy Q z + 2*a*(g ⬝ᵥ (c-z)) + a^2*fwEnergy Q (c-z) - _ ≤ _
  linarith only [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left hd (sq_nonneg a)]

/-- Uniform convergence to the minimum, stated without choosing a minimizer. -/
theorem fwIterate_gap (Q : Matrix (Fin n) (Fin n) K) (hs : Qᵀ = Q) (he : Q * Q = Q)
    (i : Fin n) (w : Fin n → K) (hw : InLabelBox i w) (p : ℕ) :
    fwEnergy Q (fwIterate Q i p) - fwEnergy Q w ≤ 4*n/(p+2 : K) := by
  induction p with
  | zero =>
    have h := fwEnergy_initial i Q hs he
    have hw₀ := fwDot_nonneg (Q *ᵥ w)
    change 0 ≤ fwEnergy Q w at hw₀
    change fwEnergy Q (fwLower i) - fwEnergy Q w ≤ _
    norm_num
    linarith [Nat.cast_nonneg (α := K) n]
  | succ p ih =>
    let a : K := 2/(p+2 : K)
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have ha₁ : a ≤ 1 := (div_le_one (by positivity)).mpr (by have : (0:K) ≤ p := Nat.cast_nonneg _; linarith)
    have h := fwStep_gap Q hs he i (fwIterate Q i p) w (fwIterate_mem Q i p) hw a ha
    have hi := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ha₁)
    change fwEnergy Q (fwStep Q i (fwIterate Q i p) a) - fwEnergy Q w ≤ _
    refine h.trans ((add_le_add hi le_rfl).trans ?_)
    dsimp [a]
    push_cast
    have hp : (0:K) ≤ p := Nat.cast_nonneg _
    field_simp
    nlinarith [Nat.cast_nonneg (α := K) n]

/-- At least `8 n / τ²` iterations ensure acceptance of a strict feasible witness. -/
theorem fwIterate_accept (Q : Matrix (Fin n) (Fin n) K) (hs : Qᵀ = Q)
    (he : Q * Q = Q) (i : Fin n) (w : Fin n → K) (hw : InLabelBox i w) (τ : K)
    (hwτ : fwEnergy Q w ≤ τ^2/4) (p : ℕ) (hp : 8*n ≤ p*τ^2) :
    fwEnergy Q (fwIterate Q i p) ≤ τ^2 := by
  have h := fwIterate_gap Q hs he i w hw p
  have he' : 4*(n : K)/((p:K)+2) ≤ τ^2/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg τ]
  linarith [sq_nonneg τ]

/-- The chosen corner in round `p`. -/
def fwChosen (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (p : ℕ) : Fin n → K :=
  fwCorner i ((Q *ᵥ fwIterate Q i p) ᵥ* Q)

/-- Clearing the common denominator gives the explicit weighted-corner formula. -/
theorem fwIterate_weighted (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (p : ℕ) (j : Fin n) :
    (p : K) * (p+1) * fwIterate Q i p j =
      2 * ∑ k ∈ Finset.range p, (k+1 : K) * fwChosen Q i k j := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, mul_add (2 : K) _ _, ← ih]
    push_cast
    change ((p:K)+1) * ((p+1)+1) *
      (fwIterate Q i p j + (2/(p+2:K)) * (fwChosen Q i p j - fwIterate Q i p j)) = _
    field_simp
    ring

/-- Materialize each new point before evaluating the matrix on the next round. -/
def fwArray (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) : ℕ → Vector K n
  | 0 => Vector.ofFn (fwLower i)
  | p+1 =>
    let z := fwArray Q i p
    let u := Vector.ofFn (Q *ᵥ z.get)
    let g := Vector.ofFn (u.get ᵥ* Q)
    let a : K := 2 / (p+2 : K)
    Vector.ofFn (fun j => z.get j + a * (fwCorner i g.get j - z.get j))

private theorem fwGet_ofFn {α : Type*} (f : Fin n → α) : (Vector.ofFn f).get = f := by
  funext j
  change (Vector.ofFn f)[j.val] = f j
  exact Vector.getElem_ofFn j.isLt

omit [IsStrictOrderedRing K] in
theorem fwArray_correct (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (p : ℕ) :
    (fwArray Q i p).get = fwIterate Q i p := by
  induction p with
  | zero => exact fwGet_ofFn _
  | succ p ih =>
    simp only [fwArray, fwGet_ofFn, ih, fwIterate, fwStep]
    rfl

private theorem fwChosen_quarters (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (p : ℕ) (j : Fin n) :
    ∃ q : ℕ, (q : K) = 4 * fwChosen Q i p j := by
  unfold fwChosen fwCorner fwLower
  split
  · split
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
  · exact ⟨4, by norm_num⟩

/-- Every coordinate of round `p` has a common explicit positive denominator
`4p(p+1)` for `p>0`, with numerator between zero and the denominator. -/
theorem fwIterate_grid (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (p : ℕ) (j : Fin n) :
    ∃ q : ℕ, q ≤ 4*p*(p+1) ∧ (q : K) = (4*p*(p+1) : K)*fwIterate Q i p j := by
  choose u hu using fun k => fwChosen_quarters Q i k j
  let num := 2 * ∑ k ∈ Finset.range p, (k+1)*u k
  have hnum : (num : K) = (4*p*(p+1) : K)*fwIterate Q i p j := by
    dsimp [num]
    push_cast
    simp_rw [hu]
    have h := fwIterate_weighted Q i p j
    simp_rw [show ∀ k : ℕ, ((k:K)+1)*(4*fwChosen Q i k j) =
      4*(((k:K)+1)*fwChosen Q i k j) by intro k; ring, ← Finset.mul_sum]
    linear_combination -4 * h
  refine ⟨num, ?_, hnum⟩
  have h := mul_le_mul_of_nonneg_left ((fwIterate_mem Q i p j).2)
    (show (0:K) ≤ 4*p*(p+1) by positivity)
  rw [mul_one, ← hnum] at h
  exact_mod_cast h

private theorem fwCastLower (i j : Fin n) :
    (fwLower (K := ℚ) i j : K) = fwLower i j := by
  by_cases h : j=i <;> simp [fwLower,h]

private theorem fwCastCorner (i : Fin n) (g : Fin n → ℚ) (j : Fin n) :
    (fwCorner (K := ℚ) i g j : K) = fwCorner i (fun k => (g k : K)) j := by
  by_cases h : 0 ≤ g j <;> simp [fwCorner, h, fwCastLower]

private theorem fwCastStep (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) (z : Fin n → ℚ)
    (a : ℚ) (j : Fin n) :
    (fwStep (K := ℚ) Q i z a j : K) =
      fwStep (Q.map (Rat.castHom K)) i (fun k => (z k : K)) (a : K) j := by
  let f := Rat.castHom K
  have h₁ : f ∘ (Q *ᵥ z) = Q.map f *ᵥ (f ∘ z) := funext (f.map_mulVec Q z)
  have h₂ : f ∘ ((Q *ᵥ z) ᵥ* Q) = (Q.map f *ᵥ (f ∘ z)) ᵥ* Q.map f := by
    rw [← h₁]
    exact funext (f.map_vecMul Q (Q *ᵥ z))
  change ((z j + a * (fwCorner i ((Q *ᵥ z) ᵥ* Q) j - z j) : ℚ) : K) = _
  push_cast
  rw [fwCastCorner]
  change _ + _ * (fwCorner i (f ∘ ((Q *ᵥ z) ᵥ* Q)) j - _) = _
  rw [h₂]
  rfl

/-- All rational corner comparisons commute with the canonical ordered-field embedding. -/
theorem fwCastIterate_field (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) (p : ℕ) :
    (fun j => (fwIterate (K := ℚ) Q i p j : K)) = fwIterate (Q.map (Rat.castHom K)) i p := by
  induction p with
  | zero => exact funext (fwCastLower i)
  | succ p ih =>
    funext j
    change (fwStep (K := ℚ) Q i (fwIterate Q i p) _ j : K) = fwStep _ _ _ _ j
    rw [fwCastStep, ih]
    push_cast
    rfl

theorem fwCastEnergy_field (Q : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℚ) :
    (fwEnergy (K := ℚ) Q z : K) = fwEnergy (Q.map (Rat.castHom K)) (fun j => (z j : K)) := by
  let f := Rat.castHom K
  have h₁ : f ∘ (Q *ᵥ z) = Q.map f *ᵥ (f ∘ z) := funext (f.map_mulVec Q z)
  exact (f.map_dotProduct _ _).trans (by rw [h₁]; rfl)

/-- Rational execution reproduces every coordinate of execution in the real field. -/
theorem fwCastIterate (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) (p : ℕ) :
    (fun j => (fwIterate (K := ℚ) Q i p j : ℝ)) = fwIterate (Q.map (Rat.castHom ℝ)) i p :=
  fwCastIterate_field (K:=ℝ) Q i p

/-- The rational label computation is complete even when the strict witness is real. -/
theorem fwRat_accept_real (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Qᵀ = Q) (he : Q * Q = Q)
    (i : Fin n) (w : Fin n → ℝ) (hw : InLabelBox i w) (τ : ℚ)
    (hwτ : fwEnergy (Q.map (Rat.castHom ℝ)) w ≤ (τ:ℝ)^2/4)
    (p : ℕ) (hp : 8*n ≤ (p:ℚ)*τ^2) : fwEnergy Q (fwArray Q i p).get ≤ τ^2 := by
  let f := Rat.castHom ℝ
  have hs' : (Q.map f)ᵀ = Q.map f := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M.map f) hs
  have he' : (Q.map f) * (Q.map f) = Q.map f := by
    ext j k
    rw [← f.map_matrix_mul, he]
    rfl
  have h := fwIterate_accept (Q.map f) hs' he' i w hw (τ:ℝ) hwτ p (by exact_mod_cast hp)
  rw [fwArray_correct]
  apply Rat.cast_le (K := ℝ).mp
  rw [fwCastEnergy_field, fwCastIterate]
  exact_mod_cast h

/-- The paper's tolerance and integer round count, computed from the dimension alone. -/
def fwTolerance (n : ℕ) : ℚ := 1 / (1000*n : ℚ)

def fwRounds (n : ℕ) : ℕ := 8000000 * n^3

theorem fwRounds_exact (i : Fin n) :
    (fwRounds n : ℚ) * fwTolerance n ^ 2 = 8*n := by
  have hn : n ≠ 0 := Nat.ne_zero_of_lt i.isLt
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold fwRounds fwTolerance
  push_cast
  field_simp
  ring

/-- The squared test on its final rational iterate. -/
def fwLabel (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : Bool :=
  decide (fwEnergy Q (fwArray Q i (fwRounds n)).get ≤ fwTolerance n ^ 2)

theorem fwLabel_complete (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Qᵀ = Q) (he : Q*Q = Q)
    (i : Fin n) (w : Fin n → ℝ) (hw : InLabelBox i w)
    (hstrict : fwEnergy (Q.map (Rat.castHom ℝ)) w ≤ (fwTolerance n : ℝ)^2 / 4) :
    fwLabel Q i = true := by
  apply decide_eq_true
  exact fwRat_accept_real Q hs he i w hw _ hstrict _ (fwRounds_exact i).ge

theorem fwLabel_sound (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) (h : fwLabel Q i = true) :
    ∃ z : Fin n → ℚ, InLabelBox i z ∧ fwEnergy Q z ≤ fwTolerance n ^ 2 := by
  have hz := fwIterate_mem Q i (fwRounds n)
  rw [← fwArray_correct] at hz
  exact ⟨_, hz, of_decide_eq_true h⟩

/-- Reduced rational coordinates retain numerator and denominator of magnitude at most
`4p(p+1)` after each positive round. -/
theorem fwArray_reduced_size (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (p : ℕ) (hp : 0 < p) (j : Fin n) :
    ((fwArray Q i p).get j).den ≤ 4*p*(p+1) ∧
      ((fwArray Q i p).get j).num.natAbs ≤ 4*p*(p+1) := by
  rw [fwArray_correct]
  let z := fwIterate Q i p j
  let d := 4*p*(p+1)
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨k, _, hk⟩ := fwIterate_grid Q i p j
  have hcast : (k : ℚ) = (d : ℚ) * z := by simpa [d,z] using hk
  have heq : z = Rat.divInt k d := by
    rw [Rat.divInt_eq_div]
    push_cast
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hd.ne')).mpr
    rwa [mul_comm, eq_comm]
  have hdvd : z.den ∣ d := by
    have hh := Rat.den_dvd (k : ℤ) (d : ℤ)
    rw [← heq] at hh
    exact_mod_cast hh
  have hb := fwIterate_mem Q i p j
  have h₀ : 0 ≤ z := le_trans (fwLower_bounds i j).1 hb.1
  have h₁ : z.num ≤ (z.den : ℤ) := by simpa using (Rat.le_iff z 1).mp hb.2
  have h₂ := Rat.num_nonneg.mpr h₀
  have hs : z.num.natAbs ≤ z.den := by omega
  exact ⟨Nat.le_of_dvd hd hdvd, hs.trans (Nat.le_of_dvd hd hdvd)⟩

theorem inLabelBox_iff (i : Fin n) (z : Fin n → K) :
    InLabelBox i z ↔ (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ 1/4 ≤ z i := by
  constructor
  · intro h
    refine ⟨fun j => ⟨le_trans (fwLower_bounds i j).1 (h j).1, (h j).2⟩, ?_⟩
    simpa [fwLower] using (h i).1
  · rintro ⟨h, hi⟩ j
    refine ⟨?_, (h j).2⟩
    by_cases hj : j=i
    · simpa [hj, fwLower] using hi
    · simpa [hj, fwLower] using (h j).1

theorem fwLabel_sound_real (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (h : fwLabel Q i = true) :
    ∃ z : Fin n → ℝ, InLabelBox i z ∧
      fwEnergy (Q.map (Rat.castHom ℝ)) z ≤ (fwTolerance n : ℝ)^2 := by
  obtain ⟨w, hw, he⟩ := fwLabel_sound Q i h
  refine ⟨fun j => (w j : ℝ), ?_, ?_⟩
  · intro j
    rcases hw j with ⟨h₁,h₂⟩
    constructor
    · change fwLower i j ≤ (w j : ℝ)
      rw [← fwCastLower]
      exact Rat.cast_le.mpr h₁
    · change (w j : ℝ) ≤ 1
      exact_mod_cast h₂
  · rw [← fwCastEnergy_field]
    exact_mod_cast he

/-- Equality of the executable rational Boolean answer and the exact real energy test
on the same input matrix and number of iterations. -/
theorem fwLabel_cast_eq (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    fwLabel Q i = decide (fwEnergy (Q.map (Rat.castHom ℝ))
      (fwIterate (Q.map (Rat.castHom ℝ)) i (fwRounds n)) ≤ (fwTolerance n : ℝ)^2) := by
  unfold fwLabel
  rw [decide_eq_decide, fwArray_correct, ← fwCastIterate, ← fwCastEnergy_field, ← Rat.cast_pow]
  exact Rat.cast_le.symm

/-- A fixed common denominator and a magnitude bound for intermediate rational registers. -/
def FWBounded (D : ℕ) (M x : ℚ) : Prop := x.den ∣ D ∧ |x| ≤ M

private theorem fwSumDen {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℚ) (D : ℕ)
    (h : ∀ j ∈ s, (x j).den ∣ D) : (∑ j ∈ s, x j).den ∣ D := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd
      (h j (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))

/-- Includes the products and every partial sum in a dot product evaluated coordinatewise. -/
theorem fwDotPartialBound (s : Finset (Fin n)) (x y : Fin n → ℚ) (D E : ℕ) (U V : ℚ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hx : ∀ j, FWBounded D U (x j))
    (hy : ∀ j, FWBounded E V (y j)) :
    FWBounded (D*E) (n*U*V) (∑ j ∈ s, x j*y j) := by
  constructor
  · apply fwSumDen
    exact fun j _ => (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul (hx j).1 (hy j).1)
  · have hc : (s.card : ℚ) ≤ n := by
      exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin n)
    calc
      _ ≤ ∑ j ∈ s, |x j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ s, U*V := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hx j).2 (hy j).2 (abs_nonneg _) hU
      _ = (s.card : ℚ)*(U*V) := by simp
      _ ≤ (n:ℚ)*(U*V) := mul_le_mul_of_nonneg_right hc (mul_nonneg hU hV)
      _ = _ := by ring

/-- Each coordinate of an orthogonal projection matrix has magnitude at most one. -/
theorem fwProjection_entry (Q : Matrix (Fin n) (Fin n) K) (hs : Qᵀ = Q) (he : Q*Q = Q)
    (i j : Fin n) : |Q i j| ≤ 1 := by
  have h := fwEnergy_le_norm_sq Q hs he (Pi.single j 1)
  rw [fwEnergy, mulVec_single_one, dotProduct_single_one, Pi.single_eq_same] at h
  have hh : Q i j * Q i j ≤ Q.col j ⬝ᵥ Q.col j :=
    Finset.single_le_sum (f := fun k => Q k j*Q k j) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one _).mp (by simpa [pow_two] using hh.trans h)

/-- The first two families are all partial matrix-vector sums for the residual and the
gradient. The last family contains every partial sum for the final exact energy test. -/
theorem fwIntermediateBounds (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Qᵀ = Q) (he : Q*Q = Q)
    (D B : ℕ) (hD : ∀ j k, (Q j k).den ∣ D) (z : Fin n → ℚ)
    (hden : ∀ k, (z k).den ∣ B) (hbox : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (j : Fin n) (s : Finset (Fin n)) :
    FWBounded (D*B) n (∑ k ∈ s, Q j k*z k) ∧
    FWBounded (D*B*D) ((n:ℚ)^2) (∑ k ∈ s, (Q *ᵥ z) k*Q k j) ∧
    FWBounded ((D*B)^2) ((n:ℚ)^3) (∑ k ∈ s, (Q *ᵥ z) k*(Q *ᵥ z) k) := by
  have hQ a b : FWBounded D 1 (Q a b) := ⟨hD _ _, fwProjection_entry Q hs he _ _⟩
  have hz a : FWBounded B 1 (z a) := ⟨hden _, (abs_of_nonneg (hbox a).1).le.trans (hbox a).2⟩
  have hfirst (k : Fin n) (r : Finset (Fin n)) :
      FWBounded (D*B) n (∑ l ∈ r, Q k l * z l) := by
    simpa only [mul_one] using fwDotPartialBound r (Q k) z D B 1 1 zero_le_one zero_le_one (hQ k) hz
  have hu k : FWBounded (D*B) n ((Q *ᵥ z) k) := hfirst k Finset.univ
  refine ⟨hfirst j s, ?_, ?_⟩
  · simpa only [sq, mul_one] using fwDotPartialBound s (Q *ᵥ z) (fun k => Q k j)
      (D*B) D n 1 (by positivity) zero_le_one hu (fun k => hQ k j)
  · simpa only [pow_succ, pow_zero, one_mul] using fwDotPartialBound s (Q *ᵥ z) (Q *ᵥ z)
      (D*B) (D*B) n n (by positivity) (by positivity) hu hu

/-- The explicit fraction bounds also bound both fields of Lean's reduced rational encoding. -/
theorem fwBounded_encoding {d m : ℕ} {x : ℚ} (hd : 0 < d) (h : FWBounded d m x) :
    x.den ≤ d ∧ x.num.natAbs ≤ m*d := by
  have hd' := Nat.le_of_dvd hd h.1
  refine ⟨hd', ?_⟩
  have he : (x.num.natAbs : ℚ) = |x| * (x.den : ℚ) := by
    calc
      (x.num.natAbs : ℚ) = |(x.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      _ = |x * (x.den : ℚ)| := by rw [x.mul_den_eq_num]
      _ = |x| * (x.den : ℚ) := by rw [abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ x.den from Nat.cast_nonneg _)]
  have hm : (x.num.natAbs : ℚ) ≤ (m : ℚ) * d := by
    rw [he]
    exact mul_le_mul h.2 (by exact_mod_cast hd') (by positivity) (by positivity)
  exact_mod_cast hm

end Geometry
end LinearProgramming
end Optimization
end OAI
