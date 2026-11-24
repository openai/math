import OAI.Computability.VPVNP.FormalSchur
import OAI.Computability.VPVNP.MatrixPowerQueries

/-!
# Bivariate coefficient queries for the Schur product

Appendix D.2 of *VP and VNP differ over every field* uses the Schur product to
compute any specified coefficient of `det (1 - uM(z))`. Each query uses an
oracle for individual scalar coefficients of the matrix entries. Its two
recursive computations split the list of factors and the exponents of matrix
powers in half.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Query one bidegree of the first factor using only coefficients of matrix entries. -/
def headFactorQuery (entry : Fin (n + 1) → Fin (n + 1) → ℕ → R) (u z : ℕ) : R :=
  match u with
  | 0 => if z = 0 then 1 else 0
  | 1 => -entry 0 0 z
  | h + 2 => -(∑ i : Fin n, ∑ j : Fin n, ∑ d ∈ Finset.antidiagonal z,
      (∑ e ∈ Finset.antidiagonal d.1, entry 0 i.succ e.1 *
        powerEntryCoeff (fun a b : Fin n => entry a.succ b.succ) h i j e.2) * entry j.succ 0 d.2)

theorem headFactorQuery_correct (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial R))
    (entry : Fin (n + 1) → Fin (n + 1) → ℕ → R) (he : ∀ i j z, entry i j z = (M i j).coeff z)
    (u z : ℕ) : headFactorQuery entry u z = (PowerSeries.coeff u (headFactor M)).coeff z := by
  rw [coeff_headFactor]
  cases u with
  | zero => simp [headFactorQuery, Polynomial.coeff_one]
  | succ u =>
    cases u with
    | zero => simp [headFactorQuery, he]
    | succ h =>
      simp only [headFactorQuery, Polynomial.coeff_neg, Polynomial.finsetSum_coeff,
        Polynomial.coeff_mul, powerEntryCoeff_correct (M.submatrix Fin.succ Fin.succ)
          (fun a b : Fin n => entry a.succ b.succ) (fun a b z => he a.succ b.succ z), he]

/-- Compute a coefficient of the Schur factor with sequential scans of
both matrix indices and both degree splits. Each queried power of the
trailing matrix is also evaluated by streaming scans. -/
def streamedHeadFactorQuery (entry : Fin (n + 1) → Fin (n + 1) → ℕ → R) (u z : ℕ) : R :=
  match u with
  | 0 => if z = 0 then 1 else 0
  | 1 => -entry 0 0 z
  | h + 2 => -(streamSum n fun i => streamSum n fun j =>
      streamAntiSum z fun d₁ d₂ =>
        (streamAntiSum d₁ fun e₁ e₂ => entry 0 i.succ e₁ *
          streamedPowerEntryCoeff (fun a b : Fin n => entry a.succ b.succ) h i j e₂) *
        entry j.succ 0 d₂)

theorem streamedHeadFactorQuery_eq (entry : Fin (n + 1) → Fin (n + 1) → ℕ → R) (u z : ℕ) :
    streamedHeadFactorQuery entry u z = headFactorQuery entry u z := by
  rcases u with _ | _ | h
  · rfl
  · rfl
  · simp only [streamedHeadFactorQuery, headFactorQuery, streamSum_eq, streamAntiSum_eq,
      streamedPowerEntryCoeff_eq]

section BalancedProduct

variable {ι R : Type*}

/-- Query a consecutive block of factors. Each internal node splits the block
into two halves. Each root-to-leaf path makes exactly `depth` such splits. -/
def balancedProduct (unit : ι → R) (combine : (ι → R) → (ι → R) → ι → R)
    (read : ℕ → ι → R) : ℕ → ℕ → ℕ → ι → R
  | 0, first, count, q => if count = 0 then unit q else read first q
  | depth + 1, first, count, q =>
    let half := count / 2
    combine (fun r => balancedProduct unit combine read depth first half r)
      (fun r => balancedProduct unit combine read depth (first + half) (count - half) r) q

private theorem balancedProduct_eq {A : Type*} [CommMonoid A] (coef : A → ι → R)
    (unit : ι → R) (combine : (ι → R) → (ι → R) → ι → R)
    (hunit : unit = coef 1) (hmul : ∀ a b, combine (coef a) (coef b) = coef (a * b))
    (factor : ℕ → A) (depth first count : ℕ) (hcount : count ≤ 2 ^ depth) :
    balancedProduct unit combine (fun i => coef (factor i)) depth first count =
      coef (∏ j ∈ Finset.range count, factor (first + j)) := by
  induction depth generalizing first count with
  | zero =>
    funext q
    have h : count = 0 ∨ count = 1 := by simp only [pow_zero] at hcount; omega
    rcases h with rfl | rfl <;> simp [balancedProduct, hunit]
  | succ depth ih =>
    funext q
    rw [pow_succ] at hcount
    let half := count / 2
    have hleft : half ≤ 2 ^ depth := by dsimp [half]; omega
    have hright : count - half ≤ 2 ^ depth := by dsimp [half]; omega
    rw [balancedProduct, ih first half hleft, ih (first + half) (count - half) hright, hmul]
    apply congrArg (fun a => coef a q)
    have hsplit := Finset.prod_range_add (fun j => factor (first + j)) half (count - half)
    rw [Nat.add_sub_of_le (show half ≤ count by dsimp [half]; omega)] at hsplit
    simpa only [Nat.add_assoc] using hsplit.symm

variable [CommSemiring R]

/-- Coefficient query for the factors of the Appendix D.2 determinant in
`R[z][[u]]`. Both degree splits stream over a single counter. The parameter
`depth = Nat.clog 2 count` suffices for any number of consecutive factors. -/
def balancedBivariateProduct (read : ℕ → ℕ → ℕ → R) (depth first count u z : ℕ) : R :=
  balancedProduct (fun p : ℕ × ℕ => if p.1 = 0 ∧ p.2 = 0 then 1 else 0)
    (fun left right p => streamAntiSum p.1 fun a₁ a₂ => streamAntiSum p.2 fun b₁ b₂ =>
      left (a₁, b₁) * right (a₂, b₂))
    (fun i p => read i p.1 p.2) depth first count (u, z)

theorem balancedBivariateProduct_eq (factor : ℕ → PowerSeries (Polynomial R))
    (depth first count u z : ℕ) (hcount : count ≤ 2 ^ depth) :
    balancedBivariateProduct (fun i a b => (PowerSeries.coeff a (factor i)).coeff b)
      depth first count u z =
      (PowerSeries.coeff u (∏ j ∈ Finset.range count, factor (first + j))).coeff z := by
  unfold balancedBivariateProduct
  apply congrFun (balancedProduct_eq (fun s (p : ℕ × ℕ) => (PowerSeries.coeff p.1 s).coeff p.2)
    _ _ ?_ ?_ factor depth first count hcount) (u, z)
  · funext p
    by_cases hu : p.1 = 0 <;> simp [PowerSeries.coeff_one, Polynomial.coeff_one, hu]
  · intro a b
    funext p
    simp only [streamAntiSum_eq, PowerSeries.coeff_mul, Polynomial.finsetSum_coeff,
      Polynomial.coeff_mul]

end BalancedProduct

/-- Query a Schur factor by its absolute index, giving the identity series
at indices outside the matrix. -/
private def determinantLeaf (entry : Fin n → Fin n → ℕ → R) (a u z : ℕ) : R :=
  if h : a < n then
    let i : Fin n := ⟨a, h⟩
    streamedHeadFactorQuery (fun b c => entry (suffixIndex i b) (suffixIndex i c)) u z
  else if u = 0 ∧ z = 0 then 1 else 0

private theorem determinantLeaf_correct (M : Matrix (Fin n) (Fin n) (Polynomial R))
    (entry : Fin n → Fin n → ℕ → R) (he : ∀ i j z, entry i j z = (M i j).coeff z) (a u z : ℕ) :
    determinantLeaf entry a u z = (PowerSeries.coeff u (if h : a < n then
      let i : Fin n := ⟨a, h⟩
      headFactor (M.submatrix (suffixIndex i) (suffixIndex i)) else 1)).coeff z := by
  by_cases h : a < n
  · simp only [determinantLeaf, h, dite_eq_left, streamedHeadFactorQuery_eq]
    apply headFactorQuery_correct
    intro b c z
    exact he _ _ z
  · by_cases hu : u = 0 <;> by_cases hz : z = 0 <;>
      simp [determinantLeaf, h, hu, hz, PowerSeries.coeff_one, Polynomial.coeff_one]

private theorem padded_prod_eq {A : Type*} [CommMonoid A] {n count : ℕ} (h : n ≤ count)
    (f : Fin n → A) : (∏ i ∈ Finset.range count, if hi : i < n then f ⟨i, hi⟩ else 1) = ∏ i, f i := by
  let F (i : ℕ) := if hi : i < n then f ⟨i, hi⟩ else 1
  change (∏ i ∈ Finset.range count, F i) = _
  calc
    _ = ∏ i ∈ Finset.range n, F i := Finset.prod_subset (Finset.range_mono h)
      (fun i _ hi => dite_eq_right (fun hi' => hi (Finset.mem_range.mpr hi')) ) |>.symm
    _ = ∏ i : Fin n, F i.val := (Fin.prod_univ_eq_prod_range F n).symm
    _ = _ := Finset.prod_congr rfl fun i _ => dite_eq_left i.isLt

/-- Compute a scalar bidegree of `det (1-uM(z))` without constructing its polynomial. -/
def determinantQuery (entry : Fin n → Fin n → ℕ → R) (u z : ℕ) : R :=
  balancedBivariateProduct (determinantLeaf entry) (Nat.clog 2 n) 0 n u z

theorem determinantQuery_eq (M : Matrix (Fin n) (Fin n) (Polynomial R))
    (entry : Fin n → Fin n → ℕ → R) (he : ∀ i j z, entry i j z = (M i j).coeff z) (u z : ℕ) :
    determinantQuery entry u z = (M.charpolyRev.coeff u).coeff z := by
  let F (a : ℕ) : PowerSeries (Polynomial R) := if h : a < n then
    let i : Fin n := ⟨a, h⟩
    headFactor (M.submatrix (suffixIndex i) (suffixIndex i)) else 1
  have hleaf : determinantLeaf entry = fun a u z => (PowerSeries.coeff u (F a)).coeff z :=
    funext fun a => funext fun u => funext fun z => determinantLeaf_correct M entry he a u z
  rw [determinantQuery, hleaf, balancedBivariateProduct_eq F _ _ _ _ _ (Nat.le_pow_clog (by decide) n)]
  have hprod : (∏ j ∈ Finset.range n, F (0 + j)) = (M.charpolyRev : PowerSeries (Polynomial R)) := by
    simp only [Nat.zero_add, charpolyRev_eq_schurProduct]
    exact padded_prod_eq (n := n) le_rfl
      (fun i => headFactor (M.submatrix (suffixIndex i) (suffixIndex i)))
  rw [hprod, Polynomial.coeff_coe]

end RankQuery

end VPVNP
end Computability
end OAI
