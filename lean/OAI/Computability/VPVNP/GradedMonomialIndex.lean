import OAI.Computability.VPVNP.MacaulayRows
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Count

/-!
# Streaming indices for bounded monomials

Appendix D orders monomials by total degree and then lexicographically. The
outer radix digit stores the degree, and the remaining digits store the
exponents, with variable zero in the most significant position. Removing the
codes with an inconsistent degree gives a dense indexing. Both directions use
counter loops, so neither needs a list of the monomials.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

/-- Count admissible codes strictly below the bound. -/
def countCodes (p : ℕ → Bool) (n : ℕ) : ℕ :=
  Fin.foldl n (fun count i => if p i then count + 1 else count) 0

theorem countCodes_eq (p : ℕ → Bool) (n : ℕ) :
    countCodes p n = Nat.count (fun i => p i = true) n := by
  induction n with
  | zero => simp [countCodes]
  | succ n ih =>
    rw [countCodes, Fin.foldl_succ_last, Nat.count_succ, ← ih]
    cases hp : p n <;> simp [countCodes, hp, Fin.last]

/-- Scan an interval until the zero-based ordinal of a valid code is reached.
The loop keeps only the current code, remaining interval and remaining ordinal. -/
def selectCode (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | first, 0, _ => first
  | first, len + 1, k =>
    if p first then
      if k = 0 then first else selectCode p (first + 1) len (k - 1)
    else selectCode p (first + 1) len k
termination_by _ len _ => len

theorem selectCode_spec (p : ℕ → Bool) (first len k : ℕ)
    (hk : countCodes p first + k < countCodes p (first + len)) :
    let c := selectCode p first len k
    first ≤ c ∧ c < first + len ∧ p c = true ∧ countCodes p c = countCodes p first + k := by
  induction len generalizing first k with
  | zero => simp at hk
  | succ len ih =>
    have hstep : countCodes p (first + 1) = countCodes p first + if p first then 1 else 0 := by
      rw [countCodes_eq, countCodes_eq, Nat.count_succ]
    have hend : first + (len + 1) = first + 1 + len := by omega
    by_cases hp : p first = true
    · by_cases hz : k = 0
      · subst k
        simp [selectCode, hp]
      · have h := ih (first + 1) (k - 1) (by rw [hstep, ite_eq_left hp, ← hend]; omega)
        simp only [selectCode, ite_eq_left hp, ite_eq_right hz, hend]
        rw [hstep, ite_eq_left hp] at h
        exact ⟨by omega, h.2.1, h.2.2.1, by omega⟩
    · have h := ih (first + 1) k (by simpa [hstep, hp, ← hend] using hk)
      simp only [selectCode, ite_eq_right hp, hend]
      rw [hstep, ite_eq_right hp, Nat.add_zero] at h
      exact ⟨by omega, h.2⟩

private def test {n : ℕ} (p : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then p ⟨i,h⟩ else false

/-- Dense numbering of the selected indices of a finite interval. -/
def denseCount {n : ℕ} (p : Fin n → Bool) : ℕ := countCodes (test p) n

private theorem selected_spec {n : ℕ} (p : Fin n → Bool) (k : Fin (denseCount p)) :
    let c := selectCode (test p) 0 n k
    c < n ∧ test p c = true ∧ countCodes (test p) c = k.val := by
  have h := selectCode_spec (test p) 0 n k (by simpa [countCodes_eq, denseCount] using k.isLt)
  simpa only [Nat.zero_add, countCodes_eq, Nat.count_zero] using h.2

/-- The ordinal of each selected code and the inverse ordinal query.
Both use scans of the same interval. -/
def denseEquiv {n : ℕ} (p : Fin n → Bool) :
    Fin (denseCount p) ≃ {i : Fin n // p i = true} where
  toFun k := by
    let c := selectCode (test p) 0 n k
    have hc := selected_spec p k
    exact ⟨⟨c, hc.1⟩, by simpa [test, hc.1] using hc.2.1⟩
  invFun i := ⟨countCodes (test p) i.val.val, by
    rw [denseCount, countCodes_eq, countCodes_eq]
    exact Nat.count_strict_mono (by simpa [test, i.val.isLt] using i.prop) i.val.isLt⟩
  left_inv k := Fin.ext (selected_spec p k).2.2
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    let k : Fin (denseCount p) := ⟨countCodes (test p) i.val.val, by
      rw [denseCount, countCodes_eq, countCodes_eq]
      exact Nat.count_strict_mono (by simpa [test, i.val.isLt] using i.prop) i.val.isLt⟩
    have h := selected_spec p k
    change selectCode (test p) 0 n k = i.val.val
    apply Nat.count_injective (p := fun j => test p j = true) h.2.1 (by simpa [test, i.val.isLt] using i.prop)
    simpa only [countCodes_eq, k] using h.2.2

/-- Unfiltered addresses consist of one degree digit and `t` exponent digits. -/
def rawSize (t D : ℕ) := (D + 1) * (D + 1) ^ t

private def split {t D : ℕ} (c : Fin (rawSize t D)) :
    Fin (D + 1) × Fin ((D + 1) ^ t) := finProdFinEquiv.symm c

/-- Read a single exponent by radix division and remainder. -/
def digit {t D : ℕ} (c : Fin (rawSize t D)) (i : Fin t) : ℕ :=
  (finFunctionFinEquiv.symm (split c).2 i.rev).val

/-- Test that the exponent digits of a raw monomial index sum to its recorded total degree. -/
def admissible {t D : ℕ} (c : Fin (rawSize t D)) : Bool :=
  decide ((∑ i, digit c i) = (split c).1.val)

/-- Number of monomials through degree `D`, obtained without a monomial table. -/
def size (t D : ℕ) := denseCount (@admissible t D)

/-- Build the formal exponent vector for a tuple in the finite label alphabet. -/
def exponentVector {t : ℕ} (f : Fin t → ℕ) : Fin t →₀ ℕ where
  toFun := f
  support := Finset.univ.filter fun i => f i ≠ 0
  mem_support_toFun := by simp

private def degree {t D : ℕ} (a : BoundedMonomial t D) : Fin (D + 1) :=
  ⟨a.val.sum (fun _ e => e), Nat.lt_succ_of_le a.prop⟩

/-- Graded-lex key of a bounded monomial, before removing unused codes. -/
def rawCode {t D : ℕ} (a : BoundedMonomial t D) : Fin (rawSize t D) :=
  finProdFinEquiv (degree a, finFunctionFinEquiv (fun i => a.encode i.rev))

private theorem split_rawCode {t D : ℕ} (a : BoundedMonomial t D) :
    split (rawCode a) = (degree a, finFunctionFinEquiv (fun i => a.encode i.rev)) :=
  finProdFinEquiv.symm_apply_apply _

@[simp] theorem digit_rawCode {t D : ℕ} (a : BoundedMonomial t D) (i : Fin t) :
    digit (rawCode a) i = a.val i := by
  simp [digit, split_rawCode, BoundedMonomial.encode]

theorem admissible_rawCode {t D : ℕ} (a : BoundedMonomial t D) :
    admissible (rawCode a) = true := by
  simp [admissible, split_rawCode, degree, Finsupp.sum_fintype]

private def decodeRaw {t D : ℕ} (c : {c : Fin (rawSize t D) // admissible c = true}) :
    BoundedMonomial t D := by
  refine ⟨exponentVector (digit c.val), ?_⟩
  have h : (∑ i, digit c.val i) = (split c.val).1.val := of_decide_eq_true c.prop
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact h.le.trans (Nat.le_of_lt_succ (split c.val).1.isLt)

private def validEquiv (t D : ℕ) :
    {c : Fin (rawSize t D) // admissible c = true} ≃ BoundedMonomial t D where
  toFun := decodeRaw
  invFun a := ⟨rawCode a, admissible_rawCode a⟩
  right_inv a := Subtype.ext (Finsupp.ext (digit_rawCode a))
  left_inv c := by
    apply Subtype.ext
    apply finProdFinEquiv.symm.injective
    change split (rawCode (decodeRaw c)) = split c.val
    rw [split_rawCode]
    apply Prod.ext
    · apply Fin.ext
      change (exponentVector (digit c.val)).sum (fun _ e => e) = _
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact of_decide_eq_true c.prop
    · apply finFunctionFinEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      funext i
      apply Fin.ext
      change digit c.val i.rev = _
      simp [digit]

/-- Computable dense graded-lex enumeration of all bounded monomials. -/
def enumeration (t D : ℕ) : Fin (size t D) ≃ BoundedMonomial t D :=
  (denseEquiv (@admissible t D)).trans (validEquiv t D)

/-- Read the exponent vector at a dense ordinal, without constructing a support set. -/
def indexedDigits {t D : ℕ} (k : Fin (size t D)) : Fin t → ℕ :=
  let c := (denseEquiv (@admissible t D) k).val
  digit c

theorem indexedDigits_eq {t D : ℕ} (k : Fin (size t D)) (i : Fin t) :
    indexedDigits k i = (enumeration t D k).val i := rfl

/-- The outer radix digit stores the total degree. -/
theorem degree_eq_outer {t D : ℕ} (a : BoundedMonomial t D) :
    (rawCode a).val / (D + 1) ^ t = a.val.sum (fun _ e => e) :=
  congrArg (fun x : Fin (D+1) × Fin ((D+1)^t) => x.1.val) (split_rawCode a)

/-- Dense ordinals have strictly increasing graded radix keys. -/
theorem enumeration_strictMono (t D : ℕ) : StrictMono (rawCode ∘ enumeration t D) := by
  intro i j hij
  have hi := selected_spec (@admissible t D) i
  have hj := selected_spec (@admissible t D) j
  have hlt : countCodes (test (@admissible t D)) (selectCode (test (@admissible t D)) 0 (rawSize t D) i) <
      countCodes (test (@admissible t D)) (selectCode (test (@admissible t D)) 0 (rawSize t D) j) := by
    rw [hi.2.2, hj.2.2]; exact hij
  simp only [countCodes_eq] at hlt
  have h := Nat.lt_of_count_lt_count hlt
  have key (k : Fin (size t D)) :
      (rawCode (enumeration t D k)).val = selectCode (test (@admissible t D)) 0 (rawSize t D) k := by
    exact congrArg (fun c : {c : Fin (rawSize t D) // admissible c = true} => c.val.val)
      ((validEquiv t D).symm_apply_apply (denseEquiv _ k))
  change (rawCode (enumeration t D i)).val < (rawCode (enumeration t D j)).val
  simpa only [key] using h

/-- The constant monomial gives dense ordinal zero, including when there are
no variables or when the degree bound is zero. -/
def constant (t D : ℕ) : BoundedMonomial t D := ⟨0, by simp⟩

theorem constant_ordinal (t D : ℕ) : ((enumeration t D).symm (constant t D)).val = 0 := by
  have hcode : (rawCode (constant t D)).val = 0 := by
    simp [rawCode, constant, degree, BoundedMonomial.encode]
  change countCodes _ (rawCode (constant t D)).val = 0
  simp [hcode, countCodes_eq]

theorem size_pos (t D : ℕ) : 0 < size t D := ((enumeration t D).symm (constant t D)).pos

theorem enumeration_first (t D : ℕ) :
    enumeration t D ⟨0, size_pos t D⟩ = constant t D :=
  (enumeration t D).eq_symm_apply.mp (Fin.ext (constant_ordinal t D).symm)

theorem size_eq_card (t D : ℕ) : size t D = Fintype.card (BoundedMonomial t D) := by
  simpa using Fintype.card_congr (enumeration t D)

theorem rawSize_le_pow {t D b : ℕ} (h : D + 1 ≤ 2 ^ b) :
    rawSize t D ≤ 2 ^ (b * (t + 1)) := by
  rw [pow_mul, pow_succ']
  exact Nat.mul_le_mul h (Nat.pow_le_pow_left h t)

end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
