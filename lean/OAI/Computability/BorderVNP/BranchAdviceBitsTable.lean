import OAI.Computability.BorderVNP.BranchAdviceBits
import OAI.Computability.BorderVNP.BranchSlice
import OAI.Computability.BorderVNP.ParseTable

/-! # The size bounds specialized to the universal homogeneous table

The paired family of degree `n` has `2n` variables, so all its coordinates fit in
`(n+1)^(2n)` digit slots. The table for a gate budget `s` uses the actual terminal and
binary-production labels from Lemma 2.2. Its degree in those parameters is at most
`2n−1`. Size estimates below are indexed by `M`, allowing `s` to grow faster than a
polynomial in `n` while `n,s ≤ M`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open VPVNP

private theorem digit_le_of_degree {k n : ℕ} (ν : DegreeMonomial (Fin k) n) (i : Fin k) :
    ν.val i ≤ n := (Finsupp.le_degree i ν.val).trans ν.prop.le

/-- The number of formal coefficient coordinates is bounded by the full digit box. -/
theorem card_degreeMonomial_le (k n : ℕ) :
    Nat.card (DegreeMonomial (Fin k) n) ≤ (n+1)^k := by
  let enc (ν : DegreeMonomial (Fin k) n) (i : Fin k) : Fin (n+1) := ⟨ν.val i, Nat.lt_succ_of_le (digit_le_of_degree ν i)⟩
  have hinj : Function.Injective enc := fun x y eq ↦ Subtype.ext <| Finsupp.ext fun i ↦
    congrArg Fin.val (congrFun eq i)
  simpa only [Nat.card_eq_fintype_card (α := Fin k → Fin (n+1)), Fintype.card_fun, Fintype.card_fin]
    using Nat.card_le_card_of_injective enc hinj

/-- The paper's digit exponent on all degree-`n` monomials, including non-multilinear
monomials whose prescribed coefficient is zero. -/
def pairedDegreeExponent (n : ℕ) (ν : DegreeMonomial (Fin (2*n)) n) : ℕ :=
  digitExponent (n+1) ν.val

/-- The slice coefficients occupy distinct slots, also at length zero. -/
theorem pairedDegreeExponent_injective (n : ℕ) : Function.Injective (pairedDegreeExponent n) := by
  cases n with
  | zero =>
    intro x y _
    apply Subtype.ext
    apply Finsupp.ext
    exact fun i ↦ Fin.elim0 (i.cast (by decide))
  | succ n =>
    intro x y eq
    exact Subtype.ext (DFunLike.coe_injective (digitExponent_inj (by omega)
      (fun i ↦ Nat.lt_succ_of_le (digit_le_of_degree x i))
      (fun i ↦ Nat.lt_succ_of_le (digit_le_of_degree y i)) eq))

/-- All original coefficient slots are below the first hyperplane exponent. -/
theorem pairedDegreeExponent_lt (n : ℕ) (ν : DegreeMonomial (Fin (2*n)) n) :
    pairedDegreeExponent n ν < (n+1)^(2*n) := by
  cases n with
  | zero => simp [pairedDegreeExponent, digitExponent]
  | succ n => exact digitExponent_lt (by omega) (fun i ↦ Nat.lt_succ_of_le (digit_le_of_degree ν i))

/-- Number of advice input parameters in the genuine universal parse table. -/
def pairedTableParameters (n s : ℕ) : ℕ :=
  Fintype.card (GrammarLabel (Fin (2*n)) (ParseTable.State (Fin (2*n)) s) n)

/-- The table has polynomially many labels in the length and gate budget. -/
theorem pairedTableParameters_le (n s : ℕ) :
    pairedTableParameters n s ≤ (2*n+s+1)*(2*n) + n^2*(2*n+s+1)^3 := by
  cases n with
  | zero => simp [pairedTableParameters, ParseTable.State]
  | succ n =>
    simpa [pairedTableParameters] using ParseTable.parameter_count_le (Fin (2*(n+1))) n s

/-- The parameter count remains polynomial when both `n` and `s` are measured against `M`. -/
theorem pairedTableParameters_polynomial {n s : ℕ → ℕ} (hn : PolynomiallyBounded n)
    (hs : PolynomiallyBounded s) : PolynomiallyBounded (fun m ↦ pairedTableParameters (n m) (s m)) := by
  let c := PolynomiallyBounded.const
  have vars := (c 2).mul hn
  have states := (vars.add hs).add (c 1)
  exact ((states.mul vars).add ((hn.pow 2).mul (states.pow 3))).of_le fun m ↦ pairedTableParameters_le ..

/-- Actual simultaneous grid and displacement degree bounds for the paired table. -/
theorem pairedTable_choice_bits {n s : ℕ → ℕ} (hn : PolynomiallyBounded n) (hs : PolynomiallyBounded s) :
    let h := fun m ↦ pairedTableParameters (n m) (s m)
    let d := fun m ↦ 2 * n m - 1
    let B := fun m ↦ (n m + 1) ^ (2 * n m)
    let N := fun m ↦ Nat.card (DegreeMonomial (Fin (2 * n m)) (n m))
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (sliceGridBound (h m) (d m) (B m) (N m))) ∧
      PolynomiallyBounded (fun m ↦ Nat.clog 2 (displacementDegree (h m) (d m) (d m + 1))) := by
  let c := PolynomiallyBounded.const
  let vars := fun m ↦ 2 * n m
  have hv : PolynomiallyBounded vars := (c 2).mul hn
  have hd : PolynomiallyBounded (fun m ↦ 2 * n m - 1) := hv.of_le fun _ ↦ Nat.sub_le ..
  have hB := PolynomiallyBounded.clog_pow (hn.add (c 1)).clog hv
  have hh := pairedTableParameters_polynomial hn hs
  exact ⟨sliceGridBound_clog hh hd hB (hB.of_le fun m ↦ Nat.clog_mono_right _ (card_degreeMonomial_le ..)),
    displacementDegree_clog hh hd (hd.add (c 1))⟩

/-- Combined bit lengths of the two geometric choice thresholds at actual length and gate
budget, before extending the field of constants. -/
noncomputable def pairedChoiceBitBudget (n s : ℕ) : ℕ :=
  let h := pairedTableParameters n s
  let d := 2*n - 1
  Nat.clog 2 (sliceGridBound h d ((n+1)^(2*n)) (Nat.card (DegreeMonomial (Fin (2*n)) n))) +
    Nat.clog 2 (displacementDegree h d (d+1))

/-- One pair of constants works simultaneously for every length and gate budget below
`M`. They are chosen before the circuit, its size, its field, or its characteristic. -/
theorem uniform_paired_choice_bits :
    ∃ A c : ℕ, ∀ M n s : ℕ, n ≤ M → s ≤ M → pairedChoiceBitBudget n s ≤ A*(M+1)^c := by
  let budget (M : ℕ) (u : Fin (M+1) × Fin (M+1)) := pairedChoiceBitBudget u.1.val u.2.val
  have hmax (M : ℕ) := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (budget M)
  choose u _ hu using hmax
  have h₁ := PolynomiallyBounded.id.of_le fun M ↦ Nat.le_of_lt_succ (u M).1.isLt
  have h₂ := PolynomiallyBounded.id.of_le fun M ↦ Nat.le_of_lt_succ (u M).2.isLt
  obtain ⟨hgrid, hdisp⟩ := pairedTable_choice_bits h₁ h₂
  obtain ⟨A, c, hbound⟩ := (hgrid.add hdisp).exists_global_bound
  refine ⟨A, c, fun M n s hn hs ↦ ?_⟩
  let z : Fin (M+1) × Fin (M+1) := (⟨n, Nat.lt_succ_of_le hn⟩, ⟨s, Nat.lt_succ_of_le hs⟩)
  exact (Finset.le_sup (f := budget M) (Finset.mem_univ z)).trans ((hu M) ▸ hbound M)

/-- Both field extensions, and every scalar in the whole advised system of equations, fit
the polynomial-bit budget when the input length and gate budget are at most `M`. -/
theorem pairedTable_field_advice_bits (n s q₀ q₁ q₂ : ℕ → ℕ) (hn : ∀ m, n m ≤ m)
    (hs : ∀ m, s m ≤ m) (hq : PolynomiallyBounded (fun m ↦ Nat.clog 2 (q₀ m)))
    (first : ∀ m, q₁ m ≤ q₀ m * max (sliceGridBound (pairedTableParameters (n m) (s m))
      (2*n m-1) ((n m+1)^(2*n m)) (Nat.card (DegreeMonomial (Fin (2*n m)) (n m)))) 1)
    (second : ∀ m, q₂ m ≤ q₁ m * max (displacementDegree (pairedTableParameters (n m) (s m))
      (2*n m-1) (2*n m-1+1)) 1) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (q₂ m)) ∧
      PolynomiallyBounded (fun m ↦ pairedTableParameters (n m) (s m) *
        (pairedTableParameters (n m) (s m)+3) * Nat.clog 2 (q₂ m)) := by
  have hn' := PolynomiallyBounded.id.of_le hn
  have hs' := PolynomiallyBounded.id.of_le hs
  obtain ⟨h₁, h₂⟩ := pairedTable_choice_bits hn' hs'
  have he := grid_field_card_clog (grid_field_card_clog hq h₁ first) h₂ second
  exact ⟨he, slice_advice_bits (pairedTableParameters_polynomial hn' hs') he⟩

end Branch

end BorderVNP
end Computability
end OAI
