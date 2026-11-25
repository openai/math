import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.BookRaw
import OAI.LinearAlgebra.SpectralBooks.TrivialSlots
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Applying a coefficient sum estimate to a sum of restriction classes

An ordinary sum of classes may initially use any representative of its target.
Transfer the local maps to the diagonal-times-private representative, discard its
zero images, and remove the one-dimensional auxiliary slots. This produces a sum
of actual coefficient tensors in the fixed format of the stretch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace SiteTensor

variable {K : Type*} [Field K] {B C O U : Type} [Fintype B] [Fintype C] [Fintype O] [Fintype U]
  {X : B → Type} {Y : C → Type} [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]

/-- Realize nonzero summands in the chosen book coordinates, including when the
original restriction used all the auxiliary sites. -/
theorem ClassOrdinarySum.in_book_format
    {A : NonzeroProduct.{0} (BookSite B C ⊕ O) K} {L : ℕ} {Z : Fin L → _}
    (hs : ClassOrdinarySum A L Z) (S : Tensor K U (∀ b, X b) (∀ c, Y c))
    (hA : ofRaw (Raw.withTrivial O (bookRaw S)) = classOfProduct A) :
    ∃ N : ℕ, 0 < N ∧ N ≤ L ∧ ∃ T : Fin N → Tensor K U (∀ b, X b) (∀ c, Y c),
      S = ∑ j, T j ∧
      ∀ j, T j ≠ 0 ∧ ∃ l, ofRaw (Raw.withTrivial O (bookRaw (T j))) ≤ classOfProduct (Z l) := by
  let R := Raw.withTrivial O (bookRaw S)
  let e : (∀ i, R.Leg i) ≃ U × (∀ b, X b) × (∀ c, Y c) :=
    (Raw.withTrivialIndex O (bookRaw S)).trans bookCoordinates
  obtain ⟨N, hN, hNL, t, he, ht⟩ := hs.nonzero_in_format R hA
  let T (j : Fin N) (u : U) (x : ∀ b, X b) (y : ∀ c, Y c) := t j (e.symm (u, x, y))
  have hraw (j : Fin N) : Raw.withTrivial O (bookRaw (T j)) = { R with coeff := t j } := by
    have h : (Raw.withTrivial O (bookRaw (T j))).coeff = t j := by
      funext q
      change t j (e.symm (e q)) = t j q
      exact congrArg (t j) (e.symm_apply_apply q)
    exact congrArg (fun f : (∀ i, R.Leg i) → K => { R with coeff := f }) h
  refine ⟨N, hN, hNL, T, ?_, fun j => ?_⟩
  · funext u x y
    have hx := congrFun he (e.symm (u, x, y))
    change S (e (e.symm (u, x, y))).1 (e (e.symm (u, x, y))).2.1 (e (e.symm (u, x, y))).2.2 = _ at hx
    simpa only [e.apply_symm_apply, Finset.sum_apply, T] using hx
  · refine ⟨fun h => (ht j).1 ?_, ?_⟩
    · funext q
      have hq := congrFun (congrFun (congrFun h (e q).1) (e q).2.1) (e q).2.2
      change t j (e.symm (e q)) = 0 at hq
      change t j q = 0
      simpa only [Equiv.symm_apply_apply] using hq
    · rw [hraw]
      exact (ht j).2

/-- Carry a finite coefficient estimate to any ordinary sum in the nonzero class
monoid. The coefficient functional `p` agrees with `h` on the nonzero classes in
this format. The constant `d` is the coefficient of `log₂ L` in the estimate. -/
theorem ClassOrdinarySum.exists_selected_of_book_format
    {A : NonzeroProduct.{0} (BookSite B C ⊕ O) K} {L : ℕ} {Z : Fin L → _}
    (hs : ClassOrdinarySum A L Z) (S : Tensor K U (∀ b, X b) (∀ c, Y c))
    (hA : ofRaw (Raw.withTrivial O (bookRaw S)) = classOfProduct A)
    (h : NonzeroProduct.{0} (BookSite B C ⊕ O) K → ℝ)
    (hmono : ∀ {x y}, classOfProduct x ≤ classOfProduct y → h x ≤ h y)
    (p : Tensor K U (∀ b, X b) (∀ c, Y c) → ℝ)
    (hprice : ∀ T t, ofRaw (Raw.withTrivial O (bookRaw T)) = classOfProduct t → p T = h t)
    {d : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ N : ℕ, 0 < N → ∀ T : Fin N → Tensor K U (∀ b, X b) (∀ c, Y c),
      (∀ j, T j ≠ 0) → S = ∑ j, T j → ∃ j, p S ≤ p (T j) + d * Real.logb 2 N) :
    ∃ l, h A ≤ h (Z l) + d * Real.logb 2 L := by
  obtain ⟨N, hN, hNL, T, hsum, hT⟩ := hs.in_book_format S hA
  obtain ⟨j, hj⟩ := hbound N hN T (fun i => (hT i).1) hsum
  let r := Raw.withTrivial O (bookRaw (T j))
  have hnz : r.coeff ≠ 0 := by
    intro hz
    apply (hT j).1
    funext u x y
    exact congrFun hz ((Raw.withTrivialIndex O (bookRaw (T j))).symm (bookCoordinates.symm (u, x, y)))
  let z : NonzeroProduct.{0} (BookSite B C ⊕ O) K := Additive.ofMul ⟨ofRaw r,
    fun hz => hnz ((ofRaw_eq_zero_iff r).mp hz)⟩
  obtain ⟨l, hl⟩ := (hT j).2
  refine ⟨l, ?_⟩
  rw [hprice S A hA, hprice (T j) z rfl] at hj
  refine hj.trans (add_le_add (hmono (x := z) (y := Z l) hl) (mul_le_mul_of_nonneg_left ?_ hd))
  exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hN) (by exact_mod_cast hNL)

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
