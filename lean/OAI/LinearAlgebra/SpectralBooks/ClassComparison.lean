import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero
import OAI.LinearAlgebra.SpectralBooks.PriceSelection
import OAI.LinearAlgebra.SpectralBooks.ComparisonExpansion

/-!
# Strict comparison on the nonzero tensor classes

The ground-field comparison theorem is isolated as `StrictSpectralComparison`.
From a restriction to a sum of classes we extract local images in the target's
own format. Distributing powers over the direct sum and retaining its nonzero
images gives the expanded comparison used by the doubling argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor

open scoped BigOperators NNReal Classical

universe v u w

variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K]

/-- Nonzero tensors are closed under tensor product. -/
def nonzeroClasses : Submonoid (TensorClass.{v} I K) where
  carrier := {t | t ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' := mul_ne_zero

/-- Addition denotes tensor product, for taking logarithms of multiplicative prices. -/
abbrev NonzeroProduct := Additive (nonzeroClasses.{v} I K)

variable {I K}

/-- Forget the proof that a tensor class is nonzero. -/
abbrev classOfProduct (x : NonzeroProduct.{v} I K) : TensorClass.{v} I K := x.toMul.val

theorem unit_le_nonzeroClass (x : nonzeroClasses.{v} I K) : 1 ≤ x.val :=
  one_le_of_ne_zero x.property

/-- The normalized base-two log price of an actual ground-field spectral point. -/
abbrev logPoint (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
    NonzeroProduct.{v} I K →+ ℝ := spectralLogHom unit_le_nonzeroClass f

/-- Representatives for an ordinary sum all have the target's local coordinates. -/
def ClassOrdinarySum (X : NonzeroProduct.{v} I K) (L : ℕ) (Z : Fin L → NonzeroProduct.{v} I K) :
    Prop :=
  ∃ (R : Raw.{v} I K) (z : Fin L → (∀ i, R.Leg i) → K),
    ofRaw R = classOfProduct X ∧ R.coeff = ∑ l, z l ∧
    ∀ l, ofRaw { R with coeff := z l } = classOfProduct (Z l)

/-- Move the summands to the local format of a chosen representative of the target.
Each transported summand is a local restriction of its original class. -/
theorem ClassOrdinarySum.in_format {X : NonzeroProduct.{v} I K} {L : ℕ} {Z : Fin L → _}
    (hs : ClassOrdinarySum X L Z) (R : Raw.{v} I K) (hR : ofRaw R = classOfProduct X) :
    ∃ t : Fin L → (∀ i, R.Leg i) → K, R.coeff = ∑ l, t l ∧
      ∀ l, ofRaw { R with coeff := t l } ≤ classOfProduct (Z l) := by
  obtain ⟨U, z, hU, hz, hclass⟩ := hs
  obtain ⟨M, hM⟩ := (ofRaw_le_iff.mp (hR.trans hU.symm).le)
  let t (l : Fin L) (x : ∀ i, R.Leg i) := ∑ a, z l a * ∏ i, M i (x i) (a i)
  refine ⟨t, ?_, fun l => ?_⟩
  · funext x
    rw [hM, hz, Finset.sum_apply]
    simp only [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  · rw [← hclass l]
    exact ⟨M, fun _ => rfl⟩

/-- Transfer a class ordinary sum into a prescribed format and drop precisely
its zero images. This permits the stretch estimate to be applied to its stated
diagonal-times-private-products representative. -/
theorem ClassOrdinarySum.nonzero_in_format {X : NonzeroProduct.{v} I K} {L : ℕ} {Z : Fin L → _}
    (hs : ClassOrdinarySum X L Z) (R : Raw.{v} I K) (hR : ofRaw R = classOfProduct X) :
    ∃ N : ℕ, 0 < N ∧ N ≤ L ∧ ∃ t : Fin N → (∀ i, R.Leg i) → K,
      R.coeff = ∑ j, t j ∧
      ∀ j, t j ≠ 0 ∧ ∃ l, ofRaw { R with coeff := t j } ≤ classOfProduct (Z l) := by
  obtain ⟨z, hsum, hle⟩ := hs.in_format R hR
  have hn : R.coeff ≠ 0 := fun h => X.toMul.property (hR.symm.trans ((ofRaw_eq_zero_iff _).mpr h))
  obtain ⟨N, hN, hcount, idx, hnz, heq⟩ := ComparisonExpansion.nonzero_terms_of_sum hn z hsum
  exact ⟨N, hN, hcount.trans_eq (Fintype.card_fin L), z ∘ idx, heq,
    fun j => ⟨hnz j, idx j, hle _⟩⟩

/-- The strict comparison assertion of Proposition 2.1, without any expansion
or finite-family cost information built into it. -/
def StrictSpectralComparison (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K] : Prop :=
  ∀ X Y : TensorClass.{v} I K, X ≠ 0 → Y ≠ 0 →
    (∀ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop), f.val X < f.val Y) →
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → X ^ n ≤ C • (Y ^ n)

omit [Nonempty I] in
private theorem split_add (R : Raw.{v} I K) (Y V : TensorClass.{v} I K)
    (h : ofRaw R ≤ Y + V) :
    ∃ A B : (∀ i, R.Leg i) → K, R.coeff = A + B ∧
      ofRaw { R with coeff := A } ≤ Y ∧ ofRaw { R with coeff := B } ≤ V := by
  induction Y using Quotient.inductionOn with | h Y =>
  induction V using Quotient.inductionOn with | h V =>
  obtain ⟨M, hM⟩ := h
  let image {B : I → Type v} [∀ i, Fintype (B i)] (T : (∀ i, B i) → K)
      (N : ∀ i, R.Leg i → B i → K) (x : ∀ i, R.Leg i) := ∑ a, T a * ∏ i, N i (x i) (a i)
  let left := fun i x a => M i x (Sum.inl a)
  let right := fun i x a => M i x (Sum.inr a)
  refine ⟨image Y.coeff left, image V.coeff right, ?_, ⟨left, fun _ => rfl⟩, ⟨right, fun _ => rfl⟩⟩
  funext x
  have hh := hM x
  change R.coeff x = ∑ a, sumCoeff Y.coeff V.coeff a * ∏ i, M i (x i) (a i) at hh
  simpa [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul, image, left, right] using hh

/-- A restriction to a finite direct sum gives an ordinary sum in *any given*
representative of the target, with one local image for each source class. -/
theorem images_of_le_sum {J : Type*} [Fintype J] (R : Raw.{v} I K)
    (Y : J → TensorClass.{v} I K) (h : ofRaw R ≤ ∑ j, Y j) :
    ∃ Z : J → (∀ i, R.Leg i) → K, R.coeff = ∑ j, Z j ∧
      ∀ j, ofRaw { R with coeff := Z j } ≤ Y j := by
  have aux (s : Finset J) (x : (∀ i, R.Leg i) → K)
      (hx : ofRaw { R with coeff := x } ≤ ∑ j ∈ s, Y j) :
      ∃ Z : J → (∀ i, R.Leg i) → K, x = ∑ j ∈ s, Z j ∧
        ∀ j ∈ s, ofRaw { R with coeff := Z j } ≤ Y j := by
    induction s using Finset.induction_on generalizing x with
    | empty =>
      have hx' : ofRaw { R with coeff := x } = 0 :=
        le_antisymm (by simpa using hx) (zero_le_tensor _)
      exact ⟨0, by simpa using (ofRaw_eq_zero_iff _).mp hx', by simp⟩
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj] at hx
      obtain ⟨a, b, heq, ha, hb⟩ := split_add {R with coeff := x} _ _ hx
      obtain ⟨Z, hZ, hle⟩ := ih b hb
      refine ⟨Function.update Z j a, ?_, ?_⟩
      · rw [Finset.sum_insert hj, Function.update_self]
        rw [show ∑ l ∈ s, Function.update Z j a l = ∑ l ∈ s, Z l from
          Finset.sum_congr rfl fun l hl => Function.update_of_ne (show l ≠ j from fun h => hj (h ▸ hl)) ..]
        exact heq.trans (congrArg (a + ·) hZ)
      · intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hs
        · simpa using ha
        · simpa [Function.update_of_ne (show l ≠ j from fun e => hj (e ▸ hs))] using hle l hs
  obtain ⟨Z, hsum, hle⟩ := aux Finset.univ R.coeff h
  exact ⟨Z, hsum, fun j => hle j (Finset.mem_univ _)⟩

/-- On the concrete tensor semiring, strict comparison for two classes suffices
for the expansion with a bounded number of nonzero ordinary summands. -/
theorem expandedStrictComparison_of_strict (strict : StrictSpectralComparison.{v} I K) :
    ExpandedStrictComparison (Set.range (logPoint.{v} (I := I) (K := K)))
      (fun x y => classOfProduct x ≤ classOfProduct y) ClassOrdinarySum := by
  intro J X Y hJ hlog
  let y := fun i => classOfProduct (Y i)
  have summand_le (j : Fin J) : y j ≤ ∑ i, y i := by
    rw [← Finset.sum_erase_add Finset.univ y (Finset.mem_univ j)]
    simpa using add_mono (zero_le_tensor (∑ i ∈ Finset.univ.erase j, y i)) (le_refl (y j))
  have hnonzero : ∑ i, y i ≠ 0 := by
    let j : Fin J := ⟨0, hJ⟩
    intro hz
    exact (Y j).toMul.property (le_antisymm ((summand_le j).trans_eq hz) (zero_le_tensor _))
  have greater (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
      f.val (classOfProduct X) < f.val (∑ i, y i) := by
    obtain ⟨i, hi⟩ := hlog (logPoint f) ⟨f, rfl⟩
    apply lt_of_lt_of_le _ (f.property.2.2.2.2 _ _ (summand_le i))
    by_contra! hh
    apply hi.not_ge
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_spectral_value f (unit_le_nonzeroClass (Y i).toMul))
    · exact_mod_cast hh
  obtain ⟨C, hC, hx⟩ := strict _ _ X.toMul.property hnonzero greater
  refine ⟨C, hC, fun n hn => ?_⟩
  let P := Fin C × (Fin n → Fin J)
  let W (p : P) := ∑ t, Y (p.2 t)
  have prod (w : Fin n → Fin J) : classOfProduct (∑ t, Y (w t)) = ∏ t, y (w t) := by
    simp [classOfProduct, toMul_sum, y]
  have distrib : C • (∑ j, y j)^n = ∑ p : P, classOfProduct (W p) := by
    change _ = ∑ p : Fin C × (Fin n → Fin J), classOfProduct (∑ t, Y (p.2 t))
    rw [Fintype.sum_prod_type]
    simp only [prod, ← Fintype.prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const]
  obtain ⟨R, hR⟩ := Quotient.exists_rep (classOfProduct (n • X))
  change ofRaw R = classOfProduct (n • X) at hR
  have hr : ofRaw R ≤ ∑ p : P, classOfProduct (W p) := by
    rw [hR, ← distrib]
    simpa [classOfProduct, y] using hx n hn
  obtain ⟨z, hsum, hle⟩ := images_of_le_sum R _ hr
  have hnz : R.coeff ≠ 0 := fun heq => (n • X).toMul.property
    (hR.symm.trans ((ofRaw_eq_zero_iff _).mpr heq))
  obtain ⟨L, hL, hcount, idx, hnz', heq⟩ := ComparisonExpansion.nonzero_terms_of_sum hnz z hsum
  let images (l : Fin L) : NonzeroProduct.{v} I K :=
    Additive.ofMul ⟨ofRaw { R with coeff := z (idx l) },
      fun h => hnz' l ((ofRaw_eq_zero_iff _).mp h)⟩
  exact ⟨L, hL, hcount.trans_eq (by simp [P]), images,
    ⟨R, z ∘ idx, hR, heq, fun _ => rfl⟩, fun l => ⟨(idx l).2, hle _⟩⟩

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
