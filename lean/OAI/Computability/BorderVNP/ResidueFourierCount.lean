import OAI.Computability.BorderVNP.ResidueFourierEntry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finset.Card

/-!
# Binary counting of an interpolation entry

Section 10.2 sums over canonical encodings of field elements. Invalid encodings and
zero field elements are rejected. After a prime-field linear coordinate projection,
the final binary guess realizes a prime-field weight by that many accepting paths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open ResidueBox
open scoped BigOperators Classical

variable {ι σ E K : Type*} [Fintype ι] [Fintype σ] [Field E] [Field K] [Fintype K]

/-- The local field expression contributed by a valid tuple to the coefficient reader. -/
noncomputable def pathSummand (φ : E →+* K) (q : ℕ) (g : ι → MvPolynomial (Option σ) E)
    (a b : E) (e μ k : Exponent σ) (x : Option σ → Kˣ) : K :=
  let j := sourceIndex q (k - μ)
  if inShiftedBox e j ((q - 1) * ∑ t, (g t).totalDegree) then
    (φ a * ((Fintype.card Kˣ : K) ^ Fintype.card (Option σ))⁻¹) *
      ((φ b * monomialValue x e * ∏ t, MvPolynomial.eval₂ φ (fun i => (x i : K)) (g t) ^
        (q - 1)) * monomialValue x (-j))
  else 0

/-- The sum of the local field expressions is the embedded row coefficient. -/
theorem entry_eq_pathSum (φ : E →+* K) (q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (a b : E) (e μ k : Exponent σ)
    (hwidth : (q - 1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ) :
    φ ((rowPolynomial q hq g (RingHom.id E) a b e μ).coeff k) =
      ∑ x : Option σ → Kˣ, pathSummand φ q g a b e μ k x := by
  rw [entry_on_grid φ q hq g a b e μ k hwidth]
  by_cases h : inShiftedBox e (sourceIndex q (k - μ)) ((q - 1) * ∑ t, (g t).totalDegree)
  · simp only [pathSummand, h, ite_true, ← Finset.mul_sum, mul_assoc]
  · simp [pathSummand, h]

/-- A binary field word has just enough bits to represent all field elements. -/
abbrev FieldWord (K : Type*) [Fintype K] := Fin (2 ^ Nat.clog 2 (Fintype.card K))

/-- Decode a canonical field word. Out-of-range words decode to zero, which the
multiplicative-grid test rejects. -/
def decodeWord (enc : K ≃ Fin (Fintype.card K)) (w : FieldWord K) : K :=
  if h : w.val < Fintype.card K then enc.symm ⟨w.val, h⟩ else 0

private def encodeUnit (enc : K ≃ Fin (Fintype.card K)) (x : Kˣ) : FieldWord K :=
  (enc x.val).castLE (Nat.le_pow_clog (by decide) _)

private theorem decode_encode (enc : K ≃ Fin (Fintype.card K)) (x : Kˣ) :
    decodeWord enc (encodeUnit enc x) = x.val := by
  simp [decodeWord, encodeUnit]

private theorem encode_decode (enc : K ≃ Fin (Fintype.card K)) (w : FieldWord K)
    (h : decodeWord enc w ≠ 0) : encodeUnit enc (Units.mk0 _ h) = w := by
  have hlt : w.val < Fintype.card K := by
    by_contra hlt
    exact h (by simp [decodeWord, hlt])
  apply Fin.ext
  simp [encodeUnit, decodeWord, hlt]

private def encodeGrid (enc : K ≃ Fin (Fintype.card K)) : (ι → Kˣ) ↪ (ι → FieldWord K) where
  toFun x i := encodeUnit enc (x i)
  inj' := by
    intro x y he
    funext i
    apply Units.ext
    simpa only [decode_encode] using congrArg (decodeWord enc) (congrFun he i)

/-- Extend the grid summand by zero to all tuples of binary words. -/
def wordValue {R : Type*} [Zero R] (enc : K ≃ Fin (Fintype.card K))
    (f : (ι → Kˣ) → R) (w : ι → FieldWord K) : R :=
  let _ : DecidableEq K := enc.decidableEq
  let _ : Decidable (∀ i, decodeWord enc (w i) ≠ 0) := Fintype.decidableForallFintype
  if h : ∀ i, decodeWord enc (w i) ≠ 0 then f (fun i => Units.mk0 _ (h i)) else 0

/-- Rejection of invalid or zero entries leaves each multiplicative-grid tuple exactly once. -/
theorem sum_wordValue {R : Type*} [AddCommMonoid R] (enc : K ≃ Fin (Fintype.card K))
    (f : (ι → Kˣ) → R) :
    ∑ w : ι → FieldWord K, wordValue enc f w = ∑ x : ι → Kˣ, f x := by
  classical
  let c := encodeGrid (ι := ι) enc
  have henc (x : ι → Kˣ) : wordValue enc f (c x) = f x := by
    have h (i : ι) : decodeWord enc (c x i) ≠ 0 := by
      change decodeWord enc (encodeUnit enc (x i)) ≠ 0
      rw [decode_encode]
      exact (x i).ne_zero
    rw [wordValue, dite_eq_left h]
    congr 1
    funext i
    apply Units.ext
    exact decode_encode enc (x i)
  calc
    _ = ∑ w ∈ Finset.univ.map c, wordValue enc f w := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro w _ hw
      have hn : ¬∀ i, decodeWord enc (w i) ≠ 0 := by
        intro h
        apply hw
        refine Finset.mem_map.mpr ⟨fun i => Units.mk0 _ (h i), Finset.mem_univ _, ?_⟩
        funext i
        exact encode_decode enc (w i) (h i)
      simp [wordValue, hn]
    _ = _ := by simp only [Finset.sum_map, henc]

/-- The final word guess realizes an arbitrary prime-field element by Boolean outputs. -/
theorem count_prime_weight (p : ℕ) [Fact p.Prime] (v : ZMod p) :
    (∑ y : Fin (2 ^ Nat.clog 2 p), if y.val < v.val then (1 : ZMod p) else 0) = v := by
  rw [Finset.sum_boole, ← Fintype.card_subtype (fun y : Fin (2 ^ Nat.clog 2 p) => y.val < v.val),
    Fintype.card_fin_lt_of_le ((ZMod.val_lt v).le.trans (Nat.le_pow_clog (by decide) _)),
    ZMod.natCast_zmod_val]

omit [Fintype K] in
/-- Each base-field coordinate extends to a prime-field linear map on the grid field. -/
theorem exists_coordinate_extension (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) E] [Algebra (ZMod p) K] (φ : E →ₐ[ZMod p] K)
    (π : E →ₗ[ZMod p] ZMod p) :
    ∃ π' : K →ₗ[ZMod p] ZMod p, π'.comp φ.toLinearMap = π := by
  obtain ⟨r, hr⟩ := φ.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr φ.injective)
  refine ⟨π.comp r, ?_⟩
  rw [LinearMap.comp_assoc, hr, LinearMap.comp_id]

/-- The specified prime-field coordinate of (10.3) is the sum of the actual zero/one
outputs, using one binary word per field coordinate and one for the final threshold test. -/
theorem entry_binary_count (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) K]
    (φ : E →ₐ[ZMod p] K) (π : E →ₗ[ZMod p] ZMod p) (enc : K ≃ Fin (Fintype.card K)) :
    ∃ π' : K →ₗ[ZMod p] ZMod p, π'.comp φ.toLinearMap = π ∧
      ∀ (q : ℕ) (hq : 0 < q) (g : ι → MvPolynomial (Option σ) E)
        (a b : E) (e μ k : Exponent σ),
        (q - 1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ →
        π ((rowPolynomial q hq g (RingHom.id E) a b e μ).coeff k) =
          ∑ w : Option σ → FieldWord K, ∑ y : Fin (2 ^ Nat.clog 2 p),
            if y.val < (wordValue enc (fun x => π' (pathSummand φ q g a b e μ k x)) w).val
            then 1 else 0 := by
  obtain ⟨π', hπ⟩ := exists_coordinate_extension p φ π
  refine ⟨π', hπ, ?_⟩
  intro q hq g a b e μ k hwidth
  simp_rw [count_prime_weight]
  rw [← hπ, LinearMap.comp_apply]
  change π' (φ.toRingHom _) = _
  rw [entry_eq_pathSum φ.toRingHom q hq g a b e μ k hwidth, map_sum]
  convert! (sum_wordValue enc (fun x => π' (pathSummand φ q g a b e μ k x))).symm using 1 <;>
    apply Finset.sum_congr (Finset.ext fun _ => by simp) <;> intros <;> rfl

end ResidueFourier

end BorderVNP
end Computability
end OAI
