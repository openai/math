import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # Rank of the outer label matrix

In each monomial of the outer Hamming-distance polynomial, the coordinates used
by the monomial retain their row indices. Every other coordinate uses the inner
matrix factorization. This gives a factorization of each monomial even when
coordinates occur repeatedly in it. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

open scoped BigOperators

private abbrev PatchFeature (U S : Type*) {h : ℕ} (d : Finset (Fin h)) :=
  (d → U) × ({i : Fin h // i ∉ d} → S)

private theorem patch_factor {U S F : Type*} [Field F] [Fintype S] [Fintype U]
    [DecidableEq U] {h : ℕ} (d : Finset (Fin h))
    (A : Matrix U S F) (B : Matrix S U F)
    (g : (d → U) → (Fin h → U) → F) :
    ∃ (L : Matrix (Fin h → U) (PatchFeature U S d) F)
      (R : Matrix (PatchFeature U S d) (Fin h → U) F),
      ∀ v w, (L * R) v w =
        g (fun i => v i) w * ∏ i, (A * B) (v i) (w i) := by
  classical
  let l : Matrix (Fin h → U) (PatchFeature U S d) F := fun v z =>
    if z.1 = (fun i : d => v i) then ∏ i : {i : Fin h // i ∉ d}, A (v i) (z.2 i) else 0
  let r : Matrix (PatchFeature U S d) (Fin h → U) F := fun z w =>
    (g z.1 w * ∏ i : d, (A * B) (z.1 i) (w i)) *
      ∏ i : {i : Fin h // i ∉ d}, B (z.2 i) (w i)
  refine ⟨l, r, fun v w => ?_⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [l, r, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs =>
    enter [2, z]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_sum, ← Fintype.prod_sum
    (fun (i : {i : Fin h // i ∉ d}) (j : S) => A (v i) j * B j (w i)), mul_assoc]
  congr 1
  rw [show Finset.Subtype.fintype d = Subtype.fintype (fun i => i ∈ d) from Subsingleton.elim _ _]
  exact Fintype.prod_subtype_mul_prod_subtype (· ∈ d) (fun i => (A * B) (v i) (w i))

private theorem patch_card {U S : Type*} [Fintype U] [Fintype S]
    {h t : ℕ} (d : Finset (Fin h)) (hd : d.card ≤ t) (ht : t ≤ h)
    (hs : Fintype.card S ≤ Fintype.card U) :
    Fintype.card (PatchFeature U S d) ≤ Fintype.card S ^ (h-t) * Fintype.card U ^ t := by
  classical
  let c := Fintype.card S
  let n := Fintype.card U
  have hdiff : Fintype.card {i : Fin h // i ∉ d} = h - d.card := by
    simp [Fintype.card_subtype_compl]
  simp only [PatchFeature, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, hdiff]
  change n ^ d.card * c ^ (h - d.card) ≤ c ^ (h-t) * n ^ t
  rw [show h - d.card = (h-t)+(t-d.card) by omega, pow_add]
  calc
    n ^ d.card * (c ^ (h-t) * c ^ (t-d.card)) ≤
        n ^ d.card * (c ^ (h-t) * n ^ (t-d.card)) := by gcongr
    _ = c ^ (h-t) * n ^ t := by
      rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le hd]

/-- The outer kernel prior to specializing the field and the word alphabet. -/
def outerLabelMatrix {U F : Type*} [Field F] [DecidableEq U]
    (K : Matrix U U F) (h t : ℕ) : Matrix (Fin h → U) (Fin h → U) F :=
  fun v w => (1 - (∑ i, if v i ≠ w i then (1 : F) else 0) ^ t) * ∏ i, K (v i) (w i)

private def patchSupport {h t : ℕ} : Option (Fin t → Fin h) → Finset (Fin h)
  | none => ∅
  | some u => Finset.univ.image u

private def patchWeight {U F : Type*} [Field F] [DecidableEq U] {h t : ℕ} :
    (a : Option (Fin t → Fin h)) → (patchSupport a → U) → (Fin h → U) → F
  | none, _, _ => 1
  | some u, z, w => -(∏ j : Fin t,
    if z ⟨u j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩ ≠ w (u j) then 1 else 0)

/-- Tensor the inner factorization over all outer coordinates, suppressing its
rank saving only at the coordinates tested by a monomial. -/
theorem outerLabelMatrix_rank_le {U S F : Type*} [Field F] [Fintype S] [Fintype U]
    [DecidableEq U] (A : Matrix U S F) (B : Matrix S U F) {h t : ℕ} (ht : t ≤ h)
    (hs : Fintype.card S ≤ Fintype.card U) :
    (outerLabelMatrix (A * B) h t).rank ≤
      (1 + h^t) * (Fintype.card S ^ (h-t) * Fintype.card U ^ t) := by
  classical
  let Terms := Option (Fin t → Fin h)
  let Features (a : Terms) := PatchFeature U S (patchSupport a)
  have hf (a : Terms) := patch_factor (patchSupport a) A B (patchWeight a)
  choose L R hLR using hf
  let left : Matrix (Fin h → U) (Sigma Features) F := fun v z => L z.1 v z.2
  let right : Matrix (Sigma Features) (Fin h → U) F := fun z w => R z.1 z.2 w
  have heq : outerLabelMatrix (A * B) h t = left * right := by
    ext v w
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    change _ = ∑ a : Terms, (L a * R a) v w
    simp_rw [hLR]
    rw [← Finset.sum_mul, Fintype.sum_option]
    simp [outerLabelMatrix, patchWeight, Fintype.sum_pow, sub_eq_add_neg]
  rw [heq]
  apply ((Matrix.rank_mul_le_left left right).trans left.rank_le_card_width).trans
  rw [Fintype.card_sigma]
  have hcard (a : Terms) : Fintype.card (Features a) ≤
      Fintype.card S ^ (h-t) * Fintype.card U ^ t := by
    apply patch_card _ _ ht hs
    cases a with
    | none => simp [patchSupport]
    | some u => simpa [patchSupport] using (Finset.card_image_le (s := Finset.univ) (f := u))
  calc
    _ ≤ ∑ _a : Terms, Fintype.card S ^ (h-t) * Fintype.card U ^ t :=
      Finset.sum_le_sum fun a _ => hcard a
    _ = _ := by simp [Terms, Nat.add_comm]

end NearSquareRoot
end Computability
end OAI
