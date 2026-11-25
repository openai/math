import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import OAI.LinearAlgebra.FiniteFourier.RadixFourier

/-! # Layer words for radix-power Fourier transforms

Each Cooley–Tukey stage adds the small transform, one diagonal twiddle and one
permutation for its independent input and output digit orderings.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped Kronecker

variable {K : Type*} [CommRing K] {I J : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- Independent row and column relabelings cost one extra permutation. -/
theorem LayerWord.submatrixEquivs {d : ℕ} {A : Matrix I I K} (hA : LayerWord d A)
    (e f : J ≃ I) : LayerWord (d + 1) (A.submatrix e f) := by
  let P : Matrix J J K := fun i j => if (e.trans f.symm) i = j then 1 else 0
  have hP : LayerMatrix .monomial P := LayerMatrix.monomial (e.trans f.symm) (fun _ => 1)
  have heq : A.submatrix e f = P * A.submatrix f f := by
    ext i j
    rw [Matrix.mul_apply]
    change A (e i) (f j) = ∑ t, (if f.symm (e i) = t then (1 : K) else 0) * A (f t) (f j)
    simp [ite_mul]
  rw [heq, Nat.add_comm d 1]
  exact layerWord_mul (layerWord_of_layer hP) (hA.relabel f.symm)

/-- Sampling every `b`th node preserves separation by units. -/
private theorem separated_pow {a b : ℕ} {q : K} (hb : 0 < b)
    (hsep : Pairwise fun i j : Fin (a*b) => IsUnit (q^i.val - q^j.val)) :
    Pairwise fun i j : Fin a => IsUnit ((q^b)^i.val - (q^b)^j.val) := by
  intro i j hij
  let f (t : Fin a) : Fin (a*b) := ⟨t.val*b, Nat.mul_lt_mul_of_pos_right t.isLt hb⟩
  have hne : f i ≠ f j := by
    intro he
    exact hij (Fin.ext (Nat.eq_of_mul_eq_mul_right hb (congrArg Fin.val he)))
  simpa only [f, ← pow_mul, Nat.mul_comm b] using hsep hne

/-- Cooley–Tukey recursion with unit twiddles and distinct nodes modulo every
maximal ideal. Each stage contributes one twiddle and one digit permutation. -/
theorem layerWord_geometricMatrix_radixPow_of_separated {r C : ℕ} (hr : 0 < r)
    (hsmall : ∀ q : K, q^r = 1 →
      (Pairwise fun i j : Fin r => IsUnit (q^i.val - q^j.val)) →
      LayerWord C (geometricMatrix r q))
    (j : ℕ) {q : K} (hq : q^(r^j) = 1)
    (hs : Pairwise fun i k : Fin (r^j) => IsUnit (q^i.val - q^k.val)) :
    LayerWord ((C + 2) * j) (geometricMatrix (r ^ j) q) := by
  induction j generalizing q with
  | zero =>
    simp only [Nat.mul_zero]
    change geometricMatrix 1 q = 1
    ext i j
    fin_cases i
    fin_cases j
    simp
  | succ j ih =>
    rw [pow_succ] at hq hs ⊢
    have hpos := Nat.mul_pos (pow_pos hr j) hr
    have h₁ := ih (q := q^r) (by rwa [← pow_mul, Nat.mul_comm]) (separated_pow hr hs)
    have hs' : Pairwise fun i k : Fin (r*(r^j)) => IsUnit (q^i.val - q^k.val) := by
      rwa [Nat.mul_comm r]
    have h₂ := hsmall (q^(r^j)) (by rwa [← pow_mul]) (separated_pow (pow_pos hr j) hs')
    have hleft := layerWord_tensor h₁ (layerWord_one (K := K) (I := Fin r) _)
    have hright := layerWord_tensor (layerWord_one (K := K) (I := Fin (r ^ j)) _) h₂
    have htwiddle : LayerWord 1
        (diagonal (fun i : Fin (r ^ j) × Fin r => q ^ (i.1.val * i.2.val))) :=
      layerWord_of_layer (layerMatrix_diagonal_units fun _ => (IsUnit.of_pow_eq_one hq hpos.ne').pow _)
    have h := layerWord_mul (layerWord_mul hleft htwiddle) hright
    rw [← geometricMatrix_radix _ _ q hq] at h
    have hout := h.submatrixEquivs finProdFinEquiv.symm (radixInputIndex _ _).symm
    rw [show (C + 2) * (j + 1) = (C + 2) * j + 1 + C + 1 by ring]
    simpa using hout

/-- Field form of the radix-power recurrence at a primitive root. -/
theorem layerWord_geometricMatrix_radixPow {K : Type*} [Field K] {r C : ℕ} (hr : 0 < r)
    (hsmall : ∀ q : K, IsPrimitiveRoot q r → LayerWord C (geometricMatrix r q))
    (j : ℕ) {q : K} (hq : IsPrimitiveRoot q (r ^ j)) :
    LayerWord ((C + 2) * j) (geometricMatrix (r ^ j) q) := by
  apply layerWord_geometricMatrix_radixPow_of_separated hr _ j hq.pow_eq_one
  · intro i k hik
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun he => hik (Fin.ext (hq.pow_inj i.isLt k.isLt he)))
  · intro z hz hs
    apply hsmall z (IsPrimitiveRoot.mk_of_lt z hr hz ?_)
    intro k hk hkr he
    have h : (⟨k,hkr⟩ : Fin r) ≠ ⟨0,hr⟩ := fun e => hk.ne' (congrArg Fin.val e)
    have hu := hs h
    change IsUnit (z^k - z^0) at hu
    simp [he] at hu

end FiniteFourier
end LinearAlgebra
end OAI
