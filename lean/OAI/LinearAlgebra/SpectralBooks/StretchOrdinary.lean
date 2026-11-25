import OAI.LinearAlgebra.SpectralBooks.StretchSelection
import OAI.LinearAlgebra.SpectralBooks.StretchLimit
import OAI.LinearAlgebra.SpectralBooks.StretchDiagonalControl
import OAI.LinearAlgebra.SpectralBooks.SlicePrice

/-! # The ordinary-sum estimate for a diagonal times two private tensors

This combines the independent-diagonal restriction with the ordinary-sum expansion
and the two bounds on the same tagged word. Balanced-word covers yield the base-two
loss `((λ + 1)D + E) log₂ L` after division by the tensor-power length.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

section
open PermutationStretch PermutationControl

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]

/-- Agreement on all nonzero tensors private to the common site and `B`. -/
def SitePriceEval.AgreesB (p q : SitePriceEval K B C) : Prop :=
  ∀ {U : Type} {X : B → Type} [Fintype U] [∀ b, Fintype (X b)] (T : U → (∀ b, X b) → K),
    T ≠ 0 → p.value (placeB C T) = q.value (placeB C T)

/-- Agreement on all nonzero tensors private to the common site and `C`. -/
def SitePriceEval.AgreesC (p q : SitePriceEval K B C) : Prop :=
  ∀ {U : Type} {Y : C → Type} [Fintype U] [∀ c, Fintype (Y c)] (T : U → (∀ c, Y c) → K),
    T ≠ 0 → p.value (placeC B T) = q.value (placeC B T)

private theorem private_slice_le (a b c : SitePriceEval K B C) (ha : a.BinaryProductAdditive)
    (hb : b.MonoGroupedC) (hc : c.MonoGroupedB) (hagB : b.AgreesB a) (hagC : c.AgreesC a)
    {U : Type} {X : B → Type} {Y : C → Type} [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)) (h : T ≠ 0) : a.value T ≤ b.value T + c.value T := by
  apply collapsed_slice_price_le a b c ha hb hc T h
  · apply (hagB (fun (p : U × (∀ c, Y c)) x => T p.1 x p.2) ?_).symm
    exact fun hz => h (funext fun u => funext fun x => funext fun y => congrFun (congrFun hz (u,y)) x)
  · apply (hagC (fun (p : U × (∀ b, X b)) y => T p.1 p.2 y) ?_).symm
    exact fun hz => h (funext fun u => funext fun x => funext fun y => congrFun (congrFun hz (u,x)) y)

/-- The permutation-stretch estimate expressed in terms of the product, sum,
collapse, private agreement, and diagonal evaluations of actual site prices. -/
theorem permutationStretch_ordinary_sum {R L : ℕ} (hR : 0 < R) (hL : 0 < L)
    {lam D E : ℝ} (hlam : 0 ≤ lam) (hE : 0 ≤ E)
    (a b c : SitePriceEval K B C) (ha : a.BinaryProductAdditive)
    (hwordA : a.WordProductAdditive) (hwordB : b.WordProductAdditive) (hwordC : c.WordProductAdditive)
    (hsumA : a.OrdinarySumBound D) (hsumC : c.OrdinarySumBound E)
    (hb : b.MonoGroupedC) (hc : c.MonoGroupedB) (hagB : b.AgreesB a) (hagC : c.AgreesC a)
    (hdiagB : ∀ (W : Type) [Fintype W] [Nonempty W],
      a.value (diagB (K := K) B C W) = D * Real.logb 2 (Fintype.card W))
    (hdiagC : ∀ (W : Type) [Fintype W] [Nonempty W],
      a.value (diagC (K := K) B C W) = E * Real.logb 2 (Fintype.card W))
    (hdiag : a.value (diagAll (K := K) B C (Fin R)) = D * Real.logb 2 R)
    {U V : Type} {X : B → Type} {Y : C → Type} [Fintype U] [Fintype V]
    [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (P : U → (∀ b, X b) → K) (Q : V → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (T : Fin L → Tensor K (Fin R × U × V) (∀ b, Fin R × X b) (∀ c, Fin R × Y c))
    (hT : ∀ l, T l ≠ 0)
    (hsum : sharedTarget (R := Fin R) P Q = ∑ l, T l)
    (hinc : let S := sharedTarget (R := Fin R) P Q
      b.value S + c.value S = a.value S + E * Real.logb 2 R) :
    let S := sharedTarget (R := Fin R) P Q
    ∃ l, lam * a.value S + (b.value S + c.value S) ≤
      lam * a.value (T l) + (b.value (T l) + c.value (T l)) + ((lam + 1) * D + E) * Real.logb 2 L := by
  let : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  apply permutationStretch_sum_bound_of_covers hR hL hlam (fun l => a.value (T l))
    (fun l => b.value (T l) + c.value (T l)) hinc
  intro k _ tags htags
  let W := BalancedWords R k
  have hw : 0 < Fintype.card W := Nat.pos_of_mul_pos_right
    ((card_balancedWords_mul_factorial R k) ▸ Nat.factorial_pos _)
  let nw : Nonempty W := Fintype.card_pos_iff.mp hw
  let word : W ↪ (Fin (R * k) → Fin R) := ⟨Subtype.val, Subtype.val_injective⟩
  let perm : tags → Equiv.Perm (Fin (R * k)) := Subtype.val
  have cover (i j : W) : ∃ t : tags, word j ∘ perm t = word i := by
    obtain ⟨t, ht, he⟩ := htags i j
    exact ⟨⟨t, ht⟩, he⟩
  let : Nonempty tags := (cover nw.some nw.some).elim (fun t _ => ⟨t⟩)
  have he w u v x y := congrFun (congrFun (congrFun hsum (w, u, v)) x) y
  obtain ⟨s, z, hlow, hua, hubc⟩ := exists_stretch_word a b c hsumA
    (a.diagonalControlBound_of_product ha hE hdiagC) hb hc hsumC word perm cover P Q T
    (fun w u v x y => by simpa [sharedTarget, Finset.sum_apply] using he w u v x y)
    (fun s => private_slice_le a b c ha hb hc hagB hagC _
      (tagged_permutations_ne_zero perm _ (wordProduct_ne_zero T hT s)))
  have hlowval := value_independent_eq_sharedTarget_sub (R := Fin R) (M := Fin (R * k)) (W := W)
    a ha hwordA P Q hP hQ (by simpa using hdiag) (hdiagB W) (hdiagC W)
  rw [hlowval] at hlow
  refine ⟨s, z, ?_, ?_, ?_⟩
  · simpa only [W, Fintype.card_fin, Nat.cast_mul] using hlow
  · simpa only [hwordA T hT, Fintype.card_coe] using hua
  · simpa only [hwordB T hT, hwordC T hT, Finset.sum_add_distrib, Fintype.card_fin,
      Nat.cast_mul] using hubc

end

end SpectralBooks
end LinearAlgebra
end OAI
