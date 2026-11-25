import OAI.LinearAlgebra.SpectralBooks.StretchOrdinary
import OAI.LinearAlgebra.SpectralBooks.SitePriceEval.StretchWordPrice
import OAI.LinearAlgebra.SpectralBooks.StretchCollapse
import OAI.LinearAlgebra.SpectralBooks.PermutationStretch.StretchDiagonals

/-! # Permutation stretch at two collapsed placements

All diagonal values here are evaluations on binary diagonals. Their powers, the
zero cost of a fully collapsed private tensor, and the target increment are
consequences of product additivity and the grouped-site local maps.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators Classical
open MatrixMultiplication.Foundation

section
open PermutationStretch

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]

/-- Lemma `stretch` for finite site coefficients. Its price operations are
restriction monotonicity, nonzero product additivity, and the ordinary-sum
estimate at the two binary diagonal prices. -/
theorem permutationStretch_of_collapses {R L : ℕ} (hR : 0 < R) (hL : 0 < L)
    {lam : ℝ} (hlam : 0 ≤ lam) (a b c : SitePriceEval K B C)
    (ha : a.BinaryProductAdditive) (hb : b.BinaryProductAdditive) (hc : c.BinaryProductAdditive)
    (haSum : a.OrdinarySumBound (a.value (diagAll (K := K) B C (Fin 2))))
    (hcSum : c.OrdinarySumBound (c.value (diagAll (K := K) B C (Fin 2))))
    (hbc : b.MonoGroupedC) (hcb : c.MonoGroupedB) (hagB : b.AgreesB a) (hagC : c.AgreesC a)
    (hD : a.value (diagAll (K := K) B C (Fin 2)) = a.value (diagB (K := K) B C (Fin 2)))
    {U V : Type} {X : B → Type} {Y : C → Type} [Fintype U] [Fintype V]
    [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (P : U → (∀ b, X b) → K) (Q : V → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (T : Fin L → Tensor K (Fin R × U × V) (∀ b, Fin R × X b) (∀ c, Fin R × Y c))
    (hT : ∀ l, T l ≠ 0) (hsum : sharedTarget (R := Fin R) P Q = ∑ l, T l) :
    let S := sharedTarget (R := Fin R) P Q
    let D := a.value (diagAll (K := K) B C (Fin 2))
    let E := a.value (diagC (K := K) B C (Fin 2))
    ∃ l, lam * a.value S + (b.value S + c.value S) ≤
      lam * a.value (T l) + (b.value (T l) + c.value (T l)) + ((lam + 1) * D + E) * Real.logb 2 L := by
  let : Nonempty (Fin R) := ⟨⟨0,hR⟩⟩
  have diagNZ {I W : Type} [Nonempty W] : diagonalCoeff (K := K) (B := I) (W := W) ≠ 0 := by
    intro hz
    let w := Classical.arbitrary W
    simpa [diagonalCoeff] using congrFun (congrFun hz w) (fun _ => w)
  have bdiag (W : Type) [Fintype W] [Nonempty W] :
      b.value (diagAll (K := K) B C W) = a.value (diagB (K := K) B C W) :=
    (hbc.value_diagAll_eq_diagB W).trans (hagB _ diagNZ)
  have cdiag (W : Type) [Fintype W] [Nonempty W] :
      c.value (diagAll (K := K) B C W) = a.value (diagC (K := K) B C W) :=
    (hcb.value_diagAll_eq_diagC W).trans (hagC _ diagNZ)
  rw [cdiag (Fin 2)] at hcSum
  apply permutationStretch_ordinary_sum hR hL hlam (value_diagC_two_nonneg a ha) a b c ha
    (a.wordProductAdditive_of_binaryProductAdditive ha) (b.wordProductAdditive_of_binaryProductAdditive hb)
    (c.wordProductAdditive_of_binaryProductAdditive hc) haSum hcSum hbc hcb hagB hagC
    (fun W _ _ => hD ▸ value_diagB_eq_logb a ha W) (fun W _ _ => value_diagC_eq_logb a ha W)
    (by simpa only [Fintype.card_fin] using value_diagAll_eq_logb a ha (Fin R)) P Q hP hQ T hT hsum
  simpa only [Fintype.card_fin] using sharedTarget_increment (R := Fin R) a b c ha hb hc P Q hP hQ
    (value_diagAll_eq_logb a ha (Fin R))
    ((bdiag (Fin R)).trans (hD ▸ value_diagB_eq_logb a ha (Fin R)))
    ((cdiag (Fin R)).trans (value_diagC_eq_logb a ha (Fin R))) (hagB P hP)
    (hbc.value_placeC_eq_zero hb Q hQ) (hcb.value_placeB_eq_zero hc P hP) (hagC Q hQ)

end

end SpectralBooks
end LinearAlgebra
end OAI
