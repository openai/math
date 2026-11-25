import OAI.LinearAlgebra.SpectralBooks.StretchPrice
import OAI.LinearAlgebra.SpectralBooks.PermutationControl
import Mathlib.Tactic

/-! # Pricing the independent diagonals

The common target and the restriction produced by the permutation stretch factor
into private tensors and diagonals. All changes in the order of coordinates
take place separately at each original site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical BigOperators

section

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]

namespace SitePriceEval

/-- Sitewise tensor product in the common-site/two-family coordinates. -/
def splitProduct {U V : Type} {X X' : B → Type} {Y Y' : C → Type}
    (A : Tensor K U (∀ b, X b) (∀ c, Y c)) (S : Tensor K V (∀ b, X' b) (∀ c, Y' c)) :
    Tensor K (U × V) (∀ b, X b × X' b) (∀ c, Y c × Y' c) :=
  fun u x y => A u.1 (fun b => (x b).1) (fun c => (y c).1) *
    S u.2 (fun b => (x b).2) (fun c => (y c).2)

/-- Additivity of log price on binary products of nonzero tensors. -/
def BinaryProductAdditive (p : SitePriceEval K B C) : Prop :=
  ∀ {U V : Type} {X X' : B → Type} {Y Y' : C → Type} [Fintype U] [Fintype V]
    [∀ b, Fintype (X b)] [∀ b, Fintype (X' b)] [∀ c, Fintype (Y c)] [∀ c, Fintype (Y' c)]
    (A : Tensor K U (∀ b, X b) (∀ c, Y c)) (S : Tensor K V (∀ b, X' b) (∀ c, Y' c)),
    A ≠ 0 → S ≠ 0 → p.value (splitProduct A S) = p.value A + p.value S

/-- Finite product additivity in the power coordinates used for product words. -/
def WordProductAdditive (p : SitePriceEval K B C) : Prop :=
  ∀ {J L U : Type} {X : B → Type} {Y : C → Type} [Fintype J] [DecidableEq J] [Fintype U]
    [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : L → Tensor K U (∀ b, X b) (∀ c, Y c)), (∀ l, T l ≠ 0) → ∀ s : J → L,
    p.value (PermutationControl.wordProduct T s) = ∑ j, p.value (T (s j))

/-- A change of basis labels separately at every site preserves any monotone price. -/
theorem value_reindex (p : SitePriceEval K B C)
    {U V : Type} {X X' : B → Type} {Y Y' : C → Type} [Fintype U] [Fintype V]
    [∀ b, Fintype (X b)] [∀ b, Fintype (X' b)] [∀ c, Fintype (Y c)] [∀ c, Fintype (Y' c)]
    {A : Tensor K U (∀ b, X b) (∀ c, Y c)} {S : Tensor K V (∀ b, X' b) (∀ c, Y' c)}
    (e : U ≃ V) (l : ∀ b, X b ≃ X' b) (r : ∀ c, Y c ≃ Y' c)
    (h : ∀ u x y, A u x y = S (e u) (fun b => l b (x b)) (fun c => r c (y c))) :
    p.value A = p.value S := by
  apply le_antisymm
  · apply p.mono
    have ha : A = Tensor.pullback e (fun x b => l b (x b)) (fun y c => r c (y c)) S :=
      funext fun u => funext fun x => funext fun y => h u x y
    rw [ha]
    exact siteRestriction_pullback _ (fun b => l b) (fun c => r c) _
  · apply p.mono
    have hs : S = Tensor.pullback e.symm (fun x b => (l b).symm (x b))
        (fun y c => (r c).symm (y c)) A := by
      funext v x y
      simpa only [Tensor.pullback, Equiv.apply_symm_apply] using
        (h (e.symm v) (fun b => (l b).symm (x b)) (fun c => (r c).symm (y c))).symm
    rw [hs]
    exact siteRestriction_pullback _ (fun b => (l b).symm) (fun c => (r c).symm) _

end SitePriceEval

namespace PermutationStretch

variable {R W M UB UC : Type} {X : B → Type} {Y : C → Type}

/-- A private tensor supported on the common site and the sites in `B`. -/
def placeB (C : Type) (P : UB → (∀ b, X b) → K) : Tensor K UB (∀ b, X b) (C → Unit) :=
  fun u x _ => P u x

/-- A private tensor supported on the common site and the sites in `C`. -/
def placeC (B : Type) (Q : UC → (∀ c, Y c) → K) : Tensor K UC (B → Unit) (∀ c, Y c) :=
  fun u _ y => Q u y

/-- The product of the two private tensors, omitting one-dimensional slots. -/
def joinedPrivate (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) :
    Tensor K (UB × UC) (∀ b, X b) (∀ c, Y c) :=
  fun u x y => P u.1 x * Q u.2 y

/-- Diagonal on `{u} ∪ B`, with one-dimensional slots on `C`. -/
def diagB (B C W : Type) := placeB (K := K) C (diagonalCoeff (W := W) (B := B))

/-- Diagonal on `{u} ∪ C`, with one-dimensional slots on `B`. -/
def diagC (B C W : Type) := placeC (K := K) B (diagonalCoeff (W := W) (B := C))

/-- Diagonal on the union of the two sides. -/
def diagAll (B C W : Type) : Tensor K W (B → W) (C → W) :=
  fun w x y => diagonalCoeff w x * diagonalCoeff w y

/-- The shared diagonal times the two original private tensors
(`doubling-target` in the manuscript). -/
def sharedTarget (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) :
    Tensor K (R × UB × UC) (∀ b, R × X b) (∀ c, R × Y c) :=
  fun u x y =>
    diagonalCoeff u.1 (fun b => (x b).1) * diagonalCoeff u.1 (fun c => (y c).1) *
      P u.2.1 (fun b => (x b).2) * Q u.2.2 (fun c => (y c).2)

omit [Fintype B] [Fintype C] in
private theorem placeB_ne_zero {P : UB → (∀ b, X b) → K} (hP : P ≠ 0) :
    placeB C P ≠ 0 := by
  intro h
  exact hP (funext fun u => funext fun x => congrFun (congrFun (congrFun h u) x) (fun _ => ()))

omit [Fintype B] [Fintype C] in
private theorem placeC_ne_zero {Q : UC → (∀ c, Y c) → K} (hQ : Q ≠ 0) :
    placeC B Q ≠ 0 := by
  intro h
  exact hQ (funext fun u => funext fun y => congrFun (congrFun (congrFun h u) (fun _ => ())) y)

omit [Fintype B] [Fintype C] in
private theorem joinedPrivate_ne_zero {P : UB → (∀ b, X b) → K} {Q : UC → (∀ c, Y c) → K}
    (hP : P ≠ 0) (hQ : Q ≠ 0) : joinedPrivate P Q ≠ 0 := by
  contrapose! hP
  obtain ⟨v, y, hv⟩ : ∃ v y, Q v y ≠ 0 := by
    by_contra! hn
    exact hQ (funext fun v => funext (hn v))
  funext u x
  exact (mul_eq_zero.mp (congrFun (congrFun (congrFun hP (u, v)) x) y)).resolve_right hv

omit [Fintype B] in
private theorem diagonalCoeff_ne_zero [Nonempty W] :
    diagonalCoeff (K := K) (B := B) (W := W) ≠ 0 := by
  intro h
  obtain ⟨w⟩ := ‹Nonempty W›
  simpa [diagonalCoeff] using congrFun (congrFun h w) (fun _ => w)

omit [Fintype B] [Fintype C] in
private theorem diagAll_ne_zero [Nonempty W] : diagAll (K := K) B C W ≠ 0 := by
  intro h
  obtain ⟨w⟩ := ‹Nonempty W›
  simpa [diagAll, diagonalCoeff] using congrFun (congrFun (congrFun h w) (fun _ => w)) (fun _ => w)

omit [Fintype B] [Fintype C] in
theorem diagC_ne_zero [Nonempty W] : diagC (K := K) B C W ≠ 0 :=
  placeC_ne_zero diagonalCoeff_ne_zero

omit [Fintype B] in
private theorem privatePower_ne_zero [Fintype M]
    {P : UB → (∀ b, X b) → K} (hP : P ≠ 0) :
    privatePower (M := M) P ≠ 0 := by
  obtain ⟨u, x, hx⟩ : ∃ u x, P u x ≠ 0 := by
    by_contra! hn
    exact hP (funext fun u => funext (hn u))
  intro hz
  have h := congrFun (congrFun hz (fun _ => u)) (fun b _ => x b)
  exact (Finset.prod_ne_zero_iff.mpr (fun j _ => hx)) h

omit [Fintype B] [Fintype C] in
theorem sharedTarget_ne_zero [Nonempty R]
    {P : UB → (∀ b, X b) → K} {Q : UC → (∀ c, Y c) → K} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    sharedTarget (R := R) P Q ≠ 0 := by
  obtain ⟨w⟩ := ‹Nonempty R›
  intro hz
  apply joinedPrivate_ne_zero hP hQ
  funext u x y
  simpa [sharedTarget, diagonalCoeff, joinedPrivate] using
    congrFun (congrFun (congrFun hz (w, u)) (fun b => (w, x b))) (fun c => (w, y c))

variable [Fintype UB] [Fintype UC] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]

/-- The price of a product of private tensors is the sum of their prices at their
respective placements. -/
theorem value_joinedPrivate (p : SitePriceEval K B C) (hmul : p.BinaryProductAdditive)
    (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    p.value (joinedPrivate P Q) = p.value (placeB C P) + p.value (placeC B Q) := by
  rw [← hmul (placeB C P) (placeC B Q) (placeB_ne_zero hP) (placeC_ne_zero hQ)]
  apply p.value_reindex (Equiv.refl _) (fun b => (Equiv.prodUnique (X b) Unit).symm)
    (fun c => (Equiv.uniqueProd (Y c) Unit).symm)
  intros
  rfl

/-- Pricing the original shared diagonal times the two private tensors. -/
theorem value_sharedTarget [Fintype R] [Nonempty R] (p : SitePriceEval K B C)
    (hmul : p.BinaryProductAdditive) (P : UB → (∀ b, X b) → K)
    (Q : UC → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    p.value (sharedTarget (R := R) P Q) =
      p.value (diagAll (K := K) B C R) + (p.value (placeB C P) + p.value (placeC B Q)) := by
  rw [← value_joinedPrivate p hmul P Q hP hQ,
    ← hmul _ _ diagAll_ne_zero (joinedPrivate_ne_zero hP hQ)]
  congr 1
  funext u x y
  simp only [sharedTarget, SitePriceEval.splitProduct, diagAll, joinedPrivate, mul_assoc]

/-- A power of the product of private tensors, in paired power coordinates at
the common site. -/
theorem value_privatePowers [Fintype M] [DecidableEq M] (p : SitePriceEval K B C)
    (hword : p.WordProductAdditive) (P : UB → (∀ b, X b) → K)
    (Q : UC → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    p.value (joinedPrivate (privatePower (M := M) P) (privatePower (M := M) Q)) =
      Fintype.card M * p.value (joinedPrivate P Q) := by
  let A (_ : Unit) := joinedPrivate P Q
  let s (_ : M) := ()
  calc
    _ = p.value (PermutationControl.wordProduct A s) := by
      apply p.value_reindex (Equiv.arrowProdEquivProdArrow M (fun _ => UB) (fun _ => UC)).symm
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
      intro u x y
      simp only [joinedPrivate, privatePower, PermutationControl.wordProduct, A, s,
        Equiv.arrowProdEquivProdArrow_symm_apply, Equiv.refl_apply, Finset.prod_mul_distrib]
    _ = _ := by
      rw [hword A (fun _ => joinedPrivate_ne_zero hP hQ) s]
      simp [A]

/-- Regrouping power coordinates independently at each site identifies the
price of the shared power with the length times the one-copy price. -/
theorem value_sharedPower [Fintype M] [DecidableEq M] [Fintype R] [Nonempty R]
    (p : SitePriceEval K B C) (hword : p.WordProductAdditive)
    (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    p.value (sharedPower (M := M) (R := R) P Q) =
      Fintype.card M * p.value (sharedTarget (R := R) P Q) := by
  let pair (A D : Type) := (Equiv.arrowProdEquivProdArrow M (fun _ => A) (fun _ => D)).symm
  let e := ((Equiv.refl (M → R)).prodCongr (pair UB UC)).trans (pair R (UB × UC))
  let T (_ : Unit) := sharedTarget (R := R) P Q
  let s (_ : M) := ()
  calc
    _ = p.value (PermutationControl.wordProduct T s) := by
      apply p.value_reindex e (fun b => pair R (X b)) (fun c => pair R (Y c))
      rintro ⟨w, u, v⟩ x y
      exact sharedPower_eq_prod P Q w u v x y
    _ = _ := by
      rw [hword T (fun _ => sharedTarget_ne_zero hP hQ) s]
      simp [T]

/-- Pricing the four-factor restriction in the first line of
`doubling-stretched`, over any field. -/
theorem value_independent [Fintype M] [DecidableEq M] [Fintype W] [Nonempty W]
    (p : SitePriceEval K B C) (hmul : p.BinaryProductAdditive) (hword : p.WordProductAdditive)
    (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    p.value (independent (M := M) (W := W) P Q) =
      Fintype.card M * p.value (joinedPrivate P Q) +
        (p.value (diagB (K := K) B C W) + p.value (diagC (K := K) B C W)) := by
  let dB := diagonalCoeff (K := K) (W := W) (B := B)
  let dC := diagonalCoeff (K := K) (W := W) (B := C)
  let P' := privatePower (M := M) P
  let Q' := privatePower (M := M) Q
  calc
    _ = p.value (SitePriceEval.splitProduct (joinedPrivate dB dC) (joinedPrivate P' Q')) := by
      apply p.value_reindex (Equiv.prodAssoc _ _ _).symm
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
      intro u x y
      simp only [SitePriceEval.splitProduct, joinedPrivate, independent, P', Q', dB, dC,
        Equiv.prodAssoc_symm_apply, Equiv.refl_apply, mul_assoc]
    _ = _ := by
      rw [hmul _ _ (joinedPrivate_ne_zero diagonalCoeff_ne_zero diagonalCoeff_ne_zero)
        (joinedPrivate_ne_zero (privatePower_ne_zero hP) (privatePower_ne_zero hQ)),
        value_privatePowers p hword P Q hP hQ,
        value_joinedPrivate p hmul dB dC diagonalCoeff_ne_zero diagonalCoeff_ne_zero]
      exact add_comm _ _

/-- The independent-diagonal lower bound after removing the known price of
the shared diagonal from the one-copy target. -/
theorem value_independent_eq_sharedTarget_sub [Fintype M] [DecidableEq M] [Fintype W] [Nonempty W]
    [Fintype R] [Nonempty R] (p : SitePriceEval K B C)
    (hmul : p.BinaryProductAdditive) (hword : p.WordProductAdditive)
    (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    {D E : ℝ} (hd : p.value (diagAll (K := K) B C R) = D * Real.logb 2 (Fintype.card R))
    (hdB : p.value (diagB (K := K) B C W) = D * Real.logb 2 (Fintype.card W))
    (hdC : p.value (diagC (K := K) B C W) = E * Real.logb 2 (Fintype.card W)) :
    p.value (independent (M := M) (W := W) P Q) =
      Fintype.card M * (p.value (sharedTarget (R := R) P Q) - D * Real.logb 2 (Fintype.card R)) +
        (D + E) * Real.logb 2 (Fintype.card W) := by
  rw [value_independent p hmul hword P Q hP hQ, value_sharedTarget p hmul P Q hP hQ,
    value_joinedPrivate p hmul P Q hP hQ, hd, hdB, hdC]
  ring

/-- The collapsed-placement target increment (`doubling-increment`). The two
placements agree with the surviving private price, and a tensor entirely
collapsed to the common site has price zero. -/
theorem sharedTarget_increment [Fintype R] [Nonempty R] (a b c : SitePriceEval K B C)
    (ha : a.BinaryProductAdditive) (hb : b.BinaryProductAdditive) (hc : c.BinaryProductAdditive)
    (P : UB → (∀ i, X i) → K) (Q : UC → (∀ i, Y i) → K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    {D E : ℝ} (had : a.value (diagAll (K := K) B C R) = D * Real.logb 2 (Fintype.card R))
    (hbd : b.value (diagAll (K := K) B C R) = D * Real.logb 2 (Fintype.card R))
    (hcd : c.value (diagAll (K := K) B C R) = E * Real.logb 2 (Fintype.card R))
    (hbP : b.value (placeB C P) = a.value (placeB C P)) (hbQ : b.value (placeC B Q) = 0)
    (hcP : c.value (placeB C P) = 0) (hcQ : c.value (placeC B Q) = a.value (placeC B Q)) :
    b.value (sharedTarget (R := R) P Q) + c.value (sharedTarget (R := R) P Q) =
      a.value (sharedTarget (R := R) P Q) + E * Real.logb 2 (Fintype.card R) := by
  rw [value_sharedTarget a ha P Q hP hQ, value_sharedTarget b hb P Q hP hQ,
    value_sharedTarget c hc P Q hP hQ, had, hbd, hcd, hbP, hbQ, hcP, hcQ]
  ring

end PermutationStretch
end

end

end SpectralBooks
end LinearAlgebra
end OAI
