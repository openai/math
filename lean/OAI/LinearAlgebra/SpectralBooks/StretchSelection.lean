import OAI.LinearAlgebra.SpectralBooks.StretchPriceUpper

/-! # Selecting a common product summand in the permutation stretch

The lower restriction and both upper restrictions are applied to the same tagged
ordinary sum. Choosing a term once, via the ordinary-sum bound for `a`, preserves
both upper estimates when its tag is removed.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical BigOperators
open MatrixMultiplication.Foundation

section

open PermutationStretch PermutationControl

variable {K : Type*} [CommSemiring K] {B C : Type} [Fintype B] [Fintype C]
    {X : B → Type} {Y : C → Type} [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    {R UB UC J W L Tag : Type} [Fintype R] [Fintype UB] [Fintype UC]
    [Fintype J] [DecidableEq J] [Fintype W] [Fintype L] [Nonempty L] [Fintype Tag] [Nonempty Tag]

omit [Nonempty L] [Nonempty Tag] in
/-- The source and target of the tagged-power expansion use sitewise permutations
of coordinates. The maps below make the expansion an ordinary sum in a single
format up to restriction. -/
theorem tagged_expansion_restriction (perm : Tag → Equiv.Perm J)
    (P : UB → (∀ h, X h) → K) (Q : UC → (∀ i, Y i) → K)
    (T : L → Tensor K (R × UB × UC) (∀ h, R × X h) (∀ i, R × Y i))
    (hsum : ∀ w u v (b : ∀ h, R × X h) (c : ∀ i, R × Y i),
      diagonalCoeff w (fun h => (b h).1) * diagonalCoeff w (fun i => (c i).1) *
        P u (fun h => (b h).2) * Q v (fun i => (c i).2) = ∑ l, T l (w, u, v) b c) :
    SiteRestriction (PermutationStretch.tagged (R := R) perm P Q) (fun u b c => ∑ s : J → L,
      PermutationControl.tagged (fun t d i => d i ∘ perm t) (wordProduct T s) u b c) := by
  let center (a : Tag × (J → R) × (J → UB) × (J → UC)) :=
    (a.1, fun j => (a.2.1 j, a.2.2.1 j, a.2.2.2 j))
  let left (h : B) (b : (J → R) × (J → X h)) := fun j => (b.1 j, b.2 j)
  let right (i : C) (c : (J → R) × (J → Y i)) := fun j => (c.1 j, c.2 j)
  let S := fun u b c => ∑ s : J → L,
    PermutationControl.tagged (fun t d i => d i ∘ perm t) (wordProduct T s) u b c
  have h : PermutationStretch.tagged (R := R) perm P Q =
      Tensor.pullback center (fun b h => left h (b h)) (fun c i => right i (c i)) S :=
    funext fun a => funext fun b => funext fun c => tagged_sharedPower_eq_sum_wordProduct perm P Q T hsum a b c
  change SiteRestriction _ S
  rw [h]
  exact siteRestriction_pullback center left right S

/-- For each power length, a word `s` witnesses all three price inequalities in
the proof of Lemma `stretch`. The input `hslice` is the bound from the two
collapsed slice placements. -/
theorem exists_stretch_word (a b c : SitePriceEval K B C) {D E : ℝ}
    (haSum : a.OrdinarySumBound D) (haDiag : a.DiagonalControlBound E)
    (hb : b.MonoGroupedC) (hc : c.MonoGroupedB) (hcSum : c.OrdinarySumBound E)
    (word : W ↪ (J → R)) (perm : Tag → Equiv.Perm J) (hcover : ∀ i j, ∃ t, word j ∘ perm t = word i)
    (P : UB → (∀ h, X h) → K) (Q : UC → (∀ i, Y i) → K)
    (T : L → Tensor K (R × UB × UC) (∀ h, R × X h) (∀ i, R × Y i))
    (hsum : ∀ w u v (x : ∀ h, R × X h) (y : ∀ i, R × Y i),
      diagonalCoeff w (fun h => (x h).1) * diagonalCoeff w (fun i => (y i).1) *
        P u (fun h => (x h).2) * Q v (fun i => (y i).2) = ∑ l, T l (w, u, v) x y)
    (hslice : ∀ s : J → L,
      let Z := PermutationControl.tagged (fun t d i => d i ∘ perm t) (wordProduct T s)
      a.value Z ≤ b.value Z + c.value Z) :
    ∃ (s : J → L) (z : ℝ),
      a.value (independent (W := W) (M := J) P Q) ≤ z + D * Fintype.card J * Real.logb 2 (Fintype.card L) ∧
      z ≤ a.value (wordProduct T s) + E * Real.logb 2 (Fintype.card Tag) ∧
      z ≤ b.value (wordProduct T s) + c.value (wordProduct T s) +
        E * Fintype.card J * Real.logb 2 (Fintype.card L) := by
  let Z (s : J → L) := PermutationControl.tagged (fun t d i => d i ∘ perm t) (wordProduct T s)
  have hlower := a.mono (independent_restriction word perm hcover P Q)
  have hexpand := a.mono (tagged_expansion_restriction perm P Q T hsum)
  obtain ⟨s, hs⟩ := haSum Z
  refine ⟨s, a.value (Z s), ?_, taggedWord_price_upper_a a haDiag T s perm,
    taggedWord_price_upper_bc a b c hb hc hcSum T s perm (hslice s)⟩
  exact (hlower.trans hexpand).trans (by simpa [Real.logb_pow, mul_assoc] using hs)

end

end SpectralBooks
end LinearAlgebra
end OAI
