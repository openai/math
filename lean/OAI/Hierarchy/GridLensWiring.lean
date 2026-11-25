import OAI.Hierarchy.GridAddressGluing
import OAI.Hierarchy.GridFactorProduct
import OAI.Hierarchy.UniversalGrid

namespace OAI
/-! # Prices of the controller's actual shared-address wiring -/

namespace Hierarchy.UniversalGrid.Wiring
open LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {P E : Type} {L : ℕ} (W : Wiring E P L)

abbrev Factor := Fin L ⊕ Fin W.equal.length

def Ports : W.Factor → Type
  | .inl _ => P
  | .inr _ => Bool

instance [Fintype P] (c : W.Factor) : Fintype (W.Ports c) := by
  cases c with
  | inl _ => exact inferInstanceAs (Fintype P)
  | inr _ => exact inferInstanceAs (Fintype Bool)

abbrev Occurrence := Σ c, W.Ports c
abbrev Sites := GridAddress.Site (Fin W.internal) (GridDiagonal.Ends E) W.Occurrence

def address : W.Occurrence → Address E W.internal
  | ⟨.inl i, p⟩ => W.pin i p
  | ⟨.inr i, false⟩ => (W.equal.get i).1
  | ⟨.inr i, true⟩ => (W.equal.get i).2

def factors (cells : Fin L → (P → Bool) → F) : (c : W.Factor) → (W.Ports c → Bool) → F
  | .inl i, x => cells i x
  | .inr _, x => if x false = x true then 1 else 0

def mixedEval (cells : Fin L → (P → Bool) → F) (x : GridDiagonal.Pins E) : F :=
  ∑ h : Bits W.internal,
    if ∀ uv ∈ W.equal, bit x h uv.1 = bit x h uv.2
    then ∏ i, cells i (fun j => bit x h (W.pin i j)) else 0

theorem mixedEval_const (f : (P → Bool) → F) : W.mixedEval (fun _ => f) = W.eval f := rfl

private theorem equality_product (x : GridDiagonal.Pins E) (h : Bits W.internal) :
    (∏ i : Fin W.equal.length,
      if bit x h (W.equal.get i).1 = bit x h (W.equal.get i).2 then (1:F) else 0) =
    if ∀ uv ∈ W.equal, bit x h uv.1 = bit x h uv.2 then 1 else 0 := by
  by_cases ok : ∀ uv ∈ W.equal, bit x h uv.1 = bit x h uv.2
  · rw [ite_eq_left ok]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left (ok (W.equal.get i) (List.get_mem _ _))
  · rw [ite_eq_right ok]
    push Not at ok
    obtain ⟨uv, member, different⟩ := ok
    obtain ⟨i, eq⟩ := List.mem_iff_get.mp member
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eq, ite_eq_right different])

/-- Reindexing by port occurrences recovers the exact shared hidden-bit sum,
including its scalar multiplicity when a hidden address is unused. -/
theorem mixedEval_eq (cells : Fin L → (P → Bool) → F) :
    W.mixedEval cells = GridAddress.evaluate (GridFactors.independent (W.factors cells)) W.address := by
  funext x
  unfold mixedEval GridAddress.evaluate
  apply Finset.sum_congr (congrArg (@Finset.univ (Bits W.internal)) (Subsingleton.elim _ _))
  intro h _
  rw [GridFactors.independent, Fintype.prod_sum_type]
  change _ = (∏ i, cells i (fun j => bit x h (W.pin i j))) *
    ∏ i : Fin W.equal.length, if bit x h (W.equal.get i).1 = bit x h (W.equal.get i).2 then 1 else 0
  rw [W.equality_product]
  split <;> simp

theorem cells_nonzero_of_mixedEval (cells : Fin L → (P → Bool) → F)
    (nz : W.mixedEval cells ≠ 0) (i : Fin L) : cells i ≠ 0 := by
  intro vanish
  apply nz
  funext x
  apply Finset.sum_eq_zero
  intro h _
  split
  · exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [vanish]; rfl)
  · rfl

abbrev cellAt {Y : Type*} (position : W.Sites → Y) (i : Fin L) (p : P) :=
  position (GridAddress.site W.address ⟨.inl i,p⟩)

abbrev edgeAt {Y : Type*} (position : W.Sites → Y) (i : Fin W.equal.length) (b : Bool) :=
  position (GridAddress.site W.address ⟨.inr i,b⟩)

/-- A real nonzero contraction pays the prices of its used cells and a distance for
each equality test in the actual controller list. Arbitrary identifications and
fixed data pins enter through the address-indexed local linear restrictions. -/
theorem mixedEval_price_le [Fintype P] [Fintype E] [Nonempty W.Sites] {Y : Type*}
    [MetricSpace Y] (prices : SpectralPlacementPrices F Y) (position : W.Sites → Y)
    (cells : Fin L → (P → Bool) → F) (nz : W.mixedEval cells ≠ 0) :
    prices.price (GridDiagonal.raw (W.mixedEval cells)) (position ∘ GridAddress.outputSite) ≤
      (∑ i, prices.price (CorrectionProducts.raw (cells i)) (W.cellAt position i)) +
        ∑ i, dist (W.edgeAt position i false) (W.edgeAt position i true) := by
  have allnz (c : W.Factor) : W.factors cells c ≠ 0 := by
    cases c with
    | inl i => exact W.cells_nonzero_of_mixedEval cells nz i
    | inr i =>
      intro eq
      have h := congrFun eq (fun _ => false)
      simp [factors] at h
  have first := GridAddress.price_le prices (GridFactors.independent (W.factors cells)) W.address position
  rw [W.mixedEval_eq cells]
  refine first.trans ?_
  change prices.price (CorrectionProducts.raw (GridFactors.independent (W.factors cells)))
      (position ∘ GridAddress.site W.address) ≤ _
  rw [GridFactors.independent_price prices _ _ _ allnz, Fintype.sum_sum_type]
  exact add_le_add le_rfl (Finset.sum_le_sum fun e _ =>
    GridFactors.link_price_le prices (W.factors cells (.inr e)) (W.edgeAt position e))

end
end Hierarchy.UniversalGrid.Wiring

end OAI
