import OAI.Hierarchy.CorrectionProducts
import OAI.Hierarchy.WireProductPrice

namespace OAI
/-! # Independent placed factors with different port sets -/

namespace Hierarchy.GridFactors
open LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators Classical
noncomputable section

variable {C J : Type} [Fintype C] [Fintype J] [Nonempty J]
variable {F : Type*} [Field F]

/-- Independent coefficient tables, with all occurrences kept distinct before gluing. -/
def independent {I : C → Type} (f : (c : C) → (I c → Bool) → F)
    (a : (Σ c, I c) → Bool) : F := ∏ c, f c (fun i => a ⟨c,i⟩)

private def familyProduct (T : C → Raw.{0} J F) : Raw.{0} J F where
  Leg j := ∀ c, (T c).Leg j
  finiteLeg _ := inferInstance
  coeff a := ∏ c, (T c).coeff (fun j => a j c)

private theorem familyProduct_class (T : C → Raw.{0} J F) :
    ofRaw (familyProduct T) = ∏ c, ofRaw (T c) := by
  let e := Fintype.equivFin C
  have changeIndex : ofRaw (familyProduct T) = ofRaw (Raw.finProduct (fun i => T (e.symm i))) := by
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent (fun j => (Equiv.piCongrLeft' (fun c => (T c).Leg j) e))
    intro a
    exact (e.symm.prod_comp (fun c => (T c).coeff (fun j => a j c))).symm
  rw [changeIndex, ofRaw_finProduct]
  exact e.symm.prod_comp (fun c => ofRaw (T c))

variable {I : C → Type} [∀ c, Fintype (I c)]

private def split (s : (Σ c, I c) → J) (j : J) :
    ({z : Σ c, I c // s z = j} → Bool) ≃
      (∀ c, {i : I c // s ⟨c,i⟩ = j} → Bool) where
  toFun a c i := a ⟨⟨c,i.1⟩,i.2⟩
  invFun a z := a z.1.1 ⟨z.1.2,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem independent_group_class (f : (c : C) → (I c → Bool) → F)
    (s : (Σ c, I c) → J) :
    ofRaw ((CorrectionProducts.raw (independent f)).group s) =
      ∏ c, ofRaw ((CorrectionProducts.raw (f c)).group (fun i => s ⟨c,i⟩)) := by
  rw [← familyProduct_class]
  exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent (split s) (fun _ => rfl))

/-- Exact prices add across the independent factors before any contractions at sites. -/
theorem independent_price {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices F Y)
    (f : (c : C) → (I c → Bool) → F) (s : (Σ c, I c) → J) (x : J → Y)
    (nz : ∀ c, f c ≠ 0) :
    P.price (CorrectionProducts.raw (independent f)) (x ∘ s) =
      ∑ c, P.price (CorrectionProducts.raw (f c)) (fun i => x (s ⟨c,i⟩)) := by
  rw [P.group, WirePrice.product P x _ _ (fun c =>
    ((CorrectionProducts.raw (f c)).group_ne_zero_iff (fun i => s ⟨c,i⟩)).2 (nz c))
    (independent_group_class f s)]
  apply Finset.sum_congr rfl
  intro c _
  exact (P.group (CorrectionProducts.raw (f c)) (fun i => s ⟨c,i⟩) x).symm

/-- Any two-legged bit table can be implemented at one end after moving the other bit. -/
theorem link_price_le {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices F Y)
    (f : (Bool → Bool) → F) (x : Bool → Y) :
    P.price (CorrectionProducts.raw f) x ≤ dist (x false) (x true) := by
  have transfer := P.transport (CorrectionProducts.raw f) x (fun _ => x true)
  rw [P.collapsed, Real.dist_eq, sub_zero] at transfer
  refine (le_abs_self _).trans (transfer.trans ?_)
  have dim (i : Fintype Bool) : @Fintype.card Bool i = 2 := by
    rw [show i = Bool.fintype from Subsingleton.elim _ _]
    exact Fintype.card_bool
  have leg (b : Bool) : Fintype.card ((CorrectionProducts.raw f).Leg b) = 2 := dim _
  simp_rw [leg]
  simp []

end
end Hierarchy.GridFactors

end OAI
