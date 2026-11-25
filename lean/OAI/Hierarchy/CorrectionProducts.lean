import OAI.LinearAlgebra.SpectralBooks.CrossingWireClass
import OAI.LinearAlgebra.SpectralBooks.SpanValue

namespace OAI
/-! # Spectral evaluation of independent correction factors

Grouping the physical bits at their occupied sites commutes with taking an
independent product. The factors can be arbitrary coefficient tables, so each
row of a sparse correction may independently use the error or the approximation.
-/

noncomputable section
namespace Hierarchy.CorrectionProducts
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators NNReal

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty J] {F : Type*} [Field F]

/-- One physical basis bit on each port. -/
def raw (f : (I → Bool) → F) : Raw.{0} I F := ⟨fun _ => Bool, fun _ => inferInstance, f⟩

abbrev Point (J : Type) [Fintype J] [Nonempty J] (F : Type*) [Field F] :=
  normalizedSpectrum (fun a b : TensorClass.{0} J F => a ≤ b)

variable (φ : Point J F) (σ : I → J)

/-- The common spectral point first groups all ports at their assigned sites. -/
def value (f : (I → Bool) → F) : ℝ≥0 := φ.val (ofRaw ((raw f).group σ))

@[simp] theorem value_zero : value φ σ (0 : (I → Bool) → F) = 0 := by
  unfold value
  rw [(ofRaw_eq_zero_iff ((raw (0 : (I → Bool) → F)).group σ)).mpr rfl, φ.property.1]

theorem one_le_value {f : (I → Bool) → F} (hf : f ≠ 0) : 1 ≤ value φ σ f :=
  one_le_raw_spectralValue φ _ (((raw f).group_ne_zero_iff σ).2 hf)

theorem value_pos {f : (I → Bool) → F} (hf : f ≠ 0) : 0 < value φ σ f :=
  zero_lt_one.trans_le (one_le_value φ σ hf)

@[simp] theorem value_neg (f : (I → Bool) → F) : value φ σ (-f) = value φ σ f := by
  have le_neg (g : (I → Bool) → F) : value φ σ (-g) ≤ value φ σ g := by
    let u : ((j : J) → {i : I // σ i = j} → Bool) → F :=
      fun x => g (fun i => x (σ i) ⟨i,rfl⟩)
    change coeffValue φ (-u) ≤ coeffValue φ u
    simpa only [neg_one_smul] using coeffValue_smul_le φ (-1 : F) u
  exact le_antisymm (le_neg f) (by simpa only [neg_neg] using le_neg (-f))

theorem value_sum_le {L : Type*} [Fintype L] (f : L → (I → Bool) → F) :
    value φ σ (∑ l, f l) ≤ ∑ l, value φ σ (f l) := by
  have sum_eq : ((raw (∑ l, f l)).group σ).coeff =
      ∑ l, ((raw (f l)).group σ).coeff := by
    funext x
    let decode (y : (j : J) → {i : I // σ i = j} → Bool) (i : I) := y (σ i) ⟨i,rfl⟩
    change (∑ l, f l) (decode x) = (∑ l, fun y => f l (decode y)) x
    exact (Finset.sum_apply (decode x) Finset.univ f).trans
      (Finset.sum_apply x Finset.univ (fun l y => f l (decode y))).symm
  change coeffValue φ ((raw (∑ l, f l)).group σ).coeff ≤ _
  rw [sum_eq]
  exact ordinary_sum_value_le φ _

theorem value_add_le (f g : (I → Bool) → F) :
    value φ σ (f + g) ≤ value φ σ f + value φ σ g := by
  simpa [Fintype.sum_bool] using value_sum_le φ σ (fun b : Bool => if b then f else g)

theorem value_finset_sum_le {L : Type*} (S : Finset L) (f : L → (I → Bool) → F) :
    value φ σ (∑ l ∈ S, f l) ≤ ∑ l ∈ S, value φ σ (f l) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert l S hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl]
    exact (value_add_le φ σ _ _).trans (add_le_add le_rfl ih)

private def fiberCopies {s : ℕ} (j : J) :
    ({a : Fin s × I // σ a.2 = j} → Bool) ≃
      (Fin s → {i : I // σ i = j} → Bool) where
  toFun x r i := x ⟨(r,i.val),i.property⟩
  invFun x a := x a.val.1 ⟨a.val.2,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Independent physical rows retain the product of their spectral values
after grouping, even when the placement has empty fibers or repeated sites. -/
theorem value_product {s : ℕ} (f : Fin s → (I → Bool) → F) :
    value φ (σ ∘ Prod.snd) (fun x => ∏ r, f r (fun i => x (r,i))) =
      ∏ r, value φ σ (f r) := by
  let T (r : Fin s) := (raw (f r)).group σ
  have classes :
      ofRaw ((raw (fun x => ∏ r, f r (fun i => x (r,i)))).group (σ ∘ Prod.snd)) =
        ofRaw (Raw.finProduct T) := by
    apply ofRaw_eq_iff.mpr
    exact Raw.reindex_equivalent (fiberCopies σ) (fun _ => rfl)
  change (normalizedSpectrum.toRingHom φ) (ofRaw _) = ∏ r, (normalizedSpectrum.toRingHom φ) (ofRaw (T r))
  rw [classes, ofRaw_finProduct, map_prod]

private theorem choose_product {R : Type*} [CommMonoid R] {s : ℕ} (S : Finset (Fin s))
    (f g : Fin s → R) :
    (∏ r, if r ∈ S then f r else g r) = (∏ r ∈ S, f r) * ∏ r ∈ Sᶜ, g r := by
  rw [← S.prod_mul_prod_compl (fun r => if r ∈ S then f r else g r)]
  congr 1
  · exact Finset.prod_congr rfl (fun r hr => ite_eq_left hr)
  · exact Finset.prod_congr rfl (fun r hr => ite_eq_right (Finset.mem_compl.mp hr))

/-- A term with selected error rows is valued by the indicated two powers,
including a zero factor or an empty selection. -/
theorem value_mixed {s : ℕ} (S : Finset (Fin s)) (error ordinary : (I → Bool) → F) :
    value φ (σ ∘ Prod.snd) (fun x =>
      (∏ r ∈ S, error (fun i => x (r,i))) * ∏ r ∈ Sᶜ, ordinary (fun i => x (r,i))) =
      value φ σ error ^ S.card * value φ σ ordinary ^ Sᶜ.card := by
  let f (r : Fin s) := if r ∈ S then error else ordinary
  have row (r : Fin s) (x : Fin s × I → Bool) : f r (fun i => x (r,i)) =
      if r ∈ S then error (fun i => x (r,i)) else ordinary (fun i => x (r,i)) := by
    by_cases h : r ∈ S <;> simp [f,h]
  have coeff (x : Fin s × I → Bool) := choose_product S
    (fun r => error (fun i => x (r,i))) (fun r => ordinary (fun i => x (r,i)))
  have v (r : Fin s) : value φ σ (f r) =
      if r ∈ S then value φ σ error else value φ σ ordinary := by
    by_cases h : r ∈ S <;> simp [f,h]
  simpa only [row, coeff, v, choose_product, Finset.prod_const] using value_product φ σ f

end Hierarchy.CorrectionProducts

end
end OAI
