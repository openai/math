import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

namespace OAI
/-! # Contracting ports at common physical sites -/

namespace Hierarchy.GridPort

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical
noncomputable section

variable {I J : Type} [Fintype I] [Fintype J] {F : Type*}

/-- Sum over the original port labels, evaluating one matrix at each site.
Its column is the tuple of labels of precisely those ports placed there. -/
def contract [CommSemiring F] (T : Raw.{0} I F) (σ : I → J) (A : J → Type)
    [∀ j, Fintype (A j)] (M : ∀ j, A j → (T.group σ).Leg j → F) : Raw.{0} J F where
  Leg := A
  finiteLeg := inferInstance
  coeff x := ∑ a : (∀ i, T.Leg i), T.coeff a * ∏ j, M j (x j) (fun p => a p.1)

/-- Local contractions are restrictions of the tensor with its ports grouped
by their physical sites, including when some sites have no ports. -/
theorem contract_restricts [CommSemiring F] (T : Raw.{0} I F) (σ : I → J) (A : J → Type)
    [∀ j, Fintype (A j)] (M : ∀ j, A j → (T.group σ).Leg j → F) :
    (contract T σ A M).Restricts (T.group σ) := by
  refine ⟨M, fun x => ?_⟩
  exact Fintype.sum_equiv (groupIndexEquiv σ T.Leg) _ _ (fun _ => rfl)

theorem price_contract_le {X : Type*} [MetricSpace X] [Field F] [Nonempty J]
    (P : SpectralPlacementPrices F X) (T : Raw.{0} I F) (σ : I → J) (A : J → Type)
    [∀ j, Fintype (A j)] (M : ∀ j, A j → (T.group σ).Leg j → F) (x : J → X) :
    P.price (contract T σ A M) x ≤ P.price T (x ∘ σ) := by
  rw [P.group T σ x]
  exact P.placed_mono x (contract_restricts T σ A M)

/-- A network may expose only selected external ports. When its output
coefficients are given by the local contractions, both placements use the
same physical sites, including those with no surviving output. -/
theorem price_output_le {O X : Type} [Fintype O] [MetricSpace X] [Field F] [Nonempty J]
    (P : SpectralPlacementPrices F X) (T : Raw.{0} I F) (S : Raw.{0} O F)
    (σ : I → J) (τ : O → J)
    (M : ∀ j, (S.group τ).Leg j → (T.group σ).Leg j → F)
    (coeff : ∀ y, S.coeff y = ∑ a : (∀ i, T.Leg i), T.coeff a *
      ∏ j, M j (groupIndexEquiv τ S.Leg y j) (fun p => a p.1)) (x : J → X) :
    P.price S (x ∘ τ) ≤ P.price T (x ∘ σ) := by
  rw [P.group S τ x, P.group T σ x]
  apply P.placed_mono x
  refine ⟨M, fun y => ?_⟩
  change S.coeff ((groupIndexEquiv τ S.Leg).symm y) = _
  rw [coeff]
  apply Fintype.sum_equiv (groupIndexEquiv σ T.Leg)
  intro a
  apply congrArg (T.coeff a * ·)
  exact congrArg (fun v : (∀ j, (S.group τ).Leg j) => ∏ j, M j (v j) (fun p => a p.1))
    ((groupIndexEquiv τ S.Leg).apply_symm_apply y)

/-- A bilinear form on each designated pair of co-located ports. Multiple
pairs can be evaluated at a site while its remaining ports feed the output. -/
structure Pairings [CommSemiring F] (T : Raw.{0} I F) (σ : I → J) where
  Pair : J → Type
  finitePair : ∀ j, Fintype (Pair j)
  left : ∀ j, Pair j → {i // σ i = j}
  right : ∀ j, Pair j → {i // σ i = j}
  weight : ∀ j (e : Pair j), T.Leg (left j e).1 → T.Leg (right j e).1 → F

attribute [instance] Pairings.finitePair

/-- The actual matrix coefficient of all the paired evaluations at a site. -/
def Pairings.matrix [CommSemiring F] {T : Raw.{0} I F} {σ : I → J} (B : Pairings T σ)
    {A : J → Type} (keep : ∀ j, A j → (T.group σ).Leg j → F)
    (j : J) (x : A j) (ports : (T.group σ).Leg j) : F :=
  keep j x ports * ∏ e, B.weight j e (ports (B.left j e)) (ports (B.right j e))

/-- Gluing the designated input pairs with their bilinear forms has price at
most that of the input at the same placement, for arbitrary output matrices. -/
theorem price_glue_le {X : Type*} [MetricSpace X] [Field F] [Nonempty J]
    (P : SpectralPlacementPrices F X) (T : Raw.{0} I F) (σ : I → J) (A : J → Type)
    [∀ j, Fintype (A j)] (B : Pairings T σ)
    (keep : ∀ j, A j → (T.group σ).Leg j → F) (x : J → X) :
    P.price (contract T σ A (B.matrix keep)) x ≤ P.price T (x ∘ σ) :=
  price_contract_le P T σ A (B.matrix keep) x

end
end Hierarchy.GridPort

end OAI
