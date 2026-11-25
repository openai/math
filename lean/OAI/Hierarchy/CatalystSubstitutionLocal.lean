import OAI.Hierarchy.GridPortContraction

namespace OAI
/-! # A local contraction at the origin with arbitrary spectator ports

The kernel may sum over all hidden settings of an opened network. Only its data
port labels enter the local matrix. Each spectator bit passes by an identity.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators

variable {D L B O : Type} [Fintype D] [DecidableEq D] [Fintype L] [Fintype B] [Fintype O]
variable {F : Type*} [Field F]

def bitTensor {I : Type} (v : (I → Bool) → F) : Raw.{0} I F :=
  ⟨fun _ => Bool, fun _ => inferInstance, v⟩

private def gateSite (A B : Type) : A ⊕ B → Option B := Sum.elim (fun _ => none) some

def localAction (e : L ⊕ B ≃ O) (K : (L → Bool) → (D → Bool) → F)
    (v : (D ⊕ B → Bool) → F) (x : O → Bool) : F :=
  ∑ h : D → Bool, K (fun i => x (e (.inl i))) h * v (Sum.elim h (fun i => x (e (.inr i))))

omit [Fintype L] [Fintype B] [Fintype O] in
@[simp] theorem localAction_zero (e : L ⊕ B ≃ O) (K : (L → Bool) → (D → Bool) → F) :
    localAction e K 0 = 0 := by funext x; simp [localAction]

private def kernelMatrix (e : L ⊕ B ≃ O) (K : (L → Bool) → (D → Bool) → F) :
    (j : Option B) → ({i : O // gateSite L B (e.symm i) = j} → Bool) →
    ({i : D ⊕ B // gateSite D B i = j} → Bool) → F
  | none, x, a => K (fun l => x ⟨e (.inl l), by simp [gateSite]⟩) (fun d => a ⟨.inl d,rfl⟩)
  | some b, x, a => if a ⟨.inr b,rfl⟩ = x ⟨e (.inr b),by simp [gateSite]⟩ then 1 else 0

omit [Fintype L] in
/-- Every spectator has its own grouped port. Their physical sites may coincide. -/
theorem price_localAction {M : Type} [MetricSpace M] (P : SpectralPlacementPrices F M)
    (e : L ⊕ B ≃ O) (K : (L → Bool) → (D → Bool) → F) (v : (D ⊕ B → Bool) → F)
    (y : Option B → M) :
    P.price (bitTensor (localAction e K v)) (y ∘ gateSite L B ∘ e.symm) ≤
      P.price (bitTensor v) (y ∘ gateSite D B) := by
  let : DecidableEq (D ⊕ B) := Classical.decEq _
  apply GridPort.price_output_le P (bitTensor v) (bitTensor (localAction e K v)) (gateSite D B)
    (gateSite L B ∘ e.symm) (kernelMatrix e K) _ y
  intro x
  change O → Bool at x
  let t : B → Bool := fun b => x (e (.inr b))
  let w : L → Bool := fun l => x (e (.inl l))
  change (∑ h, K w h * v (Sum.elim h t)) =
    ∑ a : D ⊕ B → Bool, v a * ∏ j : Option B, kernelMatrix e K j
      (groupIndexEquiv (gateSite L B ∘ e.symm) (fun _ => Bool) x j) (fun r => a r.1)
  simp only [Fintype.prod_option,kernelMatrix]
  rw [← (Equiv.sumArrowEquivProdArrow D B Bool).symm.sum_comp, Fintype.sum_prod_type]
  change _ = ∑ h : D → Bool, ∑ u : B → Bool, v (Sum.elim h u) *
    (K w h * ∏ b, @ite F (u b = t b) (instDecidableEqBool (u b) (t b)) 1 0)
  apply Finset.sum_congr rfl
  intro h _
  symm
  erw [Finset.sum_eq_single t]
  · simp [mul_comm]
  · intro u _ ne
    obtain ⟨b,hb⟩ : ∃ b, u b ≠ t b := not_forall.mp (fun hu => ne (funext hu))
    have z : (∏ j, @ite F (u j = t j) (instDecidableEqBool (u j) (t j)) 1 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) (ite_eq_right hb)
    rw [z,mul_zero,mul_zero]
  · simp

/-- Moving the newly exposed local ports to their physical positions costs the
sum of their travel distances. Spectator ports already occupy their final sites. -/
theorem price_move_localAction {M : Type} [MetricSpace M] (P : SpectralPlacementPrices F M)
    (e : L ⊕ B ≃ O) (K : (L → Bool) → (D → Bool) → F) (v : (D ⊕ B → Bool) → F)
    (x : O → M) (z : M) (y : B → M) (fixed : ∀ b, x (e (.inr b)) = y b) :
    P.price (bitTensor (localAction e K v)) x ≤
      P.price (bitTensor v) (Sum.elim (fun _ => z) y) + ∑ l : L, dist (x (e (.inl l))) z := by
  let Y := Option.elim' z y
  let σ := Y ∘ gateSite L B ∘ e.symm
  have near := price_localAction P e K v Y
  have atInput : Y ∘ gateSite D B = Sum.elim (fun _ => z) y := by funext i; cases i <;> rfl
  rw [atInput] at near
  have travel := P.transport (bitTensor (localAction e K v)) x σ
  rw [Real.dist_eq] at travel
  have total : (∑ i : O, dist (x i) (σ i) * Real.logb 2 (Fintype.card ((bitTensor (localAction e K v)).Leg i))) =
      ∑ l : L, dist (x (e (.inl l))) z := by
    change (∑ i : O, dist (x i) (σ i) * Real.logb 2 (Fintype.card Bool)) = _
    rw [Fintype.card_bool,Nat.cast_ofNat,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    simp only [mul_one]
    rw [← e.sum_comp, Fintype.sum_sum_type]
    have sl (l : L) : σ (e (.inl l)) = z := by simp [σ,Function.comp_def,gateSite,Y]
    have sr (b : B) : σ (e (.inr b)) = y b := by simp [σ,Function.comp_def,gateSite,Y]
    simp [sl,sr,fixed]
  rw [total] at travel
  have lt := (le_abs_self _).trans travel
  change P.price (bitTensor (localAction e K v)) σ ≤ _ at near
  linarith

end Hierarchy.CatalystSubstitution

end
end OAI
