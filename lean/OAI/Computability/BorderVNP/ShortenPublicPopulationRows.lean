import OAI.Computability.BorderVNP.ShortenPublicPopulationKeys

/-! # Counting a batch of moved rows with one-hot relative-bin tags

The geometric move classifier emits a product tile and one flag per relative
bin. Each occupied row's flags select its binary bin ordinal once. The
following population circuit reuses the existing moved-row frame and its
unchanged active and width fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit ParseBatchCounts ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped BigOperators

variable {U σ : Type*} {B : Type} [Fintype U] [Fintype B] [Fintype σ] {q l r w D : ℕ}
    (flag : U → B → σ) (code : B ↪ Fin (2^r))

private noncomputable def digit (u : U) (j : Fin r) : Expr σ :=
  Expr.disjoin (Finset.univ.toList.map fun b =>
    if (numberWords r).symm (code b) j then .input (flag u b) else .const false)

omit [Fintype U] [Fintype σ] in
private theorem digit_size (u : U) (j : Fin r) : (digit flag code u j).size ≤ 2*Fintype.card B+1 := by
  apply (Expr.size_disjoin_le _ 1 ?_).trans
  · simp [Nat.mul_comm]
  · intro e he
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp he
    split <;> rfl

omit [Fintype U] [Fintype σ] in
private theorem digit_eval (x : σ → Bool) (u : U) (b : B)
    (h : ∀ c, x (flag u c) = true ↔ c = b) (j : Fin r) :
    (digit flag code u j).eval x = (numberWords r).symm (code b) j := by
  have single (c : B) :
      ((if (numberWords r).symm (code c) j then Expr.input (flag u c) else .const false).eval x = true) ↔
        (numberWords r).symm (code c) j = true ∧ c = b := by
    cases (numberWords r).symm (code c) j <;> simp [Expr.eval,h]
  apply Bool.eq_iff_iff.mpr
  simp [digit,Expr.eval_disjoin_true,single]

/-- Encode one-hot relative-bin tags independently for each named public row. -/
noncomputable def ordinals : Frame σ (U × Fin r) :=
  (Frame.initial id).step fun uj => digit flag code uj.1 uj.2

/-- The binary representation of a valid tag is the chosen numerical bin code. -/
theorem ordinals_eval (x : σ → Bool) (u : U) (b : B)
    (h : ∀ c, x (flag u c) = true ↔ c = b) (j : Fin r) :
    (ordinals flag code).eval x (u,j) = (numberWords r).symm (code b) j := by
  have hid : (Frame.initial id).eval x = x := funext (Frame.initial_eval id x)
  rw [ordinals, Frame.step_eval, hid]
  exact digit_eval flag code x u b h j

/-- Binary tag computation is linear in row count, with a fixed finite-bin factor. -/
theorem ordinals_size : (ordinals flag code).size ≤ Fintype.card U*r*(2*Fintype.card B+1) := by
  simpa only [ordinals,Frame.initial_size,zero_add,Fintype.card_prod,Fintype.card_fin] using
    Frame.step_size_le (Frame.initial (id : σ → σ))
      (fun uj : U × Fin r => digit flag code uj.1 uj.2) _ (fun uj => digit_size flag code uj.1 uj.2)

variable (active : U → σ) (tile : U → ProductSlots q l → σ) (width : U → Fin w → σ)

private def codedPins : Pins U (σ ⊕ (U × Fin r)) (r+keyWidth q l) w :=
  tilePins (Sum.inl ∘ active) (fun u => Sum.inl ∘ tile u) (fun u j => .inr (u,j))
    (fun u => Sum.inl ∘ width u)

/-- Complete histogram from the moved tile and one-hot relative classifier. -/
noncomputable def fromRows : Frame σ (((Fin q → Deck l) × B) × Fin w) :=
  (frame (codedPins (r := r) active tile width) (tileBinCode q l code)).subst
    (ordinals flag code).withInput

/-- Work is linear in public rows and legal tile-bin pairs times a polynomial
in sort depth and binary widths. The tag lookup never scans the tiles. -/
theorem fromRows_size :
    let n := Fintype.card U + Fintype.card (Fin q → Deck l)*Fintype.card B
    (fromRows flag code active tile width).size ≤ Fintype.card U*r*(2*Fintype.card B+1) +
      2*(n+1)*laneCost (Nat.clog 2 n) (r+keyWidth q l) w := by
  intro n
  rw [fromRows,Frame.subst_size,Frame.withInput_size]
  exact Nat.add_le_add (ordinals_size flag code) (tileFrame_size _ _ _ _ _)

variable {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)
    (bin : N.Edge → Option ((Fin q → Deck l) × B)) (slot : N.Edge ↪ U)

/-- The one-hot batch computes the population used by every direction pool. It
requires no tag, geometric or width field to be meaningful on inactive rows. -/
theorem fromRows_count (x : σ → Bool)
    (enabled : ∀ e, x (active (slot e)) = (bin e).isSome)
    (empty : ∀ u, u ∉ Set.range slot → x (active u) = false)
    (tileWord : ∀ e a, bin e = some a → x ∘ tile (slot e) = productWires l a.1)
    (tag : ∀ e a, bin e = some a → ∀ c, x (flag (slot e) c) = true ↔ c = a.2)
    (widthWord : ∀ e a, bin e = some a → value (x ∘ width (slot e)) = N.width e)
    (fits : ∀ a, SeedIntervals.count N bin a < 2^w) (a : (Fin q → Deck l) × B) :
    value (fun j => (fromRows flag code active tile width).eval x (a,j)) = SeedIntervals.count N bin a := by
  simp only [fromRows,Frame.subst_eval]
  refine tileFrame_count N bin slot (Sum.inl ∘ active) (fun u => Sum.inl ∘ tile u)
    (fun u j => Sum.inr (u,j)) (fun u => Sum.inl ∘ width u) code
    ((ordinals flag code).withInput.eval x) ?_ ?_ ?_ ?_ ?_ fits a
  · simpa only [Function.comp_apply,Frame.withInput_eval_inl] using enabled
  · simpa only [Function.comp_apply,Frame.withInput_eval_inl] using empty
  · simpa only [Function.comp_def,Frame.withInput_eval_inl] using tileWord
  · intro e b hb
    funext j
    rw [Function.comp_apply, Frame.withInput_eval_inr, ordinals_eval flag code x (slot e) b.2 (tag e b hb)]
  · simpa only [Function.comp_def,Frame.withInput_eval_inl] using widthWord

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
