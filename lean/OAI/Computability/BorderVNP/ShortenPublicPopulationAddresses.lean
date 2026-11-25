import OAI.Computability.BorderVNP.ShortenPublicPopulationNamed

/-! # Numeric moved-bin words at stable old cable names

The original input is retained, so active, occupied, sign, endpoint and width
fields can be read by the prefix allocator. The finite relative tag is encoded
once per row and appended to its canonical tile wires by pure reindexing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit ParseBatchCounts ParseBatchLookup ParseBatchSort PackedHistogram
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {U σ : Type*} {I B : Type} {q l r w D : ℕ}
    (enum : Fin q ≃ I) (code : B ↪ Fin (2^r))

/-- The canonical sparse numerical address of an allocator bin in the original factor order. -/
noncomputable def addressCode : ((I → Deck l) × B) ↪ Fin (2^(r+keyWidth q l)) :=
  (indexBins enum).toEmbedding.trans (tileBinCode q l code)

variable [Fintype U] [Fintype B] [Fintype σ] (rows : Frame σ (U × (ProductSlots q l ⊕ B)))

private noncomputable def encodeRows : Frame σ ((σ ⊕ (U × (ProductSlots q l ⊕ B))) ⊕ U × Fin r) :=
  ((ordinals (fun u b => Sum.inr (u,Sum.inr b)) code).withInput).subst rows.withInput

/-- Append the relative ordinal to the moved tile key and retain all original inputs. -/
noncomputable def addressFrame : Frame σ (σ ⊕ U × Fin (r+keyWidth q l)) :=
  (encodeRows code rows).select (Sum.elim (Sum.inl ∘ Sum.inl) (fun uj =>
    prepend (fun b => Sum.inl (Sum.inr (uj.1,Sum.inl ((keySlots q l).symm b))))
      (fun j => Sum.inr (uj.1,j)) uj.2))

/-- The only additional gates encode the finite relative-bin alphabet. -/
theorem addressFrame_size : (addressFrame code rows).size ≤ rows.size + Fintype.card U*r*(2*Fintype.card B+1) := by
  simp only [addressFrame,Frame.select_size,encodeRows,Frame.subst_size,Frame.withInput_size]
  exact Nat.add_le_add_left (ordinals_size _ _) _

/-- Original input fields retain their wire values. -/
theorem addressFrame_input (x : σ → Bool) (i : σ) : (addressFrame code rows).eval x (.inl i) = x i := by
  simp [addressFrame,encodeRows]

/-- The numerical key emitted at a valid cable's stable name is the canonical
encoding of its geometric bin. Other rows may contain arbitrary metadata. -/
theorem addressFrame_key (x : σ → Bool) (u : U) (a : (I → Deck l) × B)
    (ht : ∀ j, rows.eval x (u,Sum.inl j) = productWires l (a.1 ∘ enum) j)
    (hb : ∀ b, rows.eval x (u,Sum.inr b) = true ↔ b = a.2) :
    value (fun j => (addressFrame code rows).eval x (.inr (u,j))) = (addressCode enum code a).val := by
  let E := (encodeRows code rows).eval x
  have hrel (j : Fin r) : E (.inr (u,j)) = (numberWords r).symm (code a.2) j := by
    dsimp only [E,encodeRows]
    rw [Frame.subst_eval,Frame.withInput_eval_inr]
    apply ordinals_eval
    simpa only [Frame.withInput_eval_inr] using hb
  have htile (j : Fin (keyWidth q l)) : E (.inl (.inr (u,.inl ((keySlots q l).symm j)))) =
      keyWord q l (a.1 ∘ enum) j := by
    simp only [E,encodeRows,Frame.subst_eval,Frame.withInput_eval_inl,Frame.withInput_eval_inr]
    exact ht _
  change value _ = value (prepend _ _)
  apply congrArg value
  funext j
  simp only [addressFrame,Frame.select_eval,Sum.elim_inr]
  let Mid := (σ ⊕ U × (ProductSlots q l ⊕ B)) ⊕ U × Fin r
  let high : Fin (keyWidth q l) → Mid := fun t => Sum.inl (Sum.inr (u,Sum.inl ((keySlots q l).symm t)))
  let low : Fin r → Mid := fun t => Sum.inr (u,t)
  change E (prepend high low j) = _
  exact (congrFun (prepend_map E high low) j).trans (by
    rw [show E ∘ high = keyWord q l (a.1 ∘ enum) from funext htile,
      show E ∘ low = (numberWords r).symm (code a.2) from funext hrel]
    rfl)

/-- Active, numeric address and width pins directly consumable by the sparse prefix directory. -/
def addressedPins {k : ℕ} (active : U → σ) (width : U → Fin w → σ) : Pins U (σ ⊕ U × Fin k) k w where
  active := Sum.inl ∘ active
  key u j := .inr (u,j)
  width u := Sum.inl ∘ width u

variable {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)
    (bin : N.Edge → Option ((I → Deck l) × B)) (slot : N.Edge ↪ U)
    (active : U → σ) (width : U → Fin w → σ) (x : σ → Bool)

/-- The old interval directory's full representation relation, including
absence of unoccupied rows and true old widths on every charged cable. -/
theorem addressFrame_represents
    (enabled : ∀ e, x (active (slot e)) = (bin e).isSome)
    (empty : ∀ u, u ∉ Set.range slot → x (active u) = false)
    (classifies : ∀ e a, bin e = some a →
      (∀ j, rows.eval x (slot e,Sum.inl j) = productWires l (a.1 ∘ enum) j) ∧
        ∀ b, rows.eval x (slot e,Sum.inr b) = true ↔ b = a.2)
    (widthWord : ∀ e a, bin e = some a → value (x ∘ width (slot e)) = N.width e) :
    Represents (addressedPins active width) N bin slot (addressCode enum code) ((addressFrame code rows).eval x) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [addressedPins,Function.comp_apply,addressFrame_input] using enabled
  · simpa only [addressedPins,Function.comp_apply,addressFrame_input] using empty
  · intro e a he
    exact addressFrame_key enum code rows x (slot e) a (classifies e a he).1 (classifies e a he).2
  · simpa only [addressedPins,Function.comp_def,addressFrame_input] using widthWord

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
