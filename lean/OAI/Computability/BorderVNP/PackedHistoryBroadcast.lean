import OAI.Computability.BorderVNP.PackedHistoryOuter

/-! # Actual reserved broadcast positions for the adaptive profile history

Child transcripts are consecutive, in child order, followed by the local
profile pins in the supplied directory order. The unused tail of the reserved
bank is forced to zero. The exact outer history index is therefore equivalent
to a passing physical word in the auxiliary field of the evaluation header.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Packing VPVNP.VerifierNetwork

/-- Length of the concatenation of the child transcripts and local pin words. -/
def broadcastWidth (k : ℕ) (width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => k*broadcastWidth k width n + width n

/-- Child-major recursive numbering of physical profile slots. The ordering of
each node's own fixed pins is supplied by its actual site descriptor. -/
def broadcastOrder {G : ℕ → Type} (k : ℕ) (width : ℕ → ℕ) (order : ∀ j, G j ≃ Fin (width j)) :
    (n : ℕ) → Slot k G n ≃ Fin (broadcastWidth k width n)
  | 0 => ⟨Empty.elim,Fin.elim0,(fun j => nomatch j),(fun j => Fin.elim0 j)⟩
  | n+1 =>
    let children := ((Equiv.refl (Fin k)).prodCongr (broadcastOrder k width order n)).trans finProdFinEquiv
    (children.sumCongr (order n)).trans finSumFinEquiv

/-- Exact active width used by the packed-history circuit's accounting theorem. -/
theorem broadcastWidth_eq_card {G : ℕ → Type} [∀ j, Fintype (G j)] (k : ℕ) (width : ℕ → ℕ)
    (order : ∀ j, G j ≃ Fin (width j)) (n : ℕ) :
    broadcastWidth k width n = Fintype.card (Slot k G n) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (broadcastOrder k width order n)).symm

variable {α : Type*} {active reserve : ℕ}

/-- Place the actual bit at its directory position and force every unused slot to zero. -/
def paddedProfile (order : α ≃ Fin active) (bits : α → Bool) (i : Fin reserve) : Bool :=
  if h : i.val < active then bits (order.symm ⟨i.val,h⟩) else false

/-- Recover active bits from their assigned physical positions. -/
def readProfile (order : α ≃ Fin active) (fit : active ≤ reserve) (word : Fin reserve → Bool) : α → Bool :=
  fun i => word ((order i).castLE fit)

/-- Accept exactly the flag-tested active profile with a canonically zero padding tail. -/
def validProfile (order : α ≃ Fin active) (fit : active ≤ reserve) (ok : (α → Bool) → Prop)
    (word : Fin reserve → Bool) : Prop :=
  ok (readProfile order fit word) ∧ ∀ i, active ≤ i.val → word i = false

/-- Padded physical bank words satisfying the flag and padding test have exactly
the same valid choices as the original active slot bank. -/
def acceptedPadded (order : α ≃ Fin active) (fit : active ≤ reserve) (ok : (α → Bool) → Prop) :
    {bits : α → Bool // ok bits} ≃ {word : Fin reserve → Bool // validProfile order fit ok word} := by
  have rd (bits : α → Bool) : readProfile order fit (paddedProfile order bits) = bits := by
    funext i
    simp only [readProfile,paddedProfile,Fin.val_castLE,dite_eq_left (order i).isLt,Fin.eta,Equiv.symm_apply_apply]
  refine ⟨fun b => ⟨paddedProfile order b.val,(rd b.val).symm ▸ b.property,fun i hi => dite_eq_right (not_lt.mpr hi)⟩,
    fun w => ⟨readProfile order fit w.val,w.property.1⟩,fun b => Subtype.ext (rd b.val),fun w => ?_⟩
  apply Subtype.ext
  funext i
  by_cases h : i.val < active
  · simp [paddedProfile,readProfile,h]
  · exact (dite_eq_right h).trans (w.property.2 i (Nat.le_of_not_gt h)).symm

/-- Convert any checked history equivalence, including one obtained by restricting
the physical states to their width capacities, to the same reserved broadcast bank. -/
def acceptedBroadcastOfEquiv {I : Type*} (order : α ≃ Fin active) (fit : active ≤ reserve)
    (ok : (α → Bool) → Prop) (checked : I ≃ {bits : α → Bool // ok bits}) :
    I ≃ {word : Fin reserve → Bool // validProfile order fit ok word} :=
  checked.trans (acceptedPadded order fit ok)

variable {K T : ℕ} {A : ℕ → Type*} {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
  {σ : Type*} [Fintype σ]

/-- Each genuine dependent outer pack history corresponds to exactly one accepted
fixed-width physical broadcast word. The flag is the actual compiled outer circuit's
test on the child-major ordering, including all the local epoch checks. -/
noncomputable def acceptedOuterBroadcast (bottom : A 0) (epoch : ∀ j, (Fin K → A j) → ProfileSum (A (j+1)))
    (C : Codec (outerSystem T epoch) G) (rep : Represents A W) (step : Steps K T W G)
    (correct : LocalCorrect C rep step) (f : Frame σ (W 0)) (x : σ → Bool) (hx : rep 0 (f.eval x) bottom)
    (width : ℕ → ℕ) (order : ∀ j, G j ≃ Fin (width j)) (fit : broadcastWidth K width T ≤ reserve) :
    (packHistory bottom epoch T).Index ≃
      {word : Fin reserve → Bool // validProfile (broadcastOrder K width order T) fit
        (fun g => flag step T le_rfl (repeatLeaf K f T) x g = true) word} :=
  acceptedBroadcastOfEquiv _ fit _ (acceptedOuter bottom epoch C rep step correct f x hx)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
