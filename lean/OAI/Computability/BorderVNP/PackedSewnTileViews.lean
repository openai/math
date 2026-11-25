import OAI.Computability.BorderVNP.PackedSewnTileFragments
import OAI.Computability.BorderVNP.PackedRoutingWideFields
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Real singleton incidence columns for the six tile fragment slots

The two public site-local address scans run on the shared previous and
sewn endpoint columns. The owner is read through the old port pointer,
including zero extension to the common scalar width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment.Tile

open CellAddressCircuit CellAddressViews Inherited Crossing ParseBatchSort VPVNP.VerifierNetwork

variable {γ σ τ : Type*} [Fintype γ] [Fintype σ] [Fintype τ]
variable {s old p m n C C' d d' k k' w : ℕ}

/-- Shared upstream pins followed by the two virtual singleton-cell view tables. -/
abbrev Banks (γ : Type*) (s old p m n w : ℕ) :=
  γ ⊕ ((View s old p s × Fin w) ⊕ (View s m n s × Fin w))

variable (F : Fields s old p C d k w σ) (B : Fields s m n C' d' k' w τ)
variable (oldPin : σ → γ) (newPin : τ → γ)

/-- Gather both virtual singleton-cell passes on the same shared upstream pins. -/
noncomputable def physicalBase : Frame γ (Banks γ s old p m n w) :=
  (parallelFrame ((Views.frame F).subst (Frame.initial oldPin)) ((Views.frame B).subst (Frame.initial newPin))).withInput

/-- Actual physical sources of the four frozen fragment words. -/
def physicalFields (hd : d≤w) (zero : γ) : Inputs (Banks γ s old p m n w) p m n w where
  owner a j := .inl (widthPins hd zero (oldPin ∘ F.ptr (.inr a)) j)
  oldStart a j := .inr (.inl (.inl (.inr a),j))
  newStart e j := .inr (.inr (.inl e,j))

/-- The old owner word on the actual joined input. -/
theorem physical_owner (hd : d≤w) (zero : γ) (x : γ → Bool) (hz : x zero=false) (a : Fin p) :
    value ((physicalBase F B oldPin newPin).eval x ∘ (physicalFields (m:=m) (n:=n) F oldPin hd zero).owner a) =
      value (x ∘ oldPin ∘ F.ptr (.inr a)) := by
  have e : ((physicalBase F B oldPin newPin).eval x ∘ (physicalFields (m:=m) (n:=n) F oldPin hd zero).owner a) =
      x ∘ widthPins hd zero (oldPin ∘ F.ptr (.inr a)) := by funext j; simp [physicalFields,physicalBase]
  rw [e,widthPins_value hd zero _ x hz]

/-- The old slot is an address in the original site's one-copy slab. -/
theorem physical_oldStart (hd : d≤w) (zero : γ) (x : γ → Bool) (a : Fin p) :
    value ((physicalBase F B oldPin newPin).eval x ∘ (physicalFields (m:=m) (n:=n) F oldPin hd zero).oldStart a) =
      value (fun j => (Views.frame F).eval (x ∘ oldPin) (.inl (.inr a),j)) := by
  apply congrArg value
  funext j
  simp [physicalBase,physicalFields,Frame.subst_eval]
  rw [show (Frame.initial oldPin).eval x = x ∘ oldPin from funext (Frame.initial_eval oldPin x)]

/-- Every chosen new source uses its true singleton-cell incidence column. -/
theorem physical_newStart (hd : d≤w) (zero : γ) (x : γ → Bool) (e : End m n) :
    value ((physicalBase F B oldPin newPin).eval x ∘ (physicalFields (m:=m) (n:=n) F oldPin hd zero).newStart e) =
      value (fun j => (Views.frame B).eval (x ∘ newPin) (.inl e,j)) := by
  apply congrArg value
  funext j
  simp [physicalBase,physicalFields,Frame.subst_eval]
  rw [show (Frame.initial newPin).eval x = x ∘ newPin from funext (Frame.initial_eval newPin x)]

/-- The complete source of frozen tile fragments after the common geometry
state. Old and new coordinate fields may be wired to different subbanks. -/
noncomputable def physicalFrame {slots : ℕ} (hd : d≤w) (zero : γ) (rows : Fin slots → Option (Item p m n)) :
    Frame γ (Pin slots w) :=
  (frame (physicalFields F oldPin hd zero) rows).subst (physicalBase F B oldPin newPin)

theorem physicalFrame_eval {slots : ℕ} (hd : d≤w) (zero : γ) (rows : Fin slots → Option (Item p m n))
    (x : γ → Bool) :
    (physicalFrame F B oldPin newPin hd zero rows).eval x =
      (frame (physicalFields F oldPin hd zero) rows).eval ((physicalBase F B oldPin newPin).eval x) :=
  funext (Frame.subst_eval _ _ x)

/-- Both public singleton scans are shared across all tile slots. -/
theorem physicalFrame_size {slots : ℕ} (hd : d≤w) (zero : γ) (rows : Fin slots → Option (Item p m n)) :
    (physicalFrame F B oldPin newPin hd zero rows).size ≤
      (Views.frame F).size+(Views.frame B).size+slots*(2+4*w)*(16*w+22) := by
  simp only [physicalFrame,Frame.subst_size,physicalBase,Frame.withInput_size,parallelFrame_size,Frame.initial_size,zero_add]
  have bound := frame_size (physicalFields F oldPin hd zero) rows
  omega

/-- Exactly the genuine positive intervals survive the fixed rectangle. -/
theorem physicalFrame_active {slots : ℕ} (hd : d≤w) (zero : γ) (rows : Fin slots → Option (Item p m n))
    (x : γ → Bool) (i : Fin slots) :
    active ((physicalFrame F B oldPin newPin hd zero rows).eval x) i = true ↔ ∃ a, rows i=some a ∧ 0<a.span := by
  rw [physicalFrame_eval,active_iff]

/-- A populated physical row reads the parsed data of its actual input banks. -/
theorem physicalFrame_parse {slots : ℕ} (hd : d≤w) (zero : γ) (rows : Fin slots → Option (Item p m n))
    (x : γ → Bool) {i : Fin slots} {a : Item p m n} (row : rows i=some a)
    (fits : (physicalFields F oldPin hd zero).Fits ((physicalBase F B oldPin newPin).eval x) a) :
    parse ((physicalFrame F B oldPin newPin hd zero rows).eval x) i =
      (physicalFields F oldPin hd zero).parsed ((physicalBase F B oldPin newPin).eval x) a := by
  rw [physicalFrame_eval]
  exact parse_eq _ _ _ row fits

end Packing.SewnField.Fragment.Tile

end BorderVNP
end Computability
end OAI
