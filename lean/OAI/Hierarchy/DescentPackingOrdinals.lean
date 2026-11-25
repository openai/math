import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Stable stream ordinals for actual grouped matching occurrences -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section

/-- Concatenate the units of every chronological record in its supplied order. -/
def orderedUnits {I : Type*} [Fintype I] (width rank : I→ℕ) (inj : Function.Injective rank) :
    (Σ i,Fin (width i)) ≃ Fin (Fintype.card (Σ i,Fin (width i))) :=
  (ProtocolRAMPortRanks.enumerate width rank inj).trans (finCongr (by simp [Fintype.card_sigma]))

@[simp] theorem orderedUnits_val {I : Type*} [Fintype I] (width rank : I→ℕ) (inj : Function.Injective rank)
    (i : I) (j : Fin (width i)) : (orderedUnits width rank inj ⟨i,j⟩).val =
      ProtocolRAMPortRanks.«prefix» width rank i+j.val := rfl

/-- Enumerate site / destination / unit in that order. The two offsets determine
the original site, the precise destination and the local ordinal. -/
def orderedNested {I J : Type*} [Fintype I] [Fintype J]
    (width : I→J→ℕ) (rank : I→ℕ) (order : J→ℕ)
    (inj : Function.Injective rank) (distinct : Function.Injective order) :
    (Σ i,Σ j,Fin (width i j)) ≃ Fin (Fintype.card (Σ i,Σ j,Fin (width i j))) :=
  let inner := fun i=>orderedUnits (width i) order distinct
  let shape := fun i=>Fintype.card (Σ j,Fin (width i j))
  let rows := Equiv.sigmaCongrRight inner
  (rows.trans (orderedUnits shape rank inj)).trans (finCongr (Fintype.card_congr rows).symm)

@[simp] theorem orderedNested_val {I J : Type*} [Fintype I] [Fintype J]
    (width : I→J→ℕ) (rank : I→ℕ) (order : J→ℕ)
    (inj : Function.Injective rank) (distinct : Function.Injective order)
    (i : I) (j : J) (u : Fin (width i j)) :
    (orderedNested width rank order inj distinct ⟨i,j,u⟩).val =
      ProtocolRAMPortRanks.«prefix» (fun a=>Fintype.card (Σ b,Fin (width a b))) rank i+
      (ProtocolRAMPortRanks.«prefix» (width i) order j+u.val) := rfl

end
end Hierarchy.DescentPacking

end OAI
