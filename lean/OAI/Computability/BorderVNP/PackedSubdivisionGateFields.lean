import OAI.Computability.BorderVNP.PackedSubdivisionGateSource
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews

/-! # Compiling subdivision commands from both genuine incidence address scans -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork

variable {s m np extra C C' d d' k k' w : ℕ} {σ : Type*} [Fintype σ]
variable (old : CellAddressCircuit.Fields s m np C d k w σ)
variable (new : CellAddressCircuit.Fields (s+extra*m) ((extra+1)*m) np C' d' k' w σ)
variable (work extent : Fin s → Fin w → σ) (present : Fin ((extra+1)*m) → σ)

/-- All inputs and shared scan/lookup outputs, retained once for the complete rectangle. -/
abbrev Table (σ : Type*) (s m np extra w : ℕ) :=
  σ ⊕ ((CellAddressViews.View s m np s × Fin w) ⊕
    ((CellAddressViews.View (s+extra*m) ((extra+1)*m) np (s+extra*m) × Fin w) ⊕
      ((End m np × Fin w) ⊕ (End m np × Fin w))))

/-- Share both virtual singleton-cell incidence scans and the two work prefix lookups. -/
noncomputable def table : Frame σ (Table σ s m np extra w) :=
  (parallelFrame (Views.frame old) (parallelFrame (Views.frame new)
    (parallelFrame (Layer.prefixFrame old work) (Layer.prefixFrame old extent)))).withInput

/-- Input pins, output lanes of the old and new address scans, and work fields read at old ends. -/
def tableFields : Fields m np extra d d' w (Table σ s m np extra w) where
  edgeWidth i j := .inl (old.edgeWidth i j)
  portWidth i j := .inl (old.portWidth i j)
  oldPtr e j := .inl (old.ptr e j)
  newPtr e j := .inl (new.ptr e j)
  oldView e j := .inr (.inl (.inl e,j))
  newView e j := .inr (.inr (.inl (.inl e,j)))
  present i := .inl (present i)
  work e j := .inr (.inr (.inr (.inl (e,j))))
  extent e j := .inr (.inr (.inr (.inr (e,j))))

/-- Actual shared operand circuit on the raw public geometry words. -/
noncomputable def inputs : Frame σ (Row m np extra × Layer.Column d' w) :=
  (source (tableFields old new present)).subst (table old new work extent)

/-- Explicit additive charge of the two scans, two batched lookups, and sparse row selectors. -/
theorem inputs_size : (inputs old new work extent present).size ≤
    (Views.frame old).size+((Views.frame new).size+
      ((Layer.prefixFrame old work).size+(Layer.prefixFrame old extent).size))+
    Fintype.card (Row m np extra)*(1+d'+6*w)*(30*(d+w)+18) := by
  simpa [inputs,table,Frame.subst_size] using
    Nat.add_le_add_left (source_size (tableFields old new present)) (table old new work extent).size

/-- The returned equality rows contain all nine serialized words with their relocation
tags, their active bits, and the live endpoint's owner in the successor site directory. -/
theorem emit_subdivision :
    ∃ f : Frame σ (Row m np extra × (Unit ⊕ (Fin d' ⊕ Fin 9 × Fin w))),
      f.size ≤ (inputs old new work extent present).size+1+Fintype.card (Row m np extra)*(4500*(w+1)^2) ∧
      (∀ x r, f.eval x (r,.inl ()) = (inputs old new work extent present).eval x (r,.inl ())) ∧
      (∀ x r j, f.eval x (r,.inr (.inl j)) = (inputs old new work extent present).eval x (r,.inr (.inl j))) ∧
      ∀ (x : σ → Bool) (r : Row m np extra),
        let arg := values (tableFields old new present) ((table old new work extent).eval x) r
        1 < 2^w → arg .work+(arg .oldBase+arg .clip)<2^w → arg .extent+arg .newBase<2^w →
        List.ofFn (fun i => (Layer.kind i,value (fun j => f.eval x (r,.inr (.inr (i,j)))))) = marked (Layer.command arg) := by
  obtain ⟨f,hf,ha,ho,hw⟩ := Layer.emit d' w (inputs old new work extent present)
  refine ⟨f,hf,ha,ho,?_⟩
  intro x r arg h1 hl hr
  have he : (fun a => value (fun j => (inputs old new work extent present).eval x (r,.inr (.inr (a,j))))) = arg := by
    funext a
    simpa only [inputs,Frame.subst_eval] using source_value (tableFields old new present) r a
      ((table old new work extent).eval x)
  have fields := hw x r
  dsimp only at fields
  rw [he] at fields
  have v (a : Layer.Arg) : value (fun j => (inputs old new work extent present).eval x (r,.inr (.inr (a,j)))) = arg a := congrFun he a
  apply fields h1
  · simpa only [v] using hl
  · simpa only [v] using hr

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
