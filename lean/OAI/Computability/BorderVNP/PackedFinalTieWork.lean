import OAI.Computability.BorderVNP.PackedFinalTiePhysical
import OAI.Computability.BorderVNP.PackedInheritedExtent

/-! # Reading final work prefixes from the returned geometry itself

The terminal geometry publishes each full staging extent. Subtracting its
site's true incoming width recovers the work prefix for final ties directly
on those output pins, including sites with an empty private or incoming part.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity ParseBatchSort VPVNP.VerifierNetwork
open CellAddressCircuit CellAddressPhysical CellAddresses Word Subdivision.Gates
open scoped Classical

variable {s m np C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m np C d k w σ)

private noncomputable def workSource : Frame σ (Fin s × Bool × Fin w) :=
  (Views.frame F).withInput.select fun z =>
    if z.2.1 then .inr (.inr (.inr (2,z.1)),z.2.2) else .inl (F.auxWidth z.1 z.2.2)

/-- Recover all work widths from the full extents and virtual incidence markers on the same geometry. -/
theorem recover :
    ∃ f : Frame σ (Fin s × Fin w), f.size ≤ (Views.frame F).size+1+s*3*(100*(w+1)^2) ∧
      ∀ x i, value (fun j => f.eval x (i,j)) =
        value (x ∘ F.auxWidth i) - value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j)) := by
  let expr : WidthExpr Bool := .binary .sub (.field false) (.field true)
  obtain ⟨f,hs,he⟩ := WorkWords.exists_words (workSource F) id (fun _ => expr)
  refine ⟨f,?_,?_⟩
  · simpa [workSource,expr,WidthExpr.nodes] using hs
  · intro x i
    let a := fun t => value (fun j => (workSource F).eval x (i,t,j))
    have ha : a false = value (x ∘ F.auxWidth i) := by simp [a,workSource,Function.comp_def]
    have hb : a true = value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j)) := by simp [a,workSource]
    have fit : expr.Fits w a := ⟨value_lt _,value_lt _,(Nat.sub_le _ _).trans_lt (value_lt _)⟩
    have eval : expr.eval a = a false-a true := rfl
    exact (he x i fit).trans (eval.trans (congrArg₂ Nat.sub ha hb))

/-- Raw geometry pins retained beside the recovered site work words. -/
def retained : Fields s m np C d k w (σ ⊕ (Fin s × Fin w)) where
  sites := F.sites
  cells := F.cells
  owner u j := .inl (F.owner u j)
  ptr u j := .inl (F.ptr u j)
  edgeWidth u j := .inl (F.edgeWidth u j)
  auxWidth u j := .inl (F.auxWidth u j)
  portWidth u j := .inl (F.portWidth u j)

/-- The work-pin prefix leaves all geometry representations available in the same frame. -/
theorem retained_rep {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (aux : N.Site → ℕ) (sites : N.Site ↪ Fin s) (edges : N.Edge ↪ Fin m)
    (ports : P ↪ Fin np) (f : Frame σ (Fin s × Fin w)) (x : σ → Bool)
    (rep : Represents N cell aux sites edges ports F x) :
    Represents N cell aux sites edges ports (retained F) (f.withInput.eval x) := by
  constructor
  all_goals first
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.owner
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.src
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.dst
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.attach
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.edge
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.stage
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.port
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.edgeHole
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.stageHole
    | simpa only [retained,Function.comp_def,Frame.withInput_eval_inl] using rep.portHole

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (state : N.Site → Site)
    (sites : N.Site ↪ Fin s) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin np)
    {x : σ → Bool}

/-- On every represented final network the recovered prefix is the current program's exact work size. -/
theorem recover_value (rep : Represents N cell (fun u => (state u).size) sites edges ports F x)
    (hin : ∀ v, (state v).incoming = incoming N v)
    (f : Frame σ (Fin s × Fin w)) (hf : ∀ i, value (fun j => f.eval x (i,j)) =
      value (x ∘ F.auxWidth i)-value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j))) :
    WorkWords.Covers sites (fun u => (state u).work) f x := by
  have h := Views.EndpointData.of_rep N F sites edges ports rep
  have fit (v : N.Site) : incoming N v < 2^w := by
    rw [← hin v]
    exact (Nat.le_add_left (state v).incoming (state v).work).trans_lt
      ((rep.stage v).symm.trans_lt (value_lt _))
  constructor
  · intro v
    rw [hf,rep.stage,Views.input_size N F sites edges ports h fit,← hin v,Site.size,Nat.add_sub_cancel]
  · intro i hi
    rw [hf,rep.stageHole i hi,Nat.zero_sub]

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
