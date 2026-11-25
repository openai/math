import OAI.Computability.BorderVNP.PackedInheritedWorkSewnStage
import OAI.Computability.BorderVNP.PackedRoutingWideFields

/-! # The physical private-program staging widths on the sewn network

The exterior sewing stage replaces every surviving site's incident ports.
Its private prefix is the retained program's complete former extent. The
new extent adds the true current cable and external-port lanes. The joined
source evaluates the old geometry once and forwards the newly scanned sizes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.CellAddressCircuit Packing.CellAddressPhysical
open Crossing ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {σ Γ : Type} [Fintype σ] [Fintype Γ] {s m n C d k w : ℕ}
    (F : Fields s m n C d k w (σ ⊕ Bool)) (src : Frame Γ (σ ⊕ Bool))

/-- Current public fields, the final private staging extent per site, and the
original shared Boolean constants of the terminal geometry. -/
abbrev StagedWires (σ : Type) (s w : ℕ) := (σ ⊕ (Fin s × Fin w)) ⊕ Bool

private def oldWire : σ ⊕ Bool → StagedWires σ s w := Sum.map Sum.inl id

/-- One evaluation of the sewn routing source followed by the shared
per-site incidence scan. The constant wires remain available for controls. -/
noncomputable def stagedSource : Frame Γ (StagedWires σ s w) :=
  (((sewnExtent F (Frame.initial (id : σ ⊕ Bool → _))).withInput).select
    (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr))).subst src

private theorem staged_old (x : Γ → Bool) (z : σ ⊕ Bool) :
    (stagedSource F src).eval x (oldWire z) = src.eval x z := by
  cases z <;> simp [oldWire,stagedSource]

/-- The staged field bus forwards both original constant inputs verbatim. -/
theorem staged_constant (x : Γ → Bool) (b : Bool) :
    (stagedSource F src).eval x (.inr b) = src.eval x (.inr b) := staged_old F src x (.inr b)

/-- The scanned extent word is the one read from the original native
branch's shared source assignment. -/
theorem staged_word (x : Γ → Bool) (i : Fin s) (j : Fin w) :
    (stagedSource F src).eval x (.inl (.inr (i,j))) = (sewnExtent F src).eval x (i,j) := by
  have eq : (Frame.initial (id : σ ⊕ Bool → _)).eval (src.eval x) = src.eval x := funext fun _ => Frame.initial_eval ..
  simp [stagedSource,sewnExtent,Frame.subst_eval,eq]

/-- Only the staging column is changed. All remaining columns refer to the
real previous fields, including the updated exterior edges and attachments. -/
def stagedFields : Fields s m n C d k w (StagedWires σ s w) where
  sites := F.sites
  cells := F.cells
  owner i := oldWire ∘ F.owner i
  ptr e := oldWire ∘ F.ptr e
  edgeWidth i := oldWire ∘ F.edgeWidth i
  auxWidth i j := .inl (.inr (i,j))
  portWidth i := oldWire ∘ F.portWidth i

/-- The real scanned source costs one use of the terminal source plus one
near-linear pass on the current sparse sewn rows. -/
theorem staged_cost (F : Fields s m n C w k w (σ ⊕ Bool)) {R W : ℕ}
    (rows : 1+count s m n s ≤ R) (width : w≤W) (depth : Nat.clog 2 R ≤ W) :
    (stagedSource F src).size ≤ src.size+4000*R*(W+1)^3 := by
  have charge := sewnExtent_cubic (source := Frame.initial (id : σ ⊕ Bool → _)) F rows width depth
  simpa only [Frame.initial_size,zero_add,stagedSource,Frame.subst_size,Frame.select_size,Frame.withInput_size] using
    (Nat.add_le_add_left charge src.size)

/-- The complete signed/field packet estimator can charge this scan to
the same fixed routing-row count, even if there are more sites than cells. -/
theorem staged_routing_cost (F : Fields s m n C w k w (σ ⊕ Bool)) {R W : ℕ}
    (rows : 1+count s m n C ≤ R) (width : w≤W) (depth : Nat.clog 2 R ≤ W) :
    (stagedSource F src).size ≤ src.size+432000*R*(W+1)^3 := by
  have range : 1+count s m n s ≤ 4*R := by unfold count at *; omega
  have bound : R ≤ 2^W := (Nat.le_pow_clog (by decide : 1<2) R).trans (Nat.pow_le_pow_right (by decide) depth)
  have enlarged : 4*R ≤ 2^(W+2) := by rw [pow_add,show (2:ℕ)^2=4 by decide,Nat.mul_comm (2^W) 4]; exact Nat.mul_le_mul_left 4 bound
  have log := (Nat.clog_mono_right 2 enlarged).trans (by rw [Nat.clog_pow _ _ (by decide : 1<2)])
  have work := staged_cost (src:=src) F range (width.trans (Nat.le_add_right W 2)) log
  have p : ((W+2)+1)^3 ≤ (3*(W+1))^3 := Nat.pow_le_pow_left (by omega) 3
  apply work.trans (Nat.add_le_add_left _ _)
  calc
    4000*(4*R)*((W+2)+1)^3 ≤ 4000*(4*R)*(3*(W+1))^3 := Nat.mul_le_mul_left _ p
    _ = 432000*R*(W+1)^3 := by ring

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (site : N.Site ↪ Fin s) (edge : N.Edge ↪ Fin m) (port : P ↪ Fin n)
    (cell : N.Site → Fin C) (state : N.Site → Site) (runs : N.Site → List SewnField.Interval) (x : Γ → Bool)

/-- Every final slot, occupied or vacant, represents the actual adapted
private program on this sewn physical network. -/
theorem staged_represents (rep : CellAddressPhysical.Represents N cell (fun v => (state v).size) site edge port F (src.eval x))
    (room : ∀ v, (state v).size+incoming N v < 2^w) :
    CellAddressPhysical.Represents N cell (fun v => (SewnField.stage (state v) (incoming N v) (runs v)).size)
      site edge port (stagedFields F) ((stagedSource F src).eval x) := by
  have extent := sewnExtent_covers F src N site edge port cell state runs x rep room
  constructor
  all_goals simp only [stagedFields,Function.comp_def,staged_old,staged_word]
  exacts [rep.owner,rep.src,rep.dst,rep.attach,rep.edge,extent.live,rep.port,rep.edgeHole,extent.hole,rep.portHole]

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
