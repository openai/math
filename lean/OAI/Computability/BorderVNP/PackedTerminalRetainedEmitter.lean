import OAI.Computability.BorderVNP.PackedTerminalRoutingReturn
import OAI.Computability.BorderVNP.PackedRoutingControls

/-! # Terminal routing and packet output with the separately retained chronological tape

The canonical routing outputs depend on the terminal field bus. The complete cell
packet also reads the saved public history. Both buses are evaluated on the same
native input before the routing fields and packet programs are joined.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open Crossing Packing Packing.CellAddressCircuit Packing.RoutingOutputs GeometryFrameEncoding VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {Z H Γ A : Type*} [Fintype Z] [Fintype H] [Fintype Γ] [Fintype A]
variable {s m n C d k w J P o u v : ℕ}

/-- Lift a field computation by wiring all its primary inputs to the first
part of the common terminal bus. This adds no gates. -/
noncomputable def lift (f : Frame Z A) : Frame (Z ⊕ H) A := f.subst (Frame.initial Sum.inl)

@[simp] theorem lift_size (f : Frame Z A) : (lift (H := H) f).size = f.size := by simp [lift]

@[simp] theorem lift_eval (f : Frame Z A) (z : Z → Bool) (h : H → Bool) (i : A) :
    (lift f).eval (Sum.elim z h) i = f.eval z i := by
  have eqn : (Frame.initial (Sum.inl : Z → Z ⊕ H)).eval (Sum.elim z h) = z := by funext j; simp
  simp only [lift,Frame.subst_eval,eqn]

/-- Hold only the additional pins fixed in the evaluation lemma. The emitted
program itself always reads them from its actual separately retained tape. -/
noncomputable def atExtra (f : Frame (Z ⊕ H) A) (h : H → Bool) : Frame Z A :=
  f.subst ((Frame.initial (id : Z → Z)).step (Sum.elim StatementCircuit.Expr.input (StatementCircuit.Expr.const ∘ h)))

@[simp] theorem atExtra_eval (f : Frame (Z ⊕ H) A) (h : H → Bool) (z : Z → Bool) (i : A) :
    (atExtra f h).eval z i = f.eval (Sum.elim z h) i := by
  have eqn : ((Frame.initial (id : Z → Z)).step (Sum.elim StatementCircuit.Expr.input (StatementCircuit.Expr.const ∘ h))).eval z = Sum.elim z h := by
    funext p; cases p <;> simp [StatementCircuit.Expr.eval]
  simp only [atExtra,Frame.subst_eval,eqn]

private theorem prepended {l : ℕ} (f : Frame Z (Fin l × Fin w)) (rest : Frame (Z ⊕ H) (Outputs o w))
    (r : Frame Z (Outputs o w)) (z : Z → Bool) (h : H → Bool)
    (same : ∀ j, rest.eval (Sum.elim z h) j = r.eval z j) (i : Outputs (l+o) w) :
    (GeometryOutput.prepend (lift f) rest).eval (Sum.elim z h) i = (GeometryOutput.prepend f r).eval z i := by
  rcases i with ⟨i,j⟩ | ⟨⟩
  · refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp [same]
  · exact (GeometryOutput.prepend_valid ..).trans ((same _).trans (GeometryOutput.prepend_valid ..).symm)

/-- Insert control words as aliases of the two shared constant input wires.
The packet's gate table does not depend on any chosen control address. -/
noncomputable def joinedControls (controls : Fin v → Fin (2^w))
    (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w)) : Frame ((Z ⊕ Bool) ⊕ H) (Outputs (v+o) w) :=
  packet.withInput.select (Sum.elim (fun p => Fin.addCases
    (fun i => Sum.inl (.inl (.inr ((ParseBatchCounts.numberWords w).symm (controls i) p.2))))
    (fun i => Sum.inr (.inl (i,p.2))) p.1) (fun j => Sum.inr (.inr j)))

@[simp] theorem joinedControls_first (controls : Fin v → Fin (2^w)) (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w))
    (z : Z ⊕ Bool → Bool) (h : H → Bool) (i : Fin v) (j : Fin w) :
    (joinedControls controls packet).eval (Sum.elim z h) (.inl (i.castAdd o,j)) = (controlWords controls).eval z (i,j) := by
  simp [joinedControls,controlWords]

@[simp] theorem joinedControls_rest (controls : Fin v → Fin (2^w)) (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w))
    (x : (Z ⊕ Bool) ⊕ H → Bool) (i : Fin o) (j : Fin w) :
    (joinedControls controls packet).eval x (.inl (Fin.natAdd v i,j)) = packet.eval x (.inl (i,j)) := by simp [joinedControls]

@[simp] theorem joinedControls_valid (controls : Fin v → Fin (2^w)) (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w))
    (x : (Z ⊕ Bool) ⊕ H → Bool) :
    (joinedControls controls packet).eval x (.inr ()) = packet.eval x (.inr ()) := by simp [joinedControls]

/-- Public addresses and the length-only control words precede the joined
private packet. The packet can read both current fields and retained rows. -/
noncomputable def privateControls (F : Fields s m n C d k w (Z ⊕ Bool)) (old : Fin J → Fin s)
    (controls : Fin v → Fin (2^w)) (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w)) :
    Frame ((Z ⊕ Bool) ⊕ H) (Outputs ((C+(J+C))+(v+o)) w) :=
  GeometryOutput.prepend (lift (privateViews F old)) (joinedControls controls packet)

theorem privateControls_size (F : Fields s m n C d k w (Z ⊕ Bool)) (old : Fin J → Fin s)
    (controls : Fin v → Fin (2^w)) (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w)) :
    (privateControls F old controls packet).size = (privateViews F old).size+packet.size := by
  simp [privateControls,joinedControls]

theorem privateControls_eval (F : Fields s m n C d k w (Z ⊕ Bool)) (old : Fin J → Fin s)
    (controls : Fin v → Fin (2^w)) (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w))
    (z : Z ⊕ Bool → Bool) (h : H → Bool) (i : Outputs ((C+(J+C))+(v+o)) w) :
    (privateControls F old controls packet).eval (Sum.elim z h) i =
      (withPrivateViews F old (withControls controls (atExtra packet h))).eval z i := by
  apply prepended
  intro col
  rcases col with ⟨i,j⟩ | ⟨⟩
  · refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  · exact (joinedControls_valid ..).trans ((atExtra_eval ..).symm.trans (withControls_valid ..).symm)

variable (F : Fields s m n C d k w Z) (hk : k≤w) (old : Fin J → Fin s) (ports : Fin P → Fin n)
variable (rest : Frame (Z ⊕ H) (Outputs o w)) (src : Frame Γ Z) (keep : Frame Γ H)

/-- One fixed native emitter on the original branch. The retained program is
compiled once alongside the terminal fields, before all numeric outputs are selected. -/
noncomputable def emitter : Frame Γ (Fin (m*3+(RoutingOutputs.count m C J P+o)) × Fin w) :=
  let f := GeometryOutput.prepend (lift (CableTriples.frame F hk le_rfl))
    (GeometryOutput.prepend (lift (tail F hk old ports)) rest)
  (f.select Sum.inl).subst (parallelFrame src keep)

theorem emitter_size : (emitter F hk old ports rest src keep).size =
    src.size+keep.size+(CableTriples.frame F hk le_rfl).size+(tail F hk old ports).size+rest.size := by
  simp [emitter]
  omega

/-- The native retained emitter has the ordinary routing prefix and exactly
the new packet suffix evaluated on the same branch's real historical outputs. -/
theorem emitter_eval (y : Γ → Bool) (i : Fin (m*3+(RoutingOutputs.count m C J P+o)) × Fin w) :
    (emitter F hk old ports rest src keep).eval y i =
      (full F hk old ports (atExtra rest (keep.eval y))).eval (src.eval y) (.inl i) := by
  have joined : (parallelFrame src keep).eval y = Sum.elim (src.eval y) (keep.eval y) := by
    funext z; cases z <;> simp
  simp only [emitter,Frame.subst_eval,Frame.select_eval,joined,full]
  apply prepended
  intro c
  apply prepended
  intro j
  exact (atExtra_eval ..).symm

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
