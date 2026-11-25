import OAI.Hierarchy.DescentResetSourceFrame
import OAI.Hierarchy.DescentResetExceptionalBits

namespace OAI
/-! # Reading both paid/fallback selectors from the same measured physical reset -/

namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentChosenRouter
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ)

private theorem group_cast {k k' : ℕ} (length : k=k') (L : Layout k) (L' : Layout k') (same : HEq L L')
    (x : Block k) (y : Block k') (input : x.val=y.val) (d : ℕ) :
    group d (rearrange L x)=group d (rearrange L' y) := by
  subst k'
  obtain rfl:=eq_of_heq same
  obtain rfl:=Fin.ext input
  rfl

omit [Fintype V] [DecidableEq V] in
theorem source_base (s : Bool) (e : A.graph.Edge) :
    label Z.placement.b (baseOf Z.placement.b Z.placement.depth Z.placement.L (Z.placement.old s e)) =
      let u := DescentResetAttachments.ends A.graph s e
      (frame.host (pos u), group (Z.placement.b (frame.host (pos u))) (rearrange frame.basis (ix u))) := by
  apply Prod.ext
  · exact frame.actor s e
  · change (dyadicLayout (Z.placement.depth (Z.placement.old s e).1) Z.placement.L
        (Z.placement.old s e).2).val = _
    rw [layout_id, frame.actor s e]
    exact group_cast frame.extent Z.placement.L frame.basis frame.used.symm _ _ (frame.oldBlock s e) _

theorem source_mode
    (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
    (e : A.graph.Edge) :
    useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old e ↔
      ∀ s, let u := DescentResetAttachments.ends A.graph s e
           let v := pos u
           (v, group (Z.placement.b (frame.host v)) (rearrange frame.basis (ix u))) ∉
             resetKeys near Δ f B K wt flow (fun w => Z.placement.b (frame.host w))
               (fun w => (Z.placement.depth (frame.host w)).trans_eq frame.extent) frame.basis ∧
             hub v = false := by
  apply forall_congr'
  intro s
  apply and_congr
  · apply not_congr
    simp only [validBases, Finset.mem_filter, Finset.mem_univ, true_and, frame.source_base s e]
    exact roster.2.2.2.1 _ _
  · rw [frame.actor s e, frame.rotorHub]
    cases hub (pos (DescentResetAttachments.ends A.graph s e)) <;> decide

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
