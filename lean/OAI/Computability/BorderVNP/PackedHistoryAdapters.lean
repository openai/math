import OAI.Computability.BorderVNP.PackedHistoryEpoch

/-! # Wiring subdivision and final placement around the checked inner history

The input preparation, the full shortening tree, and the returned site layout
are each computed once. The final layout frame can also use the original
child descriptors. The history guard is passed through on its own output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Crossing VPVNP.VerifierNetwork

variable {k b : ℕ} {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
variable {X V : Type} [Fintype X] [Fintype V]
variable (pre : Frame X (Fin (k^b) × W 0)) (step : Steps k b W G) (post : Frame (X ⊕ W b) V)

private noncomputable def inputStage : Frame (X ⊕ Slot k G b) (LocalPins (k^b) (W 0) (Slot k G b)) :=
  (pre.subst (Frame.initial Sum.inl)).withInput.select (Sum.elim Sum.inr (fun j => .inl (.inr j)))

private theorem inputStage_eval (x : X → Bool) (g : Slot k G b → Bool) :
    (inputStage (G := G) pre).eval (Sum.elim x g) = Sum.elim (pre.eval x) g := by
  have hx : (Frame.initial (Sum.inl : X → X ⊕ Slot k G b)).eval (Sum.elim x g) = x :=
    funext fun i => Frame.initial_eval _ _ _
  funext j
  cases j <;> simp [inputStage,hx]

private noncomputable def outputStage :
    Frame ((X ⊕ Slot k G b) ⊕ Result (W b)) (Result V) :=
  parallelFrame
    (post.subst (Frame.initial (Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j)))))
    (Frame.initial (fun _ : Unit => .inr (.inr ())))

/-- Actual public Boolean epoch with input subdivisions and output site placement. -/
noncomputable def wrappedEpoch : Frame (X ⊕ Slot k G b) (Result V) :=
  (outputStage (G := G) post).subst (((flatEpoch step).subst (inputStage pre)).withInput)

/-- The surrounding frames add exactly their individual gate counts. -/
theorem wrappedEpoch_size :
    (wrappedEpoch pre step post).size = pre.size + (flatEpoch step).size + post.size := by
  simp [wrappedEpoch,outputStage,inputStage,parallelFrame_size]

/-- The returned validity bit is exactly the inner tree's validity bit. -/
theorem wrappedEpoch_flag (x : X → Bool) (g : Slot k G b → Bool) :
    (wrappedEpoch pre step post).eval (Sum.elim x g) (.inr ()) =
      (flatEpoch step).eval (Sum.elim (pre.eval x) g) (.inr ()) := by
  simp [wrappedEpoch,outputStage,inputStage_eval]

/-- The public placement procedure sees the computed root state and the original child pins. -/
theorem wrappedEpoch_state (x : X → Bool) (g : Slot k G b → Bool) :
    (fun j => (wrappedEpoch pre step post).eval (Sum.elim x g) (.inl j)) =
      post.eval (Sum.elim x (fun j => (flatEpoch step).eval (Sum.elim (pre.eval x) g) (.inl j))) := by
  funext j
  simp only [wrappedEpoch,outputStage,Frame.subst_eval,parallelFrame_eval_inl]
  congr 1
  funext i
  cases i <;> simp [inputStage_eval]

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
