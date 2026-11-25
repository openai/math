import OAI.Computability.BorderVNP.PackedHistoryGuardedFrame
import OAI.Computability.BorderVNP.GeometryFrameEncoding

/-! # Shared geometry output words for a physically addressed profile reservation

The public row emitter can read all original pins, the physical profile bank, and the final
history state. Its reference to the history's validity flag is kept separate from the words.
Only profile bits are runtime queries to the installed gate table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.VerifierNetwork GeometryFrameEncoding Crossing

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V] {active reserve o b : ℕ}

/-- All fixed public inputs are encoded in the advised gate descriptions. The varying
queries are exactly the bits copied from the physical profile reservation. -/
def profilePins (x : σ → Bool) : σ ⊕ Fin reserve → (Fin reserve ⊕ Fin 0) ⊕ Bool :=
  Sum.elim (Sum.inr ∘ x) (Sum.inl ∘ Sum.inl)

omit [Fintype σ] in
/-- Semantic interpretation of this literal pin table. -/
theorem profilePins_eval (x : σ → Bool) (word : Fin reserve → Bool) :
    (fun i => (profilePins x i).elim (Sum.elim word Fin.elim0) id) = Sum.elim x word := by
  funext i; cases i <;> rfl

/-- Retain the exact profile validity wire while sharing its entire history evaluation among
all public sparse output rows. The emitter may refer back to an earlier raw profile field. -/
noncomputable def exportRows (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) : Frame (σ ⊕ Fin reserve) (Outputs o b) :=
  let take : (σ ⊕ Fin reserve) ⊕ V → (σ ⊕ Fin reserve) ⊕ (V ⊕ Unit) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  let h := paddedFrame history order fit
  (parallelFrame (emit.subst (Frame.initial take)) (Frame.initial (Sum.inr ∘ Sum.inr))).subst h.withInput

/-- Reading an emitted bit uses the true public pins and represented terminal state. -/
theorem exportRows_bit (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool) (word : Fin reserve → Bool) (p : Fin o × Fin b) :
    (exportRows history order fit emit).eval (Sum.elim x word) (.inl p) =
      emit.eval (Sum.elim (Sum.elim x word) (fun v => history.eval (Sum.elim x (readProfile order fit word)) (.inl v))) p := by
  simp only [exportRows,Frame.subst_eval,parallelFrame_eval_inl]
  congr 1
  funext i
  cases i <;> simp [paddedFrame_state]

/-- The complete row emitter preserves the canonical profile test. -/
theorem exportRows_valid (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool) (word : Fin reserve → Bool) :
    (exportRows history order fit emit).eval (Sum.elim x word) (.inr ()) = true ↔
      validProfile order fit (fun g => history.eval (Sum.elim x g) (.inr ()) = true) word := by
  simp [exportRows,paddedFrame_valid]

/-- The final compiled geometry advice uses the history and emitter gates exactly once, plus
three gates per padding bit and a constant guard cost. -/
theorem exportRows_size (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool) :
    (GeometryFrameEncoding.compile (exportRows history order fit emit) (profilePins x)).size ≤
      4*(history.size+emit.size+3*(reserve-active)+3) := by
  apply (GeometryFrameEncoding.size_le ..).trans
  have h := paddedFrame_size history order fit
  simp only [exportRows,Frame.subst_size,parallelFrame_size,Frame.initial_size,Frame.withInput_size]
  omega

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
