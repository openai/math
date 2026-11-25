import OAI.Computability.BorderVNP.PackedHistoryBroadcast

/-! # Wiring the physical profile reservation into the public history frame

The active profile fields use their child-major ordinals. The trailing reservation is checked
for zero in the same shared gate program as the original validity flag. Every selected output
bit refers directly to its original gate result.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.VerifierNetwork ParseBatchVerifier
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V] {active reserve : ℕ}

private def inputPin (order : S ≃ Fin active) (fit : active ≤ reserve) : σ ⊕ S → σ ⊕ Fin reserve :=
  Sum.elim Sum.inl (fun j => .inr ((order j).castLE fit))

private def padPos (fit : active ≤ reserve) (j : Fin (reserve-active)) : Fin reserve := ⟨active+j.val,by omega⟩

private def padCheck (fit : active ≤ reserve) : Expr ((σ ⊕ Fin reserve) ⊕ (V ⊕ Unit)) :=
  .and (.input (.inr (.inr ()))) (every fun j : Fin (reserve-active) => .not (.input (.inl (.inr (padPos fit j)))))

private noncomputable def padPost (fit : active ≤ reserve) : Frame ((σ ⊕ Fin reserve) ⊕ (V ⊕ Unit)) (V ⊕ Unit) :=
  (((Frame.initial id).step (fun _ : Unit => padCheck fit)).withInput).select
    (Sum.elim (fun i => .inl (.inr (.inl i))) Sum.inr)

/-- A gate list taking the copied physical bits, retaining all live outputs and testing the
unused tail of the public profile array exactly once. -/
noncomputable def paddedFrame (f : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active)
    (fit : active ≤ reserve) : Frame (σ ⊕ Fin reserve) (V ⊕ Unit) :=
  (padPost fit).subst (f.subst (Frame.initial (inputPin order fit))).withInput

private theorem wired (order : S ≃ Fin active) (fit : active ≤ reserve)
    (x : σ → Bool) (word : Fin reserve → Bool) :
    (Frame.initial (inputPin order fit)).eval (Sum.elim x word) = Sum.elim x (readProfile order fit word) := by
  funext j; cases j <;> simp [inputPin,readProfile]

/-- Original output bits are read at the exact physical profile assignment. -/
theorem paddedFrame_state (f : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active)
    (fit : active ≤ reserve) (x : σ → Bool) (word : Fin reserve → Bool) (i : V) :
    (paddedFrame f order fit).eval (Sum.elim x word) (.inl i) =
      f.eval (Sum.elim x (readProfile order fit word)) (.inl i) := by
  simp [paddedFrame,padPost,wired]

/-- The gate guard rejects each malformed active assignment and every nonzero tail bit. -/
theorem paddedFrame_valid (f : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active)
    (fit : active ≤ reserve) (x : σ → Bool) (word : Fin reserve → Bool) :
    (paddedFrame f order fit).eval (Sum.elim x word) (.inr ()) = true ↔
      validProfile order fit (fun g => f.eval (Sum.elim x g) (.inr ()) = true) word := by
  let u := (f.subst (Frame.initial (inputPin order fit))).withInput.eval (Sum.elim x word)
  have hi : (Frame.initial (id : ((σ ⊕ Fin reserve) ⊕ (V ⊕ Unit)) → _)).eval u = u := funext (Frame.initial_eval id u)
  rw [paddedFrame,Frame.subst_eval]
  change (padPost fit).eval u (.inr ()) = true ↔ _
  simp only [padPost,Frame.select_eval,Sum.elim_inr,Frame.withInput_eval_inr,Frame.step_eval,hi,padCheck,
    StatementCircuit.Expr.eval,Bool.and_eq_true,every_eval,Bool.not_eq_true',validProfile]
  have original : u (.inr (.inr ())) = f.eval (Sum.elim x (readProfile order fit word)) (.inr ()) := by simp [u,wired]
  rw [original]
  apply and_congr_right; intro _
  have bit (j : Fin (reserve-active)) : u (.inl (.inr (padPos fit j))) = word (padPos fit j) := by simp [u]
  simp only [bit]
  refine ⟨fun h i hi => ?_,fun h j => h _ (by dsimp [padPos]; omega)⟩
  have eq : padPos fit (⟨i.val-active,by have := i.isLt; omega⟩ : Fin (reserve-active)) = i := Fin.ext (by dsimp [padPos]; omega)
  simpa only [eq] using h (⟨i.val-active,by have := i.isLt; omega⟩ : Fin (reserve-active))

/-- Only the padding checks and one final conjunction are added to the shared frame. -/
theorem paddedFrame_size (f : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve) :
    (paddedFrame f order fit).size ≤ f.size + 3*(reserve-active)+3 := by
  have hv := every_size (fun j : Fin (reserve-active) =>
    (StatementCircuit.Expr.not (.input (.inl (.inr (padPos fit j)))) : Expr ((σ ⊕ Fin reserve) ⊕ (V ⊕ Unit)))) 2 (fun _ => le_rfl)
  have check : (padCheck (σ := σ) (V := V) fit).size ≤ 3*(reserve-active)+3 := by
    simp only [padCheck,StatementCircuit.Expr.size]; omega
  have h := Frame.step_size_le (Frame.initial (id : ((σ ⊕ Fin reserve) ⊕ (V ⊕ Unit)) → _))
    (fun _ : Unit => padCheck fit) _ (fun _ => check)
  simp only [Frame.initial_size,zero_add,Fintype.card_unit,one_mul] at h
  simpa only [paddedFrame,padPost,Frame.subst_size,Frame.withInput_size,Frame.select_size,Frame.initial_size,
    Nat.zero_add,Nat.add_assoc] using Nat.add_le_add_left h f.size

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
