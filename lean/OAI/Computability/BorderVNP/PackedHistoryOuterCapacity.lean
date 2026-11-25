import OAI.Computability.BorderVNP.PackedHistoryOuterReadout
import OAI.Computability.BorderVNP.PackedHistoryCapacity

/-! # All genuine outer histories above a bounded bottom pack -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing VPVNP.VerifierNetwork
open scoped Classical

variable {k T : ℕ} {A : ℕ → Type*}
    (epoch : ∀ t, (Fin k → A t) → ProfileSum (A (t+1)))
    (good : ∀ t, A t → Prop) (closed : Capacity.Closed (outerSystem T epoch) good)
    (bottom : {a // good 0 a})

private theorem erase_repeat {X : Type*} {p : X → Prop} (x : {a // p a}) (n : ℕ) :
    Capacity.eraseLeaves n (repeatLeaf k x n) = repeatLeaf k x.val n := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext fun _ => ih

/-- The public bounded-state verifier retains the entire original outer pack expansion.
The equivalence preserves the computed pack including its routing records. -/
theorem outer_bounded_indices :
    let S := Capacity.restrict (outerSystem T epoch) good closed
    let a := repeatLeaf k bottom T
    ∃ idx : (S.histories T le_rfl a).Index ≃ (packHistory bottom.val epoch T).Index,
      ∀ q, (packHistory bottom.val epoch T).term (idx q) = (state (S := S) T le_rfl a q).val := by
  intro S a
  have he := Capacity.history_equiv (outerSystem T epoch) good closed T le_rfl a
  rw [show Capacity.eraseLeaves T a = _ from erase_repeat bottom T] at he
  obtain ⟨f,hf⟩ := he
  exact ⟨f.trans (outerEquiv bottom.val epoch T le_rfl),fun q =>
    (outerEquiv_state bottom.val epoch T le_rfl (f q)).trans (hf q)⟩

variable {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)] {σ : Type*} [Fintype σ]
    (C : Codec (Capacity.restrict (outerSystem T epoch) good closed) G)
    (rep : Represents A W) (step : Steps k T W G)
    (ok : LocalCorrect C (fun j z a => rep j z a.val) step)
    (f : Frame σ (W 0)) (x : σ → Bool) (base : rep 0 (f.eval x) bottom.val)

include base in
private theorem leaf_repeated (n : ℕ) : LeafState (fun j z a => rep j z (a : {s // good j s}).val) x n
    (repeatLeaf k bottom n) (repeatLeaf k f n) := by
  induction n with
  | zero => exact base
  | succ n ih => exact fun _ => ih

/-- Fixed guessed bits above admissible leaves encode every original physical branch exactly
once, even when the mathematical factory accepts arbitrarily large packs on other inputs. -/
noncomputable def acceptedOuterBounded :
    (packHistory bottom.val epoch T).Index ≃
      {g : Slot k G T → Bool // flag step T le_rfl (repeatLeaf k f T) x g = true} :=
  (outer_bounded_indices epoch good closed bottom).choose.symm.trans
    (acceptedEquiv C (fun j z a => rep j z a.val) step ok T le_rfl _ _ x (leaf_repeated good bottom rep f x base T))

/-- On the accepted word for a genuine branch the circuit yields its original routed pack. -/
theorem acceptedOuterBounded_state (q : (packHistory bottom.val epoch T).Index) :
    rep T (output step T le_rfl (repeatLeaf k f T) x
      ((acceptedOuterBounded epoch good closed bottom C rep step ok f x base q).val))
      ((packHistory bottom.val epoch T).term q) := by
  let idx := (outer_bounded_indices epoch good closed bottom).choose
  have he := (outer_bounded_indices epoch good closed bottom).choose_spec (idx.symm q)
  change (packHistory bottom.val epoch T).term (idx (idx.symm q)) = _ at he
  rw [idx.apply_symm_apply q] at he
  rw [he]
  exact (semantics C (fun j z a => rep j z a.val) step ok T le_rfl _ _ x
    (leaf_repeated good bottom rep f x base T) _).2 (idx.symm q) rfl

include ok base in
/-- The original physical history sum equals the public bit sum on the bounded-state DAG. -/
theorem sum_outer_bounded {R : Type*} [AddCommMonoid R] (readout : (W T → Bool) → R) (value : A T → R)
    (hr : ∀ z s, rep T z s → readout z = value s) :
    (∑ g : Slot k G T → Bool, if flag step T le_rfl (repeatLeaf k f T) x g then
      readout (output step T le_rfl (repeatLeaf k f T) x g) else 0) =
      ∑ q, value ((packHistory bottom.val epoch T).term q) := by
  rw [sum_transcripts C (fun j z a => rep j z a.val) step ok T le_rfl _ _ x
    (leaf_repeated good bottom rep f x base T) readout (fun a => value a.val) (fun z a h => hr z a.val h)]
  let idx := (outer_bounded_indices epoch good closed bottom).choose
  rw [← idx.sum_comp]
  exact Finset.sum_congr rfl fun q _ => congrArg value ((outer_bounded_indices epoch good closed bottom).choose_spec q).symm

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
