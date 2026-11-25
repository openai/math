import OAI.Computability.BorderVNP.PackedHistoryNode

/-! # Sharing the physical pass between the successor directory and retained records

Both consumers read the very same selected motions, measured widths, and
count words. The retained-record emitter may also query any successor row.
The source and the checked geometry are evaluated once. All old immutable
record references can be exposed alongside the newly appended words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open VPVNP.VerifierNetwork

variable {σ Pre Geo Word : Type*} [Fintype σ] [Fintype Pre] [Fintype Geo] [Fintype Word]
    (source : Frame σ Pre) (geometry : Frame Pre (Geo ⊕ Unit))
    (emit : Frame (Pre ⊕ (Geo ⊕ Unit)) Word)

/-- One shared state update. The geometric validity bit remains at the outer
flag position, and the immutable output words occupy the second state bank. -/
noncomputable def joint : Frame σ ((Geo ⊕ Word) ⊕ Unit) :=
  (emit.withInput.select (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inr ∘ Sum.inl) Sum.inr)
    (Sum.inl ∘ Sum.inr ∘ Sum.inr))).subst (geometry.withInput.subst source)

/-- The complete common front-end and selected geometry are each charged only once. -/
theorem joint_size : (joint source geometry emit).size = source.size + geometry.size + emit.size := by
  simp only [joint,Frame.subst_size,Frame.withInput_size,Frame.select_size]

/-- Geometry and guard have exactly the values obtained before appending local records. -/
theorem joint_geometry (x : σ → Bool) (z : Geo) :
    (joint source geometry emit).eval x (.inl (.inl z)) = geometry.eval (source.eval x) (.inl z) := by
  simp [joint,Frame.subst_eval]

/-- The physical bank guard survives the addition of local payload words unchanged. -/
theorem joint_flag (x : σ → Bool) :
    (joint source geometry emit).eval x (.inr ()) = geometry.eval (source.eval x) (.inr ()) := by
  simp [joint,Frame.subst_eval]

/-- Each appended record sees exactly the evaluated pre-cut inputs and post-cut directory,
including the flag if the emitter uses it for invalid profiles. -/
theorem joint_words (x : σ → Bool) (z : Word) :
    (joint source geometry emit).eval x (.inl (.inr z)) =
      emit.eval (Sum.elim (source.eval x) (geometry.eval (source.eval x))) z := by
  simp only [joint,Frame.subst_eval,Frame.select_eval,Sum.elim_inl,Sum.elim_inr,Frame.withInput_eval_inr]
  congr 1
  funext j
  cases j <;> simp

variable {Old New : Type*} [Fintype Old] [Fintype New]

/-- Output all old immutable references and the new words. Selecting old references
from the common state incurs no extra gate and preserves exact readback. -/
noncomputable def append (old : Old → Pre) (fresh : Frame (Pre ⊕ (Geo ⊕ Unit)) New) :
    Frame (Pre ⊕ (Geo ⊕ Unit)) (Old ⊕ New) :=
  fresh.withInput.select (Sum.elim (Sum.inl ∘ Sum.inl ∘ old) Sum.inr)

/-- All additional work in this immutable append is the work of the new-record writer. -/
theorem append_size (old : Old → Pre) (fresh : Frame (Pre ⊕ (Geo ⊕ Unit)) New) :
    (append old fresh).size = fresh.size := by simp [append]

/-- The complete append returns the prior record unchanged on each of its old slots. -/
theorem append_old (old : Old → Pre) (fresh : Frame (Pre ⊕ (Geo ⊕ Unit)) New)
    (x : Pre ⊕ (Geo ⊕ Unit) → Bool) (z : Old) : (append old fresh).eval x (.inl z) = x (.inl (old z)) := by
  simp [append]

/-- Each new slot reads the actual newly generated record word. -/
theorem append_new (old : Old → Pre) (fresh : Frame (Pre ⊕ (Geo ⊕ Unit)) New)
    (x : Pre ⊕ (Geo ⊕ Unit) → Bool) (z : New) : (append old fresh).eval x (.inr z) = fresh.eval x z := by
  simp [append]

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
