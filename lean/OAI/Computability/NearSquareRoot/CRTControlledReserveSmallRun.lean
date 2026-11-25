import OAI.Computability.NearSquareRoot.CRTControlledReserveSmall
import OAI.Computability.NearSquareRoot.CRTControlledReserveRun

/-! # Uniform elementary routing at bounded address width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveSmall

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Strip NearSquareRoot.Space

noncomputable section

/-- Compile and execute both reflection matchings using one command for all
address widths. Its clock counts all elementary exchanges. -/
theorem boundedRunAllWidths {I : Type} {r : Regime I} (k V : I → ℕ)
    (p : ∀ i, Equiv.Perm (Fin (k i)))
    (f : ∀ i, Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i) (tableHeader : r.Has fun i => Reflections.table (p i)) :
    BoundedTask (fun i => (2*k i+2)*V i) V
      (fun i => .fork (r.header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) := by
  have area (i : I) : 2^(k i) ≤ V i := by
    have h := inputCap i
    rw [stripe, Task.forest_count, Series.card, lineSize] at h
    omega
  have keys : r.Has (fun i => flatSwapInput (k i) (fullMoves (p i))) := by
    simpa only [fullHeader_spec] using tableHeader.thenDo poly_fullHeader
  have hh := keys.cooked (ReserveStage.ripeOfWidth scale area)
  have volume : Volume (fun i => (V i : ℝ)) (fun i => stripe (line 2 (k i)) (f i)) :=
    ⟨1,fun i => by simpa only [Nat.cast_one, one_mul] using Nat.cast_le.mpr (inputCap i)⟩
  have prep := boundedOfCarries (hh.first volume)
  have run := boundedFlatSwaps true k V (fun i => fullMoves (p i)) (fun i => fullMoves_distinct (p i))
    2 (fun i => by have := fullMoves_length (p i); omega) f inputCap
  have correct i : swapsFlat (fullMoves (p i)).reverse = flatBitPullback (p i) := by
    apply eq_flatBitPullback
    intro y j
    rw [swapsFlat_reverse_prefixBit, fullMoves_value]
  have done := (prep.compose run).conform (output' := fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i)))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun i => by simp only [ite_true, correct i])
  apply done.mono _ (fun i => by simp)
  intro i
  calc
    _ = ((fullMoves (p i)).length+2)*V i := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right (fullMoves_length (p i)) 2)

/-- At any fixed width bound, compiling and executing the two reflection matchings
costs linear time and space in the encoded record volume. -/
theorem boundedRunUniform {I : Type} {r : Regime I} (K : ℕ) (k V : I → ℕ)
    (p : ∀ i, Equiv.Perm (Fin (k i))) (width : ∀ i, k i ≤ K)
    (f : ∀ i, Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i) (tableHeader : r.Has fun i => Reflections.table (p i)) :
    BoundedTask V V
      (fun i => .fork (r.header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) := by
  apply (boundedRunAllWidths k V p f inputCap scale tableHeader).bound (2*K+2) 1
  · intro i
    have c := Nat.mul_le_mul_right (V i) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (width i)) 2)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · intro i
    simp

/-- Execute directly from the unary permutation table and the array. -/
theorem boundedRun {I : Type} (K : ℕ) (k V : I → ℕ) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (width : ∀ i, k i ≤ K) (f : ∀ i, Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (Reflections.table (p i))) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) := by
  let r : Regime I := ⟨k, fun i => send (Reflections.table (p i)), 2, 2,
    fun i => Reflections.table_size (p i)⟩
  exact boundedRunUniform (r := r) K k V p width f inputCap (fun _ => le_rfl) r.self

/-- Fixed-width record cloth can be routed from the same shared header as the four-stage
large-width algorithm. -/
theorem boundedCloth {I X : Type} [Codec X] {U : I → Type} {r : Regime I}
    (K : ℕ) (k V : I → ℕ) (u : (i : I) → Series (U i)) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (width : ∀ i, k i ≤ K) (x : (i : I) → Block 2 (k i) → U i → X)
    (inputCap : ∀ i, (Loom.cloth (fun i => line 2 (k i)) u x i).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i) (tableHeader : r.Has fun i => Reflections.table (p i)) :
    BoundedTask V V (fun i => .fork (r.header i) (Loom.cloth (fun i => line 2 (k i)) u x i))
      (Loom.cloth (fun i => line 2 (k i)) u (fun i z => x i (flatBitPullback (p i) z))) :=
  boundedRunUniform K k V p width (fun i z => Loom.strip (u i) (x i z)) inputCap scale tableHeader

/-- Numerical-order record storage uses the same uniform program. -/
theorem boundedRecords {I A : Type} [Codec A] (K : ℕ) (k V : I → ℕ)
    (p : ∀ i, Equiv.Perm (Fin (k i))) (width : ∀ i, k i ≤ K) (f : ∀ i, Fin (2^(k i)) → A)
    (inputCap : ∀ i, (send (List.ofFn (f i))).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (Reflections.table (p i))) (send (List.ofFn (f i))))
      (fun i => send (List.ofFn (f i ∘ BoxFin.bitAddress (p i).symm))) := by
  have run := boundedRun K k V p width (fun i a => send (f i (flatAddress 2 (k i) a)))
    (fun i => (stripe_ordinals (k i) (f i)) ▸ inputCap i)
  refine run.conform (fun _ => rfl) (fun _ => rfl)
    (fun i => congrArg _ (stripe_ordinals (k i) (f i))) ?_
  intro i
  rw [← stripe_ordinals]
  apply congrArg (stripe (line 2 (k i)))
  funext x
  simp only [Function.comp_apply, flatBitPullback, Equiv.trans_apply, Equiv.apply_symm_apply]

end
end Controlled.ReserveSmall

end NearSquareRoot
end Computability
end OAI
