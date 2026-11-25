import OAI.Computability.NearSquareRoot.CRTControlledFlatSwapKey
import OAI.Computability.NearSquareRoot.CRTControlledFlatSwapSchedule

/-! # Executing a list of flat-address position exchanges from one compact table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Code NearSquareRoot.Space

noncomputable section

/-- A shared address width followed by pairs of unary bit positions suffices for both
directions. The number of pairs can vary, including the empty table. -/
theorem boundedFlatSwaps (backwards : Bool) {I : Type} (k V : I → ℕ)
    (moves : (i:I) → List (Fin (k i) × Fin (k i)))
    (distinct : ∀ i, ∀ a ∈ moves i, a.1 ≠ a.2)
    (D : ℕ) (hlen : ∀ i, (moves i).length ≤ D*(k i+1))
    (f : (i:I) → Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    BoundedTask (fun i => ((moves i).length+1)*V i) V
      (fun i => .fork (send (flatSwapInput (k i) (moves i))) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ swapsFlat (if backwards then (moves i).reverse else moves i))) := by
  let active (i:I) := if backwards then (moves i).reverse else moves i
  have lengthEq i : (active i).length = (moves i).length := by cases backwards <;> simp [active]
  have hdis i : ∀ p ∈ active i, p.1 ≠ p.2 := by
    cases backwards <;> simpa [active] using distinct i
  have area i : 2^(k i) ≤ V i := by
    have hc := inputCap i
    rw [stripe,Task.forest_count,Series.card,lineSize] at hc
    omega
  obtain ⟨C,hC⟩ := flatSwapKeys_cap D
  let vol i := (C+1)*V i
  have fileCap i : (stripe (line 2 (k i)) (f i)).count ≤ vol i :=
    (inputCap i).trans (Nat.le_mul_of_pos_left _ (by omega))
  have forestCap i : (send (flatSwapKeys (k i) (active i))).count ≤ vol i := by
    exact (hC _ _ ((lengthEq i) ▸ hlen i)).trans
      ((Nat.mul_le_mul_left _ (area i)).trans (Nat.mul_le_mul_right _ (by omega)))
  have run := boundedFlatSwapKeys k vol active hdis f fileCap (fun i => by
    simpa only [flatSwapKeys,Fin.coe_max,Fin.coe_min] using forestCap i)
  have step := run.bound (time' := fun i => ((moves i).length+1)*V i) (space' := V)
    (C+1) (C+1) (fun i => by dsimp only [vol]; rw [lengthEq]; nlinarith) (fun i => by dsimp [vol]; nlinarith)
  let data i := stripe (line 2 (k i)) (f i)
  have prep : BoundedTask V V (fun i => .fork (send (flatSwapInput (k i) (moves i))) (data i))
      (fun i => .fork (send (flatSwapKeys (k i) (active i))) (data i)) := by
    cases backwards
    · exact prepareFlatSwapList k moves V data D hlen area inputCap
    · exact prepareFlatSwapListReverse k moves V data D hlen area inputCap
  have step' := step.conform (fun _ => rfl) (fun _ => rfl)
    (input' := fun i => .fork (send (flatSwapKeys (k i) (active i))) (data i))
    (fun i => by simp only [flatSwapKeys,Fin.coe_max,Fin.coe_min,data]) (fun _ => rfl)
  exact (prep.compose step').bound 2 1 (fun i => by
    have hsmall : V i ≤ ((moves i).length+1)*V i := Nat.le_mul_of_pos_left _ (by omega)
    omega) (fun i => by simp)

/-- All moved records retain their native codec and are read in numerical order. -/
theorem boundedFlatSwapRecords (backwards : Bool) {I X : Type} [Codec X] (k V : I → ℕ)
    (moves : (i:I) → List (Fin (k i) × Fin (k i)))
    (distinct : ∀ i, ∀ a ∈ moves i, a.1 ≠ a.2)
    (D : ℕ) (hlen : ∀ i, (moves i).length ≤ D*(k i+1))
    (f : (i:I) → Fin (2^(k i)) → X) (inputCap : ∀ i, (send (List.ofFn (f i))).count ≤ V i) :
    let perm i := ((flatAddress 2 (k i)).symm.trans
      (swapsFlat (if backwards then (moves i).reverse else moves i))).trans (flatAddress 2 (k i))
    BoundedTask (fun i => ((moves i).length+1)*V i) V
      (fun i => .fork (send (flatSwapInput (k i) (moves i))) (send (List.ofFn (f i))))
      (fun i => send (List.ofFn (f i ∘ perm i))) := by
  intro perm
  have run := boundedFlatSwaps backwards k V moves distinct D hlen (fun i a => send (f i (flatAddress 2 (k i) a)))
    (fun i => (stripe_ordinals (k i) (f i)) ▸ inputCap i)
  refine run.conform (fun _ => rfl) (fun _ => rfl) (fun i => congrArg _ (stripe_ordinals (k i) (f i))) ?_
  intro i
  rw [← stripe_ordinals]
  apply congrArg _
  funext a
  simp [Function.comp_def,perm]

end
end Controlled

end NearSquareRoot
end Computability
end OAI
