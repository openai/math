import OAI.Computability.BorderVNP.ResidueEntryFieldBudget

/-! # The combined AND/NOT verifier of a residue summand

The input field expressions share a query tape with the grid-validity and threshold
checks. The projection receives the original tape together with the computed field
result, so the column basis index may select a different linear functional per query.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryVerifierCore

open ExactQuantumFactoring BooleanNetwork BitArithmetic VPVNP
open BorderVNP.ResidueEntryField

variable {I K : Type*} [Fintype I] {p n d w k b : ℕ} [Fact p.Prime]
  [Field K] [Algebra (ZMod p) K]

/-- Evaluate the given field SLP on its supplied operand circuits. The bijection of the
finite variable type with numbered registers preserves every gate. -/
noncomputable def evaluate (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) : BooleanNetwork n (d*w) :=
  let e := Fintype.equivFin I
  (wordBlocks fun i => inputs (e.symm i)).comp (compile B hp (C.subst (Sum.inl ∘ e) id))

/-- The field register represents the arithmetic result for each query whose operand registers
represent the assigned field inputs. -/
theorem evaluate_value (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) (x : Fin n → Bool) (f : I → K)
    (hf : ∀ i, Represents B ((inputs i).eval x) (f i)) :
    Represents B ((evaluate B hp C inputs).eval x) (C.eval id f) := by
  let e := Fintype.equivFin I
  let A := wordBlocks fun i => inputs (e.symm i)
  let C' := C.subst (Sum.inl ∘ e) id
  have h (i) : Represents B (block (A.eval x) i) (f (e.symm i)) := by
    rw [show block (A.eval x) i = (inputs (e.symm i)).eval x from wordBlocks_eval ..]
    exact hf _
  have hc : C'.eval id (f ∘ e.symm) = C.eval id f := by
    simp [C', Circuit.eval_subst, Function.comp_def]
  rw [evaluate, eval_comp, ← hc]
  exact compile_value B hp C' _ (f ∘ e.symm) h

/-- Cost of evaluating the SLP and reading all supplied input networks. -/
theorem evaluate_count (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) (a : ℕ)
    (ha : ∀ i, (inputs i).net.count ≤ a) :
    (evaluate B hp C inputs).net.count ≤ Fintype.card I*(d*w)*a + k*stepCost d w + d*w*w := by
  rw [evaluate, count_comp]
  have h := wordBlocks_count (fun i => inputs ((Fintype.equivFin I).symm i)) (fun i => ha _)
  have hc := compile_count B hp (C.subst (Sum.inl ∘ Fintype.equivFin I) id)
  exact (Nat.add_le_add h hc).trans (by omega)

/-- The full residue verifier network, including the indexed projection and binary guess test. -/
noncomputable def verifier (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) (valid : BooleanNetwork n 1)
    (y : BooleanNetwork n b) (project : BooleanNetwork (n+d*w) w) : BooleanNetwork n 1 :=
  valid.band (threshold y (((select id).pair (evaluate B hp C inputs)).comp project))

/-- Return the validity-filtered threshold bit in the processor's shared AND/NOT gate model. -/
noncomputable def build (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) (valid : BooleanNetwork n 1)
    (y : BooleanNetwork n b) (project : BooleanNetwork (n+d*w) w) :
    BooleanTranscript.Circuit (Fin n) (verifier B hp C inputs valid y project).net.count :=
  Transcript.circuit _ 0

/-- The combined verifier accepts exactly the valid queries with a successful final guess.
The arithmetic and projection hypotheses are needed only for an accepted validity test. -/
theorem build_eval (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w) (hb : b ≤ w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) (valid : BooleanNetwork n 1)
    (y : BooleanNetwork n b) (project : BooleanNetwork (n+d*w) w)
    (x : Fin n → Bool) (f : I → K) (v : ZMod p)
    (hf : valid.eval x 0 = true → ∀ i, Represents B ((inputs i).eval x) (f i))
    (hπ : valid.eval x 0 = true → ∀ z, Represents B z (C.eval id f) →
      value (project.eval (Fin.append x z)) = v.val) :
    (build B hp C inputs valid y project).eval x = true ↔
      valid.eval x 0 = true ∧ value (y.eval x) < v.val := by
  rw [build, Transcript.circuit_eval, verifier, eval_band, Bool.and_eq_true]
  refine and_congr_right fun hv => threshold_eval hb _ _ _ v ?_
  simp only [eval_comp, eval_pair, eval_select, Function.comp_id]
  exact hπ hv _ (evaluate_value B hp C inputs x f (hf hv))

/-- Total bit gate budget. The arithmetic part grows linearly in the shared DAG size;
the projection contributes exactly its own network size. -/
theorem build_count (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K I k) (inputs : I → BooleanNetwork n (d*w)) (valid : BooleanNetwork n 1)
    (y : BooleanNetwork n b) (project : BooleanNetwork (n+d*w) w) (a : ℕ)
    (ha : ∀ i, (inputs i).net.count ≤ a) :
    (verifier B hp C inputs valid y project).net.count ≤ Fintype.card I*(d*w)*a +
      k*stepCost d w + d*w*w + valid.net.count + y.net.count + project.net.count + 49*w + 9 := by
  have h := evaluate_count B hp C inputs a ha
  have ht := threshold_count y (((select id).pair (evaluate B hp C inputs)).comp project)
  simp only [count_comp, count_pair, count_select, zero_add] at ht
  rw [verifier, count_band]
  omega

end ResidueEntryVerifierCore

end BorderVNP
end Computability
end OAI
