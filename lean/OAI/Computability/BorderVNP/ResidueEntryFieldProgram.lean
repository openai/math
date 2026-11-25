import OAI.Computability.BorderVNP.ResidueEntryField

/-! # Compile field straight-line evaluations on a residue branch

The Boolean compiler retains every previously computed field value. Input variables and
gate references select already available wires. Thus the bit-gate cost grows linearly with
the arithmetic DAG size, regardless of fanout.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryField

open ExactQuantumFactoring BooleanNetwork BitArithmetic VPVNP

variable {p s d w k : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- Additional bit gates allowed per arithmetic gate, including two literal operands. -/
def stepCost (d w : ℕ) : ℕ := 2*(d*w*w) + fieldGateCost d w

private structure Bank (B : Module.Basis (Fin d) (ZMod p) K) (w : ℕ)
    (P : Program K (Fin s) k) where
  width : ℕ
  net : BooleanNetwork (s*(d*w)) width
  varWire : Fin s → Fin (d*w) → Fin width
  gateWire : Fin k → Fin (d*w) → Fin width
  cost : net.net.count ≤ k*stepCost d w
  inputs (x : Fin (s*(d*w)) → Bool) (i : Fin s) :
    net.eval x ∘ varWire i = block x i
  gates (x : Fin (s*(d*w)) → Bool) (f : Fin s → K)
    (h : ∀ i, Represents B (block x i) (f i)) (i : Fin k) :
    Represents B (net.eval x ∘ gateWire i) (P.run id f i)

private noncomputable def readNet {B : Module.Basis (Fin d) (ZMod p) K} {P : Program K (Fin s) k}
    (A : Bank B w P) : Ref K (Fin s) k → BooleanNetwork A.width (d*w)
  | .var i => select (A.varWire i)
  | .gate j => select (A.gateWire j)
  | .const a => fieldConst A.width w B a

private theorem readNet_count {B : Module.Basis (Fin d) (ZMod p) K} {P : Program K (Fin s) k}
    (A : Bank B w P) (r : Ref K (Fin s) k) : (readNet A r).net.count ≤ d*w*w := by
  cases r with
  | var | gate => exact Nat.zero_le _
  | const => exact fieldConst_count _ _

private theorem readNet_value {B : Module.Basis (Fin d) (ZMod p) K} {P : Program K (Fin s) k}
    (A : Bank B w P) (hp : p < 2^w) (r : Ref K (Fin s) k) (x : Fin (s*(d*w)) → Bool)
    (f : Fin s → K) (h : ∀ i, Represents B (block x i) (f i)) :
    Represents B ((readNet A r).eval (A.net.eval x)) (r.read id f (P.run id f)) := by
  cases r with
  | var i => simpa only [readNet, eval_select, A.inputs, Ref.read] using h i
  | gate i => exact A.gates _ _ h i
  | const a => exact fieldConst_value hp _ _ _

private noncomputable def bank (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (P : Program K (Fin s) k) : Bank B w P := by
  induction P with
  | nil => exact ⟨_, select id, fun i j => finProdFinEquiv (i,j), Fin.elim0,
      by simp, fun _ _ => rfl, fun _ _ _ i => i.elim0⟩
  | @snoc k P op r t A =>
    let new := ((readNet A r).pair (readNet A t)).comp (fieldGate w B op)
    let N := A.net.comp ((select id).pair new)
    let oldVar := fun i => Fin.castAdd (d*w) ∘ A.varWire i
    let oldGate := fun i => Fin.castAdd (d*w) ∘ A.gateWire i
    let gates : Fin (k+1) → Fin (d*w) → Fin (A.width + d*w) :=
      Fin.snoc oldGate (Fin.natAdd A.width)
    have hN (x) : N.eval x = Fin.append (A.net.eval x) (new.eval (A.net.eval x)) := by
      simp only [N, eval_comp, eval_pair, eval_select, Function.comp_id]
    refine ⟨_, N, oldVar, gates, ?_, ?_, ?_⟩
    · have hr := readNet_count A r
      have ht := readNet_count A t
      have hg := fieldGate_count (w := w) B op
      simp only [N, new, count_comp, count_pair, count_select, zero_add, Nat.succ_mul]
      have ha := A.cost
      unfold stepCost at *
      omega
    · intro x i
      rw [hN, ← A.inputs x i]
      funext j
      exact Fin.append_left _ _ _
    · intro x f h i
      rw [hN]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [show gates (Fin.last k) = Fin.natAdd A.width from Fin.snoc_last ..]
        rw [show (Fin.append (A.net.eval x) (new.eval (A.net.eval x)) ∘ Fin.natAdd A.width) =
          new.eval (A.net.eval x) from funext (fun _ => Fin.append_right ..)]
        simp only [new, eval_comp, eval_pair, Program.run, Fin.lastCases_last]
        exact fieldGate_value hp _ _ _ _ _ _ (readNet_value A hp r x f h)
          (readNet_value A hp t x f h)
      · rw [show gates j.castSucc = oldGate j from Fin.snoc_castSucc ..]
        rw [show (Fin.append (A.net.eval x) (new.eval (A.net.eval x)) ∘ oldGate j) =
          A.net.eval x ∘ A.gateWire j from funext (fun _ => Fin.append_left ..)]
        simpa only [Program.run, Fin.lastCases_castSucc] using A.gates x f h j

/-- Simulate an exact field circuit on the guessed basis coordinates. -/
noncomputable def compile (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (Fin s) k) : BooleanNetwork (s*(d*w)) (d*w) :=
  let A := bank B hp C.program
  A.net.comp (readNet A C.output)

/-- The simulation produces the canonical binary limbs of the evaluated field expression. -/
theorem compile_value (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (Fin s) k) (x : Fin (s*(d*w)) → Bool) (f : Fin s → K)
    (h : ∀ i, Represents B (block x i) (f i)) :
    Represents B ((compile B hp C).eval x) (C.eval id f) := by
  rw [compile, eval_comp]
  exact readNet_value _ hp _ _ _ h

/-- The arithmetic DAG may reuse gates without increasing the linear factor in its size. -/
theorem compile_count (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (Fin s) k) :
    (compile B hp C).net.count ≤ k*stepCost d w + d*w*w := by
  rw [compile, count_comp]
  exact Nat.add_le_add (bank B hp C.program).cost (readNet_count _ _)

/-- The AND/NOT circuit for any requested output bit of the simulated field register. -/
noncomputable def outputCircuit (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (Fin s) k) (j : Fin (d*w)) :
    BooleanTranscript.Circuit (Fin (s*(d*w))) (compile B hp C).net.count :=
  Transcript.circuit _ j

/-- Every projected output bit is computed by the live processor's circuit interpreter. -/
theorem outputCircuit_eval (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (Fin s) k) (j : Fin (d*w)) (x : Fin (s*(d*w)) → Bool) :
    (outputCircuit B hp C j).eval x = (compile B hp C).eval x j :=
  Transcript.circuit_eval _ _ _

end ResidueEntryField

end BorderVNP
end Computability
end OAI
