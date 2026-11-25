import OAI.Computability.QuantumFactoring.BooleanNetworkFurther
import OAI.Computability.VPVNP.BooleanTranscript

/-! # Boolean arithmetic networks in the residue-entry interpreter

Translate the project's bounded fan-in word networks to the shared AND/NOT transcript
used by the live processor. The translation emits one gate per source node.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryField

open ExactQuantumFactoring VPVNP
namespace Transcript

private def liftRef {n k : ℕ} : Ref Bool (Fin n) k → Ref Bool (Fin n) (k+1)
  | .const b => .const b
  | .var i => .var i
  | .gate i => .gate i.castSucc

private theorem liftRef_read {n k : ℕ} (r : Ref Bool (Fin n) k) (x : Fin n → Bool)
    (v : Fin k → Bool) (b : Bool) : (liftRef r).read id x (Fin.snoc v b) = r.read id x v := by
  cases r <;> simp [liftRef, Ref.read]

private def node {n k m : ℕ} (r : Fin m → Ref Bool (Fin n) k) :
    BoolNode m → BooleanTranscript.Gate (Fin n) k
  | .constant b => .and (.const b) (.const true)
  | .copy i => .and (r i) (.const true)
  | .neg i => .not (r i)
  | .conj i j => .and (r i) (r j)

private theorem node_eval {n k m : ℕ} (r : Fin m → Ref Bool (Fin n) k)
    (x : Fin n → Bool) (v : Fin k → Bool) (o : BoolNode m) :
    (node r o).eval x v = o.eval (fun i => (r i).read id x v) := by
  cases o <;> simp [node, BoolNode.eval, BooleanTranscript.Gate.eval, Ref.read]

private structure Translation {n m : ℕ} (net : BoolNet n m) where
  program : BooleanTranscript.Program (Fin n) net.count
  refs : Fin m → Ref Bool (Fin n) net.count
  correct (x : Fin n → Bool) (i : Fin m) : (refs i).read id x (program.run x) = net.eval x i

private noncomputable def translate {n m : ℕ} (net : BoolNet n m) : Translation net := by
  induction net with
  | input => exact ⟨.nil, .var, fun _ _ => rfl⟩
  | @add k net o ih =>
    let refs : Fin (k+1) → Ref Bool (Fin n) (net.count+1) :=
      Fin.snoc (fun i => liftRef (ih.refs i)) (.gate (Fin.last net.count))
    refine ⟨ih.program.snoc (node ih.refs o), refs, ?_⟩
    intro x i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hr : refs (Fin.last k) = .gate (Fin.last net.count) := Fin.snoc_last ..
      rw [hr, BoolNet.eval_add_last]
      simp only [Ref.read, BooleanTranscript.Program.run]
      rw [Fin.snoc_last, node_eval]
      congr 1
      funext j
      exact ih.correct x j
    · have hr : refs j.castSucc = liftRef (ih.refs j) := Fin.snoc_castSucc ..
      rw [hr, BoolNet.eval_add_castSucc]
      exact (liftRef_read _ _ _ _).trans (ih.correct x j)

/-- Select any output of a shared word network in the AND/NOT circuit model of §11. -/
noncomputable def circuit {n m : ℕ} (N : BooleanNetwork n m) (i : Fin m) :
    BooleanTranscript.Circuit (Fin n) N.net.count :=
  ⟨(translate N.net).program, (translate N.net).refs (N.output i)⟩

/-- The designated output bit agrees on every assignment. -/
theorem circuit_eval {n m : ℕ} (N : BooleanNetwork n m) (i : Fin m) (x : Fin n → Bool) :
    (circuit N i).eval x = N.eval x i := (translate N.net).correct x _

end Transcript
end ResidueEntryField

end BorderVNP
end Computability
end OAI
