import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate

/-! # One binary program for any of finitely many compact arities

The arity tag uses `i` true bits followed by one false bit. A finite branch instruction
reads each tag bit. Every branch uses the same result format and the branch clocks combine
into the single `Procedure` clock of the dispatcher.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

/-- Explicit self-delimiting arity and the actual payload for that case. -/
def taggedCode {n : ℕ} {α : Fin n → Type} (enc : ∀ i, α i → List Bool)
    (x : (i : Fin n) × α i) : List Bool :=
  List.replicate x.1.val true ++ false :: enc x.1 x.2

private def splitArity {n : ℕ} {α : Fin (n+1) → Type} (x : (i : Fin (n+1)) × α i) :
    α 0 ⊕ ((j : Fin n) × α j.succ) :=
  Fin.cases (motive := fun i => α i → _) (fun a => Sum.inl a)
    (fun j a => Sum.inr ⟨j,a⟩) x.1 x.2

/-- Compile finitely many polynomial-time procedures with different input types into one
polynomial-time procedure on a tagged input. Tags correspond to dimension data alone. -/
noncomputable def dispatch {γ : Type} (fallback : γ) (out : γ → List Bool) :
    (n : ℕ) → {α : Fin n → Type} → (enc : ∀ i, α i → List Bool) →
    (f : ∀ i, α i → γ) → (∀ i, Procedure (enc i) out (f i)) →
    Procedure (taggedCode enc) out (fun x => f x.1 x.2)
  | 0, _, enc, _, _ => (Procedure.constant (taggedCode enc) out fallback).congrFun
      (fun x => Fin.elim0 x.1)
  | n+1, α, enc, f, branches => by
    let tail := dispatch fallback out n (α := fun j => α j.succ)
      (fun j => enc j.succ) (fun j => f j.succ) (fun j => branches j.succ)
    let split := (Procedure.casesSum (branches 0) tail).precompose (splitArity (α := α))
    have he (x : (i : Fin (n+1)) × α i) :
        sumCode (enc 0) (taggedCode fun j => enc j.succ) (splitArity x) = taggedCode enc x := by
      rcases x with ⟨i,a⟩
      cases i using Fin.cases with
      | zero => rfl
      | succ j => simp [splitArity,taggedCode,sumCode,List.replicate_succ]
    exact (split.congrEncoding he (fun _ => rfl)).congrFun (by
      rintro ⟨i,a⟩; cases i using Fin.cases <;> rfl)

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
