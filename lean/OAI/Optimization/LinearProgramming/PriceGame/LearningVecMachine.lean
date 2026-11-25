import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! # Fixed finite arrays on the binary-stack machine

A column is represented by the ordinary bit-stack list encoding in `Fin` order. These
procedures operate on the encoded words. The arity is a compile-time parameter; the
learning routine uses only the 66 possible arities of compact skeletons.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

variable {α β : Type}

/-- The decoded type records the arity. The wire format is an ordinary encoded list. -/
def vecCode (e : β → List Bool) (n : ℕ) (v : Fin n → β) : List Bool :=
  listCode e (List.ofFn v)

def matrixCode (e : β → List Bool) (n : ℕ) (d : Fin n → Fin n → β) : List Bool :=
  vecCode (vecCode e n) n d

/-- Read a fixed coordinate by walking the encoded list. -/
noncomputable def coordinate (e : β → List Bool) (d : β) {n : ℕ} (i : Fin n) :
    Procedure (vecCode e n) e (fun v => v i) := by
  let input : Procedure (vecCode e n) (listCode e) (fun v : Fin n → β => List.ofFn v) :=
    (Procedure.identity (listCode e)).precompose List.ofFn
  let index := Procedure.constant (vecCode e n) Nat.bits i.val
  apply ((Procedure.listGet e d).comp (index.pair input)).congrFun
  intro v
  change ((List.ofFn v).drop i.val).headD d = v i
  simp [List.head?_drop]

/-- Build a fixed-arity encoded list from truly computed component words. -/
noncomputable def assemble (ea : α → List Bool) (eb : β → List Bool) :
    (n : ℕ) → (f : α → Fin n → β) → (∀ i, Procedure ea eb (fun a => f a i)) →
      Procedure ea (vecCode eb n) f
  | 0, f, _ => (Procedure.constant ea (listCode eb) ([] : List β)).result (by
      intro a; simp [vecCode])
  | n+1, f, p => by
    let tail := assemble ea eb n (fun a i => f a i.succ) (fun i => p i.succ)
    let listTail : Procedure ea (listCode eb) (fun a => List.ofFn fun i : Fin n => f a i.succ) :=
      tail.result (fun _ => rfl)
    exact ((Procedure.listCons eb).comp ((p 0).pair listTail)).result (by
      intro a; change listCode eb (_ :: _) = listCode eb (List.ofFn (f a)); rw [List.ofFn_succ])

/-- Build a square matrix in its ordinary row-list encoding. -/
noncomputable def assembleMatrix (ea : α → List Bool) (eb : β → List Bool) (n : ℕ)
    (f : α → Fin n → Fin n → β) (p : ∀ i j, Procedure ea eb (fun a => f a i j)) :
    Procedure ea (matrixCode eb n) f :=
  assemble ea (vecCode eb n) n f (fun i => assemble ea eb n (fun a => f a i) (p i))

/-- Read a cell using two charged list walks. -/
noncomputable def readMatrix (eb : β → List Bool) (default : β) {n : ℕ} (i j : Fin n) :
    Procedure (matrixCode eb n) eb (fun m => m i j) :=
  (coordinate eb default j).comp (coordinate (vecCode eb n) (fun _ => default) i)

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
