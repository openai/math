import OAI.Computability.VPVNP.RankQueryStackEngineSpec
import OAI.Computability.VPVNP.SliceArithmeticMultiplyCall

/-! # Reading a weighted Gram coefficient on the determinant machine

A nonzero Gram descriptor specifies two rows and a shared column. The first
entry read writes directly to the multiplier's query stack and the second to
its accumulator. Both reads see the same persistent Macaulay description.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open RAMTape Engine

/-- Stack addresses for reading one matrix entry, comprising its row and column words, the
packed scalar result and the reader's auxiliary storage. -/
inductive Port (K : Type) where
  | row | col | result | aux (k : K)
  deriving DecidableEq, Fintype

/-- Encode row `i` and column `j` as `w`-bit words alongside the supplied result stack and
auxiliary state of the entry reader. -/
def bank {K : Type} (w i j : ℕ) (result : List Bool) (aux : Stacks K) : Stacks (Port K)
  | .row => UniversalCountStack.digits w i
  | .col => UniversalCountStack.digits w j
  | .result => result
  | .aux k => aux k

/-- Calling convention for a single coefficient of the advised relation matrix. -/
def Correct {K : Type} [DecidableEq K] {p e n m : ℕ} {c : SliceArithmetic.Vector p e}
    (read : FiniteRoutine (Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c)) (w v B : ℕ)
    (ready : Stacks K → Prop) : Prop :=
  ∀ (i : Fin n) (j : Fin m) (aux : Stacks K), ready aux →
    ∃ t ≤ B, ∃ out, ready out ∧ read.Runs t (bank w i j [] aux) (bank w i j (scalar v (M i j)) out)

end RankQuery.Stack.MacaulayRead

namespace RankQuery.Stack.GramRead

open RAMTape Engine

/-- Ports for reading two entries in a common column, with separate row words, one column word,
a field multiplier and shared reader storage. -/
inductive Port (K : Type) where
  | first | second | column | arithmetic (k : SliceArithmetic.MultiplyCall.Port) | aux (k : K)
  deriving DecidableEq, Fintype

variable {K : Type}

/-- Route an entry read through the chosen row and common column. The first result goes to the
multiplier's query stack and the second to its accumulator. -/
def readPorts (second : Bool) : MacaulayRead.Port K → Port K
  | .row => if second then .second else .first
  | .col => .column
  | .result => .arithmetic (.inr (if second then .acc else .query))
  | .aux k => .aux k

theorem readPorts_injective (second : Bool) : Function.Injective (readPorts (K := K) second) := by
  intro x y h
  cases second <;> cases x <;> cases y <;> simp_all [readPorts]

/-- Read `M i k` and `M j k` from the shared column `k`, then multiply the two packed entries
in the field accumulator. -/
def machine (read : FiniteRoutine (MacaulayRead.Port K)) : FiniteRoutine (Port K) :=
  ((read.onPorts (readPorts false)).followedBy (read.onPorts (readPorts true))).followedBy
    (SliceArithmetic.MultiplyCall.machine.onPorts Port.arithmetic)

/-- Pack row indices `i` and `j` and their shared column `k` into `w`-bit words alongside the
multiplier stacks and the reader's auxiliary bank. -/
def bank (w i j k : ℕ) (s : Stacks SliceArithmetic.MultiplyCall.Port) (aux : Stacks K) : Stacks (Port K)
  | .first => UniversalCountStack.digits w i
  | .second => UniversalCountStack.digits w j
  | .column => UniversalCountStack.digits w k
  | .arithmetic z => s z
  | .aux z => aux z

open SliceArithmetic.MultiplyCall (clean external callCap)
open SliceArithmeticRound (packed)

variable [DecidableEq K] {p e n m w v B : ℕ} [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- Prepare the multiplier with packed modulus coefficients `c` at limb width `v`, the supplied
query and accumulator stacks, and clean internal work stacks. -/
def arithmeticBank (v : ℕ) (c : SliceArithmetic.Vector p e) (query acc : List Bool) :=
  clean (external p e v (packed v (List.ofFn c)) query acc)

/-- Two physical reads followed by the fixed polynomial-basis multiplier. -/
theorem machine_runs (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.Correct read M w v B ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v)
    (i j : Fin n) (k : Fin m) (s : Stacks K) (hs : ready s) :
    ∃ t ≤ 2*B + callCap e v, ∃ out, ready out ∧ (machine read).Runs t
      (bank w i j k (arithmeticBank v c [] []) s)
      (bank w i j k (arithmeticBank v c [] (scalar v (M i k * M j k))) out) := by
  let a := M i k
  let b := M j k
  let ab := scalar v a
  let bb := scalar v b
  obtain ⟨t₁,h₁,s₁,hs₁,r₁⟩ := hc i k s hs
  obtain ⟨t₂,h₂,s₂,hs₂,r₂⟩ := hc j k s₁ hs₁
  have l : (read.onPorts (readPorts false)).Runs t₁
      (bank w i j k (arithmeticBank v c [] []) s)
      (bank w i j k (arithmeticBank v c ab []) s₁) := by
    apply read.runs_onPorts_framed (readPorts_injective false) r₁
    · intro z; cases z <;> rfl
    · intro z; cases z <;> rfl
    · intro z hz
      cases z with
      | aux x => exact (hz (.aux x) rfl).elim
      | arithmetic x =>
        rcases x with x | x
        · rfl
        · cases x <;> first | rfl | exact (hz .result rfl).elim
      | _ => rfl
  have r : (read.onPorts (readPorts true)).Runs t₂
      (bank w i j k (arithmeticBank v c ab []) s₁)
      (bank w i j k (arithmeticBank v c ab bb) s₂) := by
    apply read.runs_onPorts_framed (readPorts_injective true) r₂
    · intro z; cases z <;> rfl
    · intro z; cases z <;> rfl
    · intro z hz
      cases z with
      | aux x => exact (hz (.aux x) rfl).elim
      | arithmetic x =>
        rcases x with x | x
        · rfl
        · cases x <;> first | rfl | exact (hz .result rfl).elim
      | _ => rfl
  obtain ⟨t₃,h₃,r₃⟩ := SliceArithmetic.MultiplyCall.machine_runs (NeZero.pos e) hw c a.digits b.digits
  have mrun : (SliceArithmetic.MultiplyCall.machine.onPorts (Port.arithmetic (K := K))).Runs t₃
      (bank w i j k (arithmeticBank v c ab bb) s₂)
      (bank w i j k (arithmeticBank v c [] (scalar v (a*b))) s₂) := by
    apply SliceArithmetic.MultiplyCall.machine.runs_onPorts_framed (fun _ _ h => Port.arithmetic.inj h) r₃
    · intro z; rfl
    · intro z; rw [Scalar.product_eq]; simp only [scalar, Scalar.digits_pack]; rfl
    · intro z hz; cases z <;> first | rfl | exact (hz _ rfl).elim
  exact ⟨_, by omega, s₂, hs₂, (l.followedBy r).followedBy mrun⟩

end RankQuery.Stack.GramRead

end VPVNP
end Computability
end OAI
