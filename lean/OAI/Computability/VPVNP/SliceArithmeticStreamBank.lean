import OAI.Computability.VPVNP.SliceArithmeticRow
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Arithmetic registers and stream ports for the finite Horner control -/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticStreamRow

open BurstRAM RAMTape

/-- The caller supplies its own disjoint ports for the loop markers and saved inputs. -/
inductive StreamPort (X : Type) where
  | old | coeff | factor | out | scratch | outer (x : X)
  deriving DecidableEq, Fintype

/-- Eight-register arithmetic bank and coefficient-stream ports used by a Horner row, including
the caller's ports of type `X`. -/
abbrev Port (X : Type) := Sum (ISA.Port 8 0) (StreamPort X)

/-- The finite arithmetic register bank and the caller's stream stacks. -/
def state {X : Type} {w : ℕ} (reg : Fin 8 → Word w) (streams : Stacks (StreamPort X)) :
    Stacks (Port X) := Sum.elim (ISA.bank Fin.elim0 0 reg []) streams

variable {X : Type} [DecidableEq X] {w : ℕ}

theorem updateStream (reg : Fin 8 → Word w) (streams : Stacks (StreamPort X))
    (s : StreamPort X) (bits : List Bool) :
    Function.update (state reg streams) (.inr s) bits = state reg (Function.update streams s bits) := by
  funext i
  cases i with
  | inl i => simp [state]
  | inr i => by_cases h : i = s <;> simp [state, h]

theorem updateReg (reg : Fin 8 → Word w) (streams : Stacks (StreamPort X))
    (i : Fin 8) (x : Word w) :
    Function.update (state reg streams) (.inl (.reg i)) (wordBits x) =
      state (Function.update reg i x) streams := by
  funext j
  cases j with
  | inr j => simp [state]
  | inl j =>
    have h := congrFun (ISA.bank_updateReg (k := 0) Fin.elim0 0 reg [] i x) j
    by_cases he : j = .reg i <;> simp_all [state]

theorem bankRun (routine : FiniteRoutine (ISA.Port 8 0)) (streams : Stacks (StreamPort X))
    {reg next : Fin 8 → Word w} {t : ℕ}
    (hr : routine.Runs t (ISA.bank Fin.elim0 0 reg []) (ISA.bank Fin.elim0 0 next [])) :
    (routine.onPorts Sum.inl).Runs t (state reg streams) (state next streams) := by
  apply routine.runs_onPorts_framed Sum.inl_injective hr (fun _ => rfl) (fun _ => rfl)
  rintro (j | j) hj
  · exact (hj j rfl).elim
  · rfl

end SliceArithmeticStreamRow

end VPVNP
end Computability
end OAI
