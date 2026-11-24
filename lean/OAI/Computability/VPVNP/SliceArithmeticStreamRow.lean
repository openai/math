import OAI.Computability.VPVNP.SliceArithmeticStreamBank
import OAI.Computability.VPVNP.SliceArithmeticStreamWord

/-!
# One streamed Horner row on bit stacks

The fixed control reads the next modulus and multiplier coefficients, runs the
four residue operations, emits the resulting limb, and saves the old
accumulator coefficient for the next row. The output is built in reverse bit
order so a single stack reversal restores all limbs to their input order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticStreamRow

open BurstRAM RAMTape SliceArithmetic.Word SliceArithmetic.StreamWord SliceArithmeticRow

variable {X : Type} {w p : ℕ}

/-- Consume the next limb from stream `s` and load it into arithmetic register `i`. -/
def loadLimb (s : StreamPort X) (i : Fin 8) : FiniteRoutine (Port X) :=
  load (.inr s) (.inl (.reg i)) (.inr .scratch)

/-- Store the result from register six on the output stack in reversed bit order for the final
reversal. -/
def emit : FiniteRoutine (Port X) :=
  storeReverse (.inr .out) (.inl (.reg 6)) (.inr .scratch) (.inl (.work 0))

/-- Read a modulus limb and a multiplier limb, compute and emit the row result, then load the
next shifted predecessor. -/
def body : FiniteRoutine (Port X) :=
  ((((loadLimb .coeff 3).followedBy (loadLimb .factor 5)).followedBy
    (row.onPorts Sum.inl)).followedBy emit).followedBy (loadLimb .old 1)

/-- Register contents after a Horner row, including its result, second product, and the old
accumulator limb needed by the next row. -/
def nextRegisters (reg : Fin 8 → BurstRAM.Word w)
    (prev reduction c digit b old : Fin p) : Fin 8 → BurstRAM.Word w :=
  let loaded := Function.update (Function.update reg 3 (limb w c)) 5 (limb w b)
  Function.update (rowRegisters loaded prev reduction c digit b) 1 (limb w old)

/-- Stream contents after one Horner row, with consumed inputs replaced by their tails and the
emitted result on the output. -/
def nextStreams (streams : Stacks (StreamPort X))
    (oldTail coeffTail factorTail resultBits : List Bool) : Stacks (StreamPort X)
  | .old => oldTail
  | .coeff => coeffTail
  | .factor => factorTail
  | .out => resultBits.reverse ++ streams .out
  | s => streams s

variable [DecidableEq X]

theorem loadLimb_runs {s : StreamPort X} (hs : s ≠ .scratch) (i : Fin 8)
    (reg : Fin 8 → BurstRAM.Word w) (streams : Stacks (StreamPort X))
    (x : BurstRAM.Word w) (tail : List Bool) (hread : streams s = wordBits x ++ tail)
    (ht : streams .scratch = []) :
    (loadLimb s i).Runs (5 * w + 2) (state reg streams)
      (state (Function.update reg i x) (Function.update streams s tail)) := by
  have run := load_runs (stream := Sum.inr s) (reg := Sum.inl (ISA.Port.reg i : ISA.Port 8 0))
    (scratch := .inr .scratch) (by simp) (by simpa using hs) (by simp)
    (state reg streams) x tail (length_wordBits (reg i)) hread ht
  rwa [updateStream, updateReg] at run

theorem emit_runs (reg : Fin 8 → BurstRAM.Word w) (streams : Stacks (StreamPort X))
    (ht : streams .scratch = []) :
    emit.Runs (7 * w + 3) (state reg streams)
      (state reg (Function.update streams .out ((wordBits (reg 6)).reverse ++ streams .out))) := by
  have run := storeReverse_runs (stream := Sum.inr (.out : StreamPort X)) (reg := .inl (.reg 6))
    (scratch := .inr .scratch) (tmp := .inl (.work 0)) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (state reg streams) (reg 6) rfl ht rfl
  rwa [updateStream] at run

theorem body_runs [NeZero p] (hw : workingWidth p ≤ w)
    (reg : Fin 8 → BurstRAM.Word w) (streams : Stacks (StreamPort X))
    (prev reduction c digit b old : Fin p) (oldTail coeffTail factorTail : List Bool)
    (hp : (reg 0).val = p) (hprev : (reg 1).val = prev.val)
    (hred : (reg 2).val = reduction.val) (hd : (reg 4).val = digit.val)
    (hold : streams .old = wordBits (limb w old) ++ oldTail)
    (hc : streams .coeff = wordBits (limb w c) ++ coeffTail)
    (hb : streams .factor = wordBits (limb w b) ++ factorTail) (ht : streams .scratch = []) :
    ∃ t ≤ 800 * (w + 1) ^ 2 + 22 * w + 9, body.Runs t (state reg streams)
      (state (nextRegisters reg prev reduction c digit b old)
        (nextStreams streams oldTail coeffTail factorTail (wordBits (limb w (prev + reduction * c + digit * b))))) := by
  let r₁ := Function.update reg 3 (limb w c)
  let s₁ := Function.update streams .coeff coeffTail
  let r₂ := Function.update r₁ 5 (limb w b)
  let s₂ := Function.update s₁ .factor factorTail
  let r₃ := rowRegisters r₂ prev reduction c digit b
  let s₃ := Function.update s₂ .out ((wordBits (r₃ 6)).reverse ++ s₂ .out)
  have run₁ := loadLimb_runs (by simp) 3 reg streams (limb w c) coeffTail hc ht
  have run₂ := loadLimb_runs (s := .factor) (by simp) 5 r₁ s₁ (limb w b) factorTail
    (by simpa [s₁] using hb) (by simpa [s₁] using ht)
  obtain ⟨n, hn, run₃⟩ := row_runs hw Fin.elim0 0 r₂ [] prev reduction c digit b
    (by simpa [r₂, r₁] using hp) (by simpa [r₂, r₁] using hprev)
    (by simpa [r₂, r₁] using hred) (by simp [r₂, r₁, limb_val hw])
    (by simpa [r₂, r₁] using hd) (by simp [r₂, limb_val hw])
  have arithmetic := bankRun row s₂ run₃
  have run₄ := emit_runs r₃ s₂ (by simpa [s₂, s₁] using ht)
  have run₅ := loadLimb_runs (s := .old) (by simp) 1 r₃ s₃ (limb w old) oldTail
    (by simpa [s₃, s₂, s₁] using hold) (by simpa [s₃, s₂, s₁] using ht)
  have hstreams : Function.update s₃ .old oldTail =
      nextStreams streams oldTail coeffTail factorTail (wordBits (limb w (prev + reduction * c + digit * b))) := by
    funext s
    cases s <;> simp [s₃, s₂, s₁, r₃, rowRegisters, nextStreams]
  rw [hstreams] at run₅
  exact ⟨_, by omega, (((run₁.followedBy run₂).followedBy arithmetic).followedBy run₄).followedBy run₅⟩

end SliceArithmeticStreamRow

end VPVNP
end Computability
end OAI
