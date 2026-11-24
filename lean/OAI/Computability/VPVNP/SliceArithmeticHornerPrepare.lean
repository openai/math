import OAI.Computability.VPVNP.SliceArithmeticStreamBank
import OAI.Computability.VPVNP.SliceArithmeticStreamStage
import OAI.Computability.VPVNP.SliceArithmeticStreamWord

/-!
# Preparing the bit stacks for a Horner digit

Each digit reuses the stored modulus and multiplier. The machine restores the
row count, loads the next high-degree-first digit, clears the predecessor and
negates the accumulator's top coefficient left in register six by the last
round. A single whole-stack reversal installs the output for the next round.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.HornerControl

open RAMTape BurstRAM SliceArithmeticStreamRow

/-- Ports holding the saved modulus coefficients, multiplier and row count, together with the
live row, digit, and round streams. -/
inductive Extra where
  | savedCoeff | savedFactor | savedCount | rows | digits | rounds
  deriving DecidableEq

instance : Fintype Extra :=
  ⟨{.savedCoeff, .savedFactor, .savedCount, .rows, .digits, .rounds}, by intro x; cases x <;> simp⟩

/-- Register and stream ports of the complete Horner multiplication controller. -/
abbrev Ports := Port Extra

/-- State of the saved polynomial and multiplier streams, unary row counts, pending digit bits,
and remaining rounds. -/
def extra (c b : List Bool) (e : ℕ) (digits : List Bool) (left rows : ℕ) : Stacks Extra
  | .savedCoeff => c
  | .savedFactor => b
  | .savedCount => List.replicate e true
  | .rows => List.replicate rows true
  | .digits => digits
  | .rounds => List.replicate left true

/-- Install the old accumulator, reduction coefficients, multiplier coefficients, and output
bits alongside the caller's streams. -/
def streams (old coeff factor out : List Bool) (caller : Stacks Extra) : Stacks (StreamPort Extra)
  | .old => old
  | .coeff => coeff
  | .factor => factor
  | .out => out
  | .scratch => []
  | .outer x => caller x

private def supplyPort : StreamStage.Port → Ports
  | .coefficient => .inr (.outer .savedCoeff)
  | .factor => .inr (.outer .savedFactor)
  | .count => .inr (.outer .savedCount)
  | .coefficientInput => .inr .coeff
  | .factorInput => .inr .factor
  | .countInput => .inr (.outer .rows)
  | .scratch => .inr .scratch

private theorem supplyPort_injective : Function.Injective supplyPort := by
  intro i j h
  cases i <;> cases j <;> simp_all [supplyPort]

private def supply : FiniteRoutine Ports := StreamStage.stage.onPorts supplyPort

private theorem supply_runs {w : ℕ} (reg : Fin 8 → BurstRAM.Word w)
    (c b old digits : List Bool) (e left : ℕ) :
    supply.Runs (5 * (c.length + b.length + e) + 6)
      (state reg (streams old [] [] [] (extra c b e digits left 0)))
      (state reg (streams old c b [] (extra c b e digits left e))) := by
  have run := StreamStage.stage_runs c b (List.replicate e true)
  rw [List.length_replicate] at run
  apply StreamStage.stage.runs_onPorts_framed supplyPort_injective run
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · rintro (k | k) h
    · rfl
    · cases k with
      | old | out | scratch => rfl
      | coeff => exact (h .coefficientInput rfl).elim
      | factor => exact (h .factorInput rfl).elim
      | outer x =>
        cases x with
        | savedCoeff | savedFactor | savedCount | digits | rounds => rfl
        | rows => exact (h .countInput rfl).elim

/-- Stage the row inputs, load the next Horner digit, clear the predecessor, and negate the top
accumulator limb for reduction. -/
def prepare : FiniteRoutine Ports :=
  ((supply.followedBy (StreamWord.load (.inr (.outer .digits)) (.inl (.reg 4)) (.inr .scratch))).followedBy
    ((ISA.loadLiteral 0 1).onPorts Sum.inl)).followedBy
    ((Word.routine .neg 2 6 6 0).onPorts Sum.inl)

/-- The register changes at the start of a Horner round. -/
def prepared {p w : ℕ} (reg : Fin 8 → BurstRAM.Word w) (digit top : Fin p) :
    Fin 8 → BurstRAM.Word w :=
  Function.update (Function.update (Function.update reg 4 (Word.limb w digit)) 1 0) 2 (Word.limb w (-top))

theorem prepare_runs {p w : ℕ} [NeZero p] (hw : Word.workingWidth p ≤ w)
    (reg : Fin 8 → BurstRAM.Word w) (digit top : Fin p)
    (hp : (reg 0).val = p) (ht : (reg 6).val = top.val)
    (c b old tail : List Bool) (e left : ℕ) :
    ∃ t ≤ 5 * (c.length + b.length + e) + 13 * w + 11 + 200 * (w + 1)^2,
      prepare.Runs t
        (state reg (streams old [] [] []
          (extra c b e (wordBits (Word.limb w digit) ++ tail) left 0)))
        (state (prepared reg digit top) (streams old c b [] (extra c b e tail left e))) := by
  let x := Word.limb w digit
  let input := streams old c b [] (extra c b e (wordBits x ++ tail) left e)
  let target := streams old c b [] (extra c b e tail left e)
  let r₁ := Function.update reg 4 x
  let r₂ := Function.update r₁ 1 (0 : BurstRAM.Word w)
  have hs := supply_runs reg c b old (wordBits x ++ tail) e left
  have hload := StreamWord.load_runs (stream := (.inr (.outer .digits) : Ports))
    (reg := .inl (.reg 4)) (scratch := .inr .scratch) (by decide) (by decide) (by decide)
    (state reg input) x tail (length_wordBits _) rfl rfl
  have tailEq : Function.update input (.outer .digits) tail = target := by
    funext i
    cases i with
    | outer y => cases y <;> simp [input, target, streams, extra, Function.update]
    | _ => rfl
  rw [updateStream, tailEq, updateReg] at hload
  have hclear := bankRun (ISA.loadLiteral 0 1) target (ISA.loadLiteral_run 0 1 Fin.elim0 0 r₁ [])
  obtain ⟨t, hticks, hneg⟩ := Word.routine_runs hw .neg 2 6 6 0 (by decide) Fin.elim0 0 r₂ []
    top top (by simpa [r₂, r₁] using ht) (by simpa [r₂, r₁] using ht) (by simpa [r₂, r₁] using hp)
  have hlast := bankRun (Word.routine .neg 2 6 6 0) target hneg
  exact ⟨_, by omega, ((hs.followedBy hload).followedBy hclear).followedBy hlast⟩

/-- Replace the consumed accumulator by the coefficient scan's bit-reversed output. -/
def restore : FiniteRoutine Ports :=
  EvaluatorRadixDivision.reverseOnto (.inr .out) (.inr .old)

theorem restore_runs {w : ℕ} (reg : Fin 8 → BurstRAM.Word w) (bits : List Bool)
    (caller : Stacks Extra) :
    restore.Runs (2 * bits.length + 1)
      (state reg (streams [] [] [] bits.reverse caller))
      (state reg (streams bits [] [] [] caller)) := by
  rw [← List.length_reverse (as := bits)]
  apply EvaluatorRadixDivision.reverseOnto_runs (src := (.inr .out : Ports)) (dst := .inr .old)
      (by decide) (state reg (streams [] [] [] bits.reverse caller))
      (state reg (streams bits [] [] [] caller)) rfl
  · change bits = bits.reverse.reverse ++ []
    simp
  · rintro (k | k) h₁ h₂
    · rfl
    · cases k <;> first | rfl | contradiction

end SliceArithmetic.HornerControl

end VPVNP
end Computability
end OAI
