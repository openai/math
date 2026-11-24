import OAI.Computability.VPVNP.SliceArithmeticWord
import Mathlib.Tactic.FinCases
import Mathlib.Data.ZMod.Defs

/-! # Subtracting canonical prime residues in the evaluator's register bank -/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticSubtract

open RAMTape ISA BurstRAM SliceArithmetic.Word

/-- Negate the negative-count residue modulo the prime and add it to the positive-count residue
in register one. -/
def machine : FiniteRoutine (Port 3 0) :=
  (routine .neg 2 2 2 0).followedBy (routine .add 1 1 2 0)

/-- The modulus, positive-count residue, and negative-count residue in subtraction-register
order. -/
def registers {w : ℕ} (prime positive negative : Word w) : Fin 3 → Word w := ![prime, positive, negative]

theorem machine_runs {p w : ℕ} [NeZero p] (hw : workingWidth p ≤ w) (prime : Word w)
    (hp : prime.val = p) (a b : Fin p) :
    ∃ t ≤ 400 * (w + 1)^2, machine.Runs t
      (bank Fin.elim0 0 (registers prime (limb w a) (limb w b)) [])
      (bank Fin.elim0 0 (registers prime (limb w (a - b)) (limb w (-b))) []) := by
  let input := registers prime (limb w a) (limb w b)
  let middle := Function.update input 2 (limb w (-b))
  obtain ⟨m, hm, hneg⟩ := routine_runs hw .neg 2 2 2 0 (by decide) Fin.elim0 0 input [] b b
    (limb_val hw b) (limb_val hw b) hp
  obtain ⟨n, hn, hadd⟩ := routine_runs hw .add 1 1 2 0 (by decide) Fin.elim0 0 middle [] a (-b)
    (by simpa [middle, input, registers] using limb_val hw a) (by simp [middle, limb_val hw])
    (by simpa [middle, input, registers] using hp)
  have hfinal : Function.update middle 1 (limb w (a + -b)) = registers prime (limb w (a-b)) (limb w (-b)) := by
    funext i
    fin_cases i <;> simp [middle, input, registers]
    exact congrArg (limb w) (sub_eq_add_neg a b).symm
  simp only [Op.eval] at hadd
  rw [hfinal] at hadd
  exact ⟨_, by omega, hneg.followedBy hadd⟩

end SliceArithmeticSubtract

end VPVNP
end Computability
end OAI
