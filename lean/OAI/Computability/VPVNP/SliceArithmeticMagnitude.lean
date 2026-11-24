import OAI.Computability.VPVNP.EvaluatorRadixDivision
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-!
# Reducing an arbitrary-width count to one residue limb

A positive working-width divisor and a little-endian count may have different
lengths. The bit division routine computes the remainder at the divisor width.
Its unused quotient is erased before the residue returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticMagnitude

open BurstRAM RAMTape TapeWord DivisionStack

private def divide : FiniteRoutine Port := .ofStackCode code id .reverseInput (· == .done)

/-- Divide a little-endian count by the advised modulus and discard the quotient, leaving the
remainder. -/
def machine : FiniteRoutine Port := divide.followedBy (SliceArithmetic.CallClear.clear .quotient)

/-- Division stack state holding the count, divisor, and remainder stream with the other work
stacks empty. -/
def frame (input divisor residue : List Bool) : Stacks Port :=
  (⟨input, [], divisor, residue, [], [], [], []⟩ : Data).stacks

/-- Number of steps to reduce an `n`-bit count modulo a positive `w`-bit divisor and erase the
quotient. -/
def cost (n w : ℕ) := 2 * n + 5 * w + 3 + (n * (10 * w + 4) + 1) + (n + 1)

theorem machine_runs {w : ℕ} (x : List Bool) (d : Word w) (hd : 0 < d.val) :
    machine.Runs (cost x.length w) (frame x (wordBits d) [])
      (frame [] (wordBits d) (wordBits (Fin.ofNat (2^w) (value x % d.val)))) := by
  let ds := wordBits d
  let out := divideWords x ds
  let mid := (⟨[], [], ds, out.2, out.1, [], [], []⟩ : Data).stacks
  have hd' : 0 < value ds := by simpa only [ds, value_wordBits] using hd
  obtain ⟨hq, hr, _, hv⟩ := EvaluatorRadixDivision.divide_spec x ds hd'
  have hbits : out.2 = wordBits (Fin.ofNat (2^w) (value x % d.val)) := by
    apply eq_of_length_value
    · simpa only [ds, length_wordBits] using hr
    · simpa only [ds, value_wordBits, Fin.val_ofNat, Nat.mod_eq_of_lt ((Nat.mod_lt _ hd).trans d.isLt)] using hv
  have hdiv : divide.Runs (ticks x ds) (frame x ds []) mid := by
    apply FiniteRoutine.runs_ofStackCode_framed (ports := id) Function.injective_id
      (normal := (· == State.done)) (entry := State.reverseInput) (exit := State.done) rfl rfl
      (fun q h => by
        have : q = State.done := by simpa using h
        subst q
        rfl)
      (divideRun x ds) (fun _ => rfl) (fun _ => rfl) (fun i hi => (hi i rfl).elim)
  have hclear := SliceArithmetic.CallClear.clear_runs .quotient mid
  have hfinal : Function.update mid .quotient [] = frame [] ds out.2 := by
    funext i
    cases i <;> rfl
  rw [hfinal, hbits, show (mid .quotient).length = x.length from hq] at hclear
  have hclock : cost x.length w = ticks x ds + (x.length + 1) := by
    simp only [cost, ticks, (anyBit_iff ds).mpr hd', ↓reduceIte, ds, length_wordBits]
  rw [hclock]
  exact hdiv.followedBy hclear

end SliceArithmeticMagnitude

end VPVNP
end Computability
end OAI
