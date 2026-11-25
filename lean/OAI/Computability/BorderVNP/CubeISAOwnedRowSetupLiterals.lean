import OAI.Computability.BorderVNP.RoutingISACubeConstantRun
import OAI.Computability.BorderVNP.RoutingISADeterministic
import OAI.Computability.BorderVNP.DiagonalTallyPacketBank

/-! # Literal packet parameters for the owned row iterator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedRowSetup

open VPVNP.BurstRAM Cube Cube.Tally Constants

/-- Install the selector bit width, number of selectors and packet bank stride. -/
def parameters (n b h K s : ℕ) : Code := .block [
  .constant 57 1, literal (digits (selectorWidth n K h)), .copy 8 58,
  literal (digits (Fintype.card (Selector n K h))), .copy 9 58,
  literal (digits (bankWidth n b h K s)), .copy 16 58]

/-- The fixed parameters are synthesized by deterministic ordinary instructions. -/
theorem parameters_deterministic (n b h K s : ℕ) : (parameters n b h K s).deterministic = true := by
  have det (bits : List Bool) : (literal bits).deterministic = true := by
    induction bits with
    | nil => rfl
    | cons bit bits ih => cases bit <;> simp [literal, Code.deterministic, ih]
  simp [parameters, Code.block, Code.deterministic, det]

/-- Literal synthesis preserves the sign and consumes no branch choices. -/
theorem parameters_unsigned (n b h K s : ℕ) : (parameters n b h K s).unsigned = true := by
  simp [parameters, Code.block, Code.unsigned, (literal_unsigned _).1]

/-- Native synthesis supplies the three packet parameters, retaining all other
caller registers outside the two synthesis registers and preserving memory. -/
theorem parameters_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (n b h K s : ℕ)
    (widthFit : selectorWidth n K h < 2^w) (countFit : Fintype.card (Selector n K h) < 2^w)
    (strideFit : bankWidth n b h K s < 2^w) (hw : 1 < 2^w) :
    BoundedRun pub mac (parameters n b h K s) r m (parameters n b h K s).slots (fun z =>
      z.reg 8 = selectorWidth n K h ∧ z.reg 9 = Fintype.card (Selector n K h) ∧
      z.reg 16 = bankWidth n b h K s ∧
      (∀ j : Reg, j ≠ 8 → j ≠ 9 → j ≠ 16 → j ≠ 57 → j ≠ 58 → z.reg j = readings r j) ∧
      z.mem = readings m) := by
  simp at countFit
  have safe (x : ℕ) (z : NatState) (one : z.reg 57 = 1) (room : x < 2^w) :=
    (literal_word_effect x w (readings pub) z one room).1
  have value (x : ℕ) (z : NatState) (one : z.reg 57 = 1) (room : x < 2^w) :=
    (literal_word_effect x w (readings pub) z one room).2
  apply (Code.runFixed _ pub mac r m ?_).mono le_rfl
  · rintro _ rfl
    simp (config := {decide := true}) [parameters, Code.block, Code.fixedEval, Code.evalNat,
      NatState.ofWords, value, widthFit, countFit, strideFit]
    intro j h8 h9 h16 h57 h58
    simp [h8, h9, h16, h57, h58]
  · simp (config := {decide := true}) [parameters, Code.block, Code.fixedSafe, Code.safeReadOnly,
      Code.fixedEval, Code.evalNat, NatState.ofWords, value, safe, widthFit, countFit, strideFit, hw]

end RoutingISA.OwnedRowSetup

end BorderVNP
end Computability
end OAI
