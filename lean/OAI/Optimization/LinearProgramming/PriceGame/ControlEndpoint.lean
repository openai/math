import OAI.Optimization.LinearProgramming.OracleSpec.CampaignPlay
import OAI.Optimization.LinearProgramming.OracleSpec.PriceUniform
import OAI.Optimization.LinearProgramming.PriceGame.ControlSign
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWirePolynomial

/-! Specialize the independent oracle-machine theorem to the paper's single fixed public
campaign, including its concrete program, terminal sign, saved bit tape and full clock. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open OracleSpec ExactQuantumFactoring.BitStackProgram

noncomputable def campaignWidthPolynomial : Polynomial ℕ :=
  Wire.dialoguePolynomial.comp (2 * Polynomial.X)

noncomputable def campaignRoundPolynomial : Polynomial ℕ :=
  Wire.queryPolynomial.comp (2 * Polynomial.X) + 1

/-- The operational clock of the binary-input machine, including conversion to the
internal public header and every query, reply, read, write and internal instruction. -/
noncomputable def campaignMachineClock
    (machine : Dialogue.ProcedureOf eiPad ecPad (dispatch (campaignSolver Campaign.rounds))) :
    Polynomial ℕ :=
  totalClock machine.shared.bound campaignWidthPolynomial campaignRoundPolynomial

/-- The guarantee is for the literal padded program built from the supplied fixed
dispatcher. In particular, the program can be embedded unchanged into another machine. -/
theorem campaignProgram_correct
    (machine : Dialogue.ProcedureOf eiPad ecPad (dispatch (campaignSolver Campaign.rounds))) :
    ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (a : Fin N) (reply : Transcript → Word → Bool),
      (Dialogue.paddedMachine machine).ComputesWithin (fun history query => [reply history query])
        (priceInput R a) ((campaignMachineClock machine).eval 1 *
          (N+(R+1).log2+1)^(campaignMachineClock machine).natDegree) (pricePost R a) := by
  let first (N R : ℕ) (a : Fin N) : PublicInput := ⟨N,R,a⟩
  let solver (N R : ℕ) (a : Fin N) := campaignSolver Campaign.rounds (first N R a)
  refine paddedPriceProgram_correct machine first campaignWidthPolynomial campaignRoundPolynomial
    solver ?_ ?_ ?_
  · intro N R a
    rfl
  · intro N R _ hR a h answer legal
    exact campaignSolver_recover (first N R a) hR h answer legal
  · intro N R _ _ a reply
    dsimp only
    let i := first N R a
    let x := N + (R+1).log2 + 1
    let y := Campaign.inputSize N R
    have hxy : y ≤ 2*x := Campaign.inputSize_le_machine N R
    have hw : Wire.dialoguePolynomial.eval y ≤ campaignWidthPolynomial.eval x := by
      simpa only [campaignWidthPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,
        Polynomial.eval_ofNat,Polynomial.eval_X] using Procedure.eval_nat_mono Wire.dialoguePolynomial hxy
    have hc : Wire.queryPolynomial.eval y+1 ≤ campaignRoundPolynomial.eval x := by
      simpa only [campaignRoundPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X] using
        Nat.add_le_add_right (Procedure.eval_nat_mono Wire.queryPolynomial hxy) 1
    obtain ⟨n,hn,protocol⟩ := Wire.reference_session_polynomial i reply
    refine ⟨Wire.dialoguePolynomial.eval y,n,hw,hn.trans hc,?_⟩
    simpa only [solver,serializedPlay_eq_wirePlay] using protocol

/-- Specialize the principal comparator to the paper's fixed dispatcher. -/
theorem extremalSignRecovery_of_campaignProcedure
    (machine : Dialogue.ProcedureOf eiPad ecPad (dispatch (campaignSolver Campaign.rounds))) :
    OracleSpec.ExtremalSignRecovery :=
  ⟨Dialogue.paddedMachine machine, (campaignMachineClock machine).eval 1,
    (campaignMachineClock machine).natDegree, campaignProgram_correct machine⟩

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
