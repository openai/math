import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchEffectiveNamed
import OAI.Computability.NearSquareRoot.FixedCandidateCRTProcedureProfile
import OAI.Computability.NearSquareRoot.FixedCandidateNativeFiles

/-! # The two effective CRT procedures for the joint multiplication selector -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters

open IntegerMultiplication Code Space DigitPacking FixedPoint Controlled CRTStream

noncomputable section

private theorem mid_pos (j : ℕ) : 0 ≤ Generator.midExponent j := by unfold Generator.midExponent; positivity

private theorem mid_le_one (j : ℕ) : Generator.midExponent j ≤ 1 := by
  have hd : 0 < 2*((j:ℝ)+2) := by positivity
  have h : 1/(2*((j:ℝ)+2)) ≤ (1:ℝ)/2 := (div_le_iff₀ hd).2 (by nlinarith [(show 0 ≤ (j:ℝ) by positivity)])
  unfold Generator.midExponent
  linarith

set_option maxHeartbeats 2800000 in
/-- A finite native interchange family supplies the fixed-alphabet source files for
both CRT directions. Every reserve guess computes the same exact padded permutation.
For each exponent index the eventually sufficient guesses have the required clock and space. -/
def crtProcedure (F : InterchangeROMFamily.NativeFamily) (degree : ℕ) (pos : 0 < degree) (inv : Bool) :
    Procedure degree (.crt inv) := Classical.choice <| by
  let files := selectedFiles F
  let rho (p : Guess) := Generator.midExponent (exponent p)
  let h₀ (p : Guess) : 0 ≤ rho p := mid_pos _
  let h₁ (p : Guess) : rho p ≤ 1 := mid_le_one _
  let X := Sigma (Joint.Job degree inv)
  let z (x : X) := Joint.site degree pos rho h₀ h₁ inv x.1 x.2
  let native (x : X) := (z x).actual
  let u (x : X) := (z x).u
  let f (x : X) := (z x).f
  have small : Dom (fun x => (native x).k) (fun x => size (native x).seed) :=
    Joint.siteSizeDom degree pos rho h₀ h₁ inv
  obtain ⟨need,profile⟩ := CRTKernel.compiledProfile native u f small
    (fun x => by simp [u,Site.u,Site.filmWidth]) files.rectangle files.registers files.effective files.within
    Generator.midExponent mid_pos files.contract
  let pick (p : Guess) (y : Joint.Job degree inv p) : X := ⟨p,y⟩
  let width p (y : Joint.Job degree inv p) := Joint.N degree p y.1.1
  let cut := inputCut degree
  have kEq p (y : Joint.Job degree inv p) : (native (pick p y)).k = addressBits (width p y) :=
    Site.actual_k _
  have volume p (y : Joint.Job degree inv p) : CRTKernel.volume native u (pick p y) ≤ CRTBudget.volume (width p y) :=
    (Site.volume_eq (z (pick p y))).le
  have V : ∃ C : ℕ, ∀ p y, CRTBudget.volume (width p y) ≤ C*(width p y+1) :=
    ⟨9696,fun p y => (CRTBudget.volume_le_linear ((inputCut_ge_two degree p).trans y.1.1.property)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))⟩
  have low p (_ : Joint.Enough need p) (y : Joint.Job degree inv p) (_ : cut p ≤ width p y) :
      payloadBits (exterior p) (native (pick p y)).k ≤ (native (pick p y)).low := by
    rw [kEq]
    exact (Joint.eligible degree pos rho h₀ h₁ inv p y).payload
  have high p (_ : Joint.Enough need p) (y : Joint.Job degree inv p) (_ : cut p ≤ width p y) :
      SynchronizedPermutationBudget.rowFactor (native (pick p y)).k (Generator.midExponent (exponent p)) ≤
        2^(native (pick p y)).A := by
    rw [kEq]
    exact (Joint.eligible degree pos rho h₀ h₁ inv p y).rows
  obtain ⟨arena,tick,run,_,price⟩ := profile pick exponent positionLow positionHigh exterior
    exponent_pr.to_comp positionLow_pr.to_comp positionHigh_pr.to_comp width addressBits CRTBudget.volume cut
    (Joint.Enough need) kEq volume V (fun _ h => h) low high
  exact ⟨Joint.procedureOfProfile degree pos rho h₀ h₁ inv tick arena run need cut price⟩

end
end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
