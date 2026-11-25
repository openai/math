import OAI.Computability.BorderVNP.DiagonalSignedReportRoom
import OAI.Computability.BorderVNP.PackedFrozenSeedExecute
import OAI.Computability.BorderVNP.PackedBankCompiledScalars

/-! # Joint size of signed reports, compact compiler operands and actual sewn rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs TeamScales Filter
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The scalar cap for the full signed directory, after adding its actual
zero and equality intervals to the complete named history. -/
def signedMarkedLimit (copies initialCap coefficient mass : ℕ) :=
  max (max 2 (max copies initialCap)) (max (coefficient*(mass+1)) (max 1 (15*mass)))

/-- The joint source range used by the physically prepared report array. -/
structure SignedReceivedScale (M ext w gadgets mass low Z digitBound : ℕ) : Prop where
  program : 1042*mass ≤ M
  publicWord : 0 < w
  wordFit : w ≤ M
  digitFit : M < 2^w
  gadgetsFit : gadgets ≤ M+1
  space : 3*M+gadgets*w ≤ ext
  digits : w ≤ digitBound
  marked : 3*M+Z ≤ 4*(M+ext+1)^3
  relative : low ≤ 4*(M+ext+1)^3

set_option maxHeartbeats 1000000 in
/-- The physical word width, private checker, actual tilted grid and shared
subtotal layout work at one length threshold before any chart or wire assignment. -/
theorem JointSchedule.eventually_signed_received_scale (b : JointSchedule s (E+1) deg Q A B j)
    (header gadgets : ℕ) (large : E+2 ≤ deg) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let axes := Fintype.card (Cube D)
      let K₀ := seedBoxCapacity n r axes d (Fintype.card (Direction axes))
      let copies := TeamScales.width n s.α
      let mass := S.publicProgramFactor^epochs s.τ n*initialMass (D:=D) n r d copies header
      let C₀ := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
      SignedReceivedScale (TeamScales.width n (1/5)) (TeamScales.width n (1/4)) (b.physical.word n) gadgets
        mass (max (tableLimit e) (max 8 K₀)) (signedMarkedLimit copies K₀ C₀ mass) ((logWidth r n+1)^(E+2)) := by
  let C₀ := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
  let g := max gadgets (max 8 (tableLimit e))
  filter_upwards [b.eventually_signed_program_mass header 1042,b.eventually_signed_report_room g C₀ large] with n charge room
  intro r d axes K₀ copies mass C
  let M := TeamScales.width n (1/5)
  let ext := TeamScales.width n (1/4)
  let w := b.physical.word n
  have hm : mass≤M := (Nat.le_mul_of_pos_left _ (by decide : 0<1042)).trans charge
  have positive : 0 < S.publicProgramFactor := by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor
    positivity
  have init : initialMass (D:=D) n r d copies header ≤ mass := Nat.le_mul_of_pos_left _ (Nat.pow_pos positive)
  have seed := SeedPlan.seedScalar_le_mass (D:=D) (n:=n) (r:=r) (d:=d) (copies:=copies) (headerFactor:=header)
  change max 2 (max copies (max K₀ (2*copies*K₀))) ≤ _ at seed
  have src : max 2 (max copies K₀) ≤ M :=
    (max_le_max_left _ (max_le_max_left _ (le_max_left ..))).trans (seed.trans (init.trans hm))
  obtain ⟨hw,word,digit,fit,space,digits,marked⟩ := room
  have gadgetsFit : gadgets≤g := le_max_left ..
  have columns : max 8 (tableLimit e) ≤ g := le_max_right ..
  refine ⟨charge,hw,word,digit,gadgetsFit.trans fit,?_,digits,?_,?_⟩
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_right w gadgetsFit) _).trans space
  · exact marked mass (max 2 (max copies K₀)) (signedMarkedLimit copies K₀ C mass) hm src le_rfl
  · change max (tableLimit e) (max 8 K₀) ≤ 4*(M+ext+1)^3
    have basis : M+1 ≤ 4*(M+ext+1)^3 := by nlinarith [Nat.zero_le (M^2*ext),Nat.zero_le (M*ext^2)]
    omega

end Diagonal

end BorderVNP
end Computability
end OAI
