import OAI.Hierarchy.DescentPhysicalResetLeft
import OAI.Hierarchy.DescentRecordedReservationRead

namespace OAI
/-! # Bounds for the retained depth and first-contact spectrum in a reset -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentPackedWalsh DescentGL ProtocolRAM
noncomputable section

/-- The measured contact totals occupy the last page of the first Walsh transform. Its
dyadically rounded bank ends before the second transform starts. -/
theorem spectrum_before_solve (E : EstimatorArena) {w : ℕ} (fit : E.Fits w) :
    E.depthRows.Fits w E.solveAt ∧ (firstContactBank E).Fits w E.solveAt := by
  let words := page E.hosts E.high
  let sq := sqOffset E.start E.hosts E.high E.low
  let bank := firstContactBank E
  have exponent : Nat.clog 2 (E.hosts*2^E.high) ≤ rowBits E.hosts E.high :=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).2 (rows_le E.hosts E.high)
  have size : bank.size ≤ words := Nat.pow_le_pow_right (by decide) exponent
  have next : bank.base+words = sq := by
    change (E.start+(E.high+E.low)*words)+words = E.start+(E.high+E.low+1)*words
    rw [Nat.succ_mul, Nat.add_assoc]
  have rest : sq ≤ E.numeratorAt := Nat.le_add_right ..
  have pageEnd : E.numeratorAt ≤ E.inputEnd := Nat.le_add_right ..
  have solve : E.inputEnd ≤ E.solveAt := Nat.le_add_right ..
  have start : E.start ≤ sq := Nat.le_add_right ..
  have after := (rest.trans pageEnd).trans solve
  have stop : bank.base+bank.size ≤ E.solveAt := ((Nat.add_le_add_left size bank.base).trans_eq next).trans after
  exact ⟨⟨fit.depth.1,fit.depth.2.1,fit.depth.2.2.trans (start.trans after)⟩,
    ⟨Nat.two_pow_pos _,lt_of_le_of_lt ((Nat.le_add_left ..).trans stop) fit.bounded,stop⟩⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentPackedWalsh DescentGL DescentGLPacked DescentPlainTerminal.Suffix DescentSixParty
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
local notation "E" => a.estimator floor
local notation "P" => a.stencilPhase sh floor count hub g Y

/-- The two original scalar arrays already fit at the start of the repacked stencil
and remain below every later root-header cutoff. -/
theorem root_spectra_before {w : ℕ} (fit : (E).Fits w) (ceiling : ℕ) (later : (P).first ≤ ceiling) :
    (E).depthRows.Fits w ceiling ∧ (ClosedReset.Recorded.firstContactBank E).Fits w ceiling := by
  have measured := ClosedReset.Recorded.spectrum_before_solve E fit
  have last : (E).solveAt ≤ (E).endAddress := by
    dsimp only [EstimatorArena.endAddress,PhysicalTrajectory.outputBase,RowStageRAM.placed]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  have prior : (E).endAddress ≤ (P).fresh := ((a.chart floor).estimator_range a.payload a.gain a.positive).2.2
  have first : (P).fresh ≤ (P).first := by unfold PackedFlow.ResetMiddle.first PackedFlow.ResetMiddle.saved; omega
  have high := ((last.trans prior).trans first).trans later
  exact ⟨⟨measured.1.1,measured.1.2.1,measured.1.2.2.trans high⟩,
    ⟨measured.2.1,measured.2.2.1,measured.2.2.2.trans high⟩⟩

theorem root_spectra_fit {w : ℕ} (fit : (E).Fits w) (ceiling : ℕ) (later : (P).endAddress ≤ ceiling) :
    (E).depthRows.Fits w ceiling ∧ (ClosedReset.Recorded.firstContactBank E).Fits w ceiling := by
  have lower : (P).first ≤ (P).base := by unfold PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination; omega
  have endBound : (P).base ≤ (P).endAddress := by
    rw [PackedFlow.ResetMiddle.endAddress, (P).S.extent]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  exact a.root_spectra_before sh floor count hub g Y fit ceiling ((lower.trans endBound).trans later)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
