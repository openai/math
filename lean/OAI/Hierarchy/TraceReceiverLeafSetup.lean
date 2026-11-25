import OAI.Hierarchy.TraceReceiverLeafOperands
import OAI.Hierarchy.GridReceiverDirectory
import OAI.ThreeFlat.RAM.HistoryPhysicalFamilies

namespace OAI
/-! # Stage archive of the selected receiver family -/

namespace Hierarchy.TraceReceiverLeafSetup
open ThreeFlat Diagonal Diagonal.PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open GridRegisteredSetting TraceBitHeader
noncomputable section
variable {F : Type} [Fintype F] [Field F] {w pc regs slots S base fuel axes : ℕ}
variable (D : GridRegisteredSetting.RunData F (64*w) pc regs slots S base fuel axes (w/2))

/-- The stage lookup tables use the exact finite block catalog at S38, the
physical word width as its height and the actual second directory's histogram stride. -/
def bank (l : GridNativeImage.Layout) : HistoryStageBody.Physical.Archive :=
  HistoryStageBody.Physical.archive D.block (start w) (pages w) (GridReceiverDirectory.archive (F:=F) (w:=w) D l).K

/-- The receiver replays the selected compressor in its independent low
archive. Its whole journal lies before the installed S38 block. -/
theorem archive_bounds (l : GridNativeImage.Layout) (large : 1≤w) {heap : ℕ}
    (held : heap≤(GridReceiverDirectory.archive (F:=F) (w:=w) D l).control+64) :
    TickWorkspace.base (TraceAdmission.receiverAge w) 20≤(GridReceiverDirectory.archive (F:=F) (w:=w) D l).cursor.header ∧
    heap ≤ start w ∧ heap≤TickWorkspace.base (TraceAdmission.receiverAge w) 40 := by
  let u:=TraceAdmission.receiverAge w
  let step:=TickWorkspace.stride u
  have age : 4*w≤u^10 := TraceAdmission.receiverAge_lower w
  have huge : (2^w)^4 ≤ step := by
    dsimp [step,TickWorkspace.stride]
    exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega)) 4
  have floor : 64 ≤ step := by
    change 64≤(2^(u^10))^4
    have h : 2^2≤2^(u^10) := Nat.pow_le_pow_right (by decide) (by omega)
    have := Nat.pow_le_pow_left h 4
    omega
  change heap≤21*step+6*(2^w)^4+64 at held
  change 21*step≤21*step+64 ∧ heap≤39*step ∧ heap≤41*step
  omega

/-- The scheduled scan uses the true number of directory records. -/
theorem librarySrc_eq (l : GridNativeImage.Layout) :
    librarySrc (F:=F) (w:=w) D l=templateSrc (F:=F) (w:=w) D l+(64*w)*(templateSize (F:=F) (w:=w) D+64*((GridReceiverDirectory.native (F:=F) (w:=w) D l).stages.length+2)) := by
  unfold librarySrc GridStructuralHeader.directory
  rw [NavigationPass.Archive.directory_length]; rfl


end
end Hierarchy.TraceReceiverLeafSetup

end OAI
