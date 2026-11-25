import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic
import OAI.Hierarchy.DescentTerminalIntegralFrontier
import OAI.Hierarchy.DescentTerminalMaskInvoice
import OAI.Hierarchy.DescentPrivateGateScale

namespace OAI
/-! # The local row quantum and the single partial terminal bin -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty DescentTerminalGraphVolume DescentTerminalBinPack
noncomputable section

/-- The initial exterior has q₀ slots of width U*p; the terminal row has
q₀*U slots of width p. Choosing p as W ordinary slices makes the transpose
an integral wiring on every one of the paid rows. -/
theorem split_quantum (h q₀ U W : ℕ) (hq : 0<q₀) (hU : 0<U) (hW : 0<W)
    (room : 32*(q₀*U*W)≤h) :
    let piece:=h/(16*(q₀*U*W)); let p:=W*piece; let q:=q₀*U
    0<piece ∧ 16*(q*p)≤h ∧ h≤32*(q*p) ∧ q₀*(p*U)=q*p := by
  let a:=q₀*U
  obtain ⟨positive,_,lower,upper⟩:=packing_width (show 0<W from hW) (Nat.mul_pos hq hU) room
  dsimp only
  exact ⟨positive,by simpa only [Nat.mul_comm W] using lower,by simpa only [Nat.mul_comm W] using upper,by ring⟩

end
end Hierarchy.DescentCompiler.TerminalScale

end OAI
