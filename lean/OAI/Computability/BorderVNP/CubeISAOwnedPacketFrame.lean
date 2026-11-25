import OAI.Computability.BorderVNP.CubeISAOwnedPrepare
import OAI.Computability.BorderVNP.CubeISAOwnedTraceScan
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Routed cursors survive local packet address preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM DiagonalResidueRAM

/-- The native filter is unsigned and never assigns either routed source cursor. -/
theorem packetFilter_frame (n : ℕ) :
    (packetFilter n).unsigned = true ∧ (packetFilter n).keeps 36 = true ∧ (packetFilter n).keeps 37 = true := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (true && ((packetFilter n).unsigned && true)) = true ∧
      (true && ((packetFilter n).keeps 36 && true)) = true ∧ (true && ((packetFilter n).keeps 37 && true)) = true
    simpa only [Bool.true_and,Bool.and_true] using ih

/-- A complete packet candidate contributes no private bits or signs and
retains the two shared stream cursors. -/
theorem packetCandidate_frame (n : ℕ) :
    (packetCandidate n).unsigned = true ∧ (packetCandidate n).keeps 36 = true ∧
      (packetCandidate n).keeps 37 = true := by
  change (true && (packetFilter n).unsigned) = true ∧
    (true && (packetFilter n).keeps 36) = true ∧ (true && (packetFilter n).keeps 37) = true
  simpa only [Bool.true_and] using packetFilter_frame n

/-- Refine the bounded physical candidate with its exact trace bits and the
two routed cursors, including on invalid digit trials. -/
theorem packetCandidate_traced {w n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r : Bank w} {m : Memory w} {cost : ℕ} {post : NatState → Prop}
    (run : BoundedRun pub mac (packetCandidate n) r m cost post) :
    TraceRun pub mac (packetCandidate n) r m [] cost
      (fun t mt => post (.ofWords t mt) ∧ t 36 = r 36 ∧ t 37 = r 37) := by
  obtain ⟨unsigned,k36,k37⟩ := packetCandidate_frame n
  obtain ⟨es,t,mt,path,tr,cap,hp⟩ := traceRun_unsigned run unsigned
  exact ⟨es,t,mt,path,tr,cap,hp,path.keepsReg k36,path.keepsReg k37⟩

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
