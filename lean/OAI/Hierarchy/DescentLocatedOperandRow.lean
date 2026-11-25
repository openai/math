import OAI.Hierarchy.DescentOriginalOperandLocation

namespace OAI
/-! # Returning a native row observation at its original operand location -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentLocalArchiveOrder DescentCompiler DescentSharedCableNames
open DescentDatedAddressBook Chronology
open scoped Classical
noncomputable section
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
    {q ε:ℝ} {S:AtomSchedule} {k age z D wire hist n h C f g cut tail:ℕ}
    {base:Reached W G q ε S k age z D wire hist} {ctl:ResetRates G S k D n h C f g cut tail}
    (B:ClosedReset base ctl)
local notation "Host" => Stage.Host (Fin (S.groupCount (age+1))) B.next.V k

/-- A lookup made at a concrete hardware slot and a lookup made at the receiver's
compact coordinates give the same dependent row, including its physical block. -/
theorem location_pullback {blocks hosts groups : ℕ}
    (hx : blocks=2^k) (hh : hosts=S.hostSize (age+1)) (hg : groups=S.groupCount (age+1))
    (property : Fin blocks→Fin hosts→Fin groups→Prop)
    (x : Fin blocks) (rh : Fin hosts) (rg : Fin groups) (u : Host)
    (located : operandLocation B (x.cast hx) (rh.cast hh) (rg.cast hg)=some u)
    (original : property (u.2.cast hx.symm) (((denseOrder B u.1.2).castLE B.next.valid.host).cast hh.symm)
      (u.1.1.cast hg.symm)) : property x rh rg :=by
  obtain ⟨blockAt,hostAt,groupAt⟩:=location_coordinates B (x.cast hx) (rh.cast hh) (rg.cast hg) u located
  have sameBlock : x=u.2.cast hx.symm:=Fin.ext (congrArg (Fin.val (n := 2^k)) blockAt)
  have sameHost : rh=((denseOrder B u.1.2).castLE B.next.valid.host).cast hh.symm:=
    Fin.ext (congrArg (Fin.val (n := S.hostSize (age+1))) hostAt)
  have sameGroup : rg=u.1.1.cast hg.symm:=Fin.ext (congrArg (Fin.val (n := S.groupCount (age+1))) groupAt)
  rwa [sameBlock,sameHost,sameGroup]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
