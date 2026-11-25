import OAI.Hierarchy.DescentResetStemIssuedGroups

namespace OAI
/-! # The recorded group and fine cells of an actual old stem -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentResetStemCompactOrder
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "groups" => S.groupCount (i+1)
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "m" => S.groupWidth k tail i+k
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)
local notation "Slot" => Fin (2^(m-(T).commonDepth))×Fin (2*(A).cap)

/-- The two scalar lane reads supply exactly the source digits of the grain
returned by the old-stem roster, on either side of its cable. -/
theorem group_fine_key (u : Host) (side : Bool) (slot : Slot) (j : (old).graph.Edge)
    (found : oldStemAt B u side slot=some j) {field : ℕ} (group fine : Cell field)
    (groupRead : group.val=compress (groupDomain digitsIn B.frame.basis fits () ((digits).symm (u.1.1,u.2)))
      (digitsIn ((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1))).1.val)
    (fineRead : fine.val=((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1)).val%2^k) :
    group.val=compress (groupDomain digitsIn B.frame.basis fits
        (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2)
      (((A).pos (W.graph.src (beforeStem B j).1)).1.val) ∧
    fine.val=((A).block (W.graph.src (beforeStem B j).1)).val :=
  ⟨groupRead.trans (cell_group B u side slot j found), fineRead.trans (cell_fine B u side slot j found)⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
