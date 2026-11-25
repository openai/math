import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentOriginalPaddedNodes
import OAI.Hierarchy.DescentResetSignedAll
import OAI.Hierarchy.DescentResetCandidateMeta

namespace OAI
/-! # The signed candidate lookup for an occupied original argument slot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentLocalArchiveOrder DescentCompiler DescentSharedCableNames
open DescentDatedAddressBook Chronology
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
    {q ε:ℝ} {S:AtomSchedule} {k age z D wire hist n h C f g cut tail:ℕ}
    {base:Reached W G q ε S k age z D wire hist} {ctl:ResetRates G S k D n h C f g cut tail}
    (B:ClosedReset base ctl)
local notation "entry" => (B.reset.denseHostRank B.terminals
  (B.frame.host.symm.toEmbedding.trans (base.vertex.trans (Fin.castLEEmb base.valid.host)))).trans
  (Fin.castLEEmb B.next.valid.host)
local notation "Host" => Stage.Host (Fin (S.groupCount (age+1))) B.next.V k

def operandLocation (block : Fin (2^k)) (host : Fin (S.hostSize (age+1))) (group : Fin (S.groupCount (age+1))) :
    Option Host := (rackOf B entry host).map (fun z=>((group,z),block))

theorem location_at_archive (ports : DatePorts) (next : BitDescription _) (number : Local next)
    (room : DatePorts.RangeRoom ports B.next next)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (h : Fin ports.operandHosts) (g : Fin ports.venue.groups)
    (y : NodeOrder.All next) (seen : DatePorts.slotAt ports B.next next number room block node h g=some y)
    (h₀ : Fin (S.hostSize (age+1))) (hostAt : h₀.val=h.val) :
    operandLocation B (block.cast (congrArg (2^·) room.radix.symm)) h₀ (g.cast room.groups.symm) =
      some (Stage.home B.next.placement y.1) ∧ node.val=(number y.1 y.2).val:=by
  obtain ⟨host,groupId,blockId,ordinal⟩:=(Reached.NodeCells.atPhysical_some B.next next number
    (block.cast (congrArg (2^·) room.radix.symm)) node h (g.cast room.groups.symm) y.1 y.2).mp seen
  have whereHost : entry (B.next.placement.pos y.1).2=h₀:=Fin.ext ((dense_physical B base.valid.host _).trans
    (host.trans hostAt.symm))
  refine ⟨?_,ordinal⟩
  have rack : rackOf B entry h₀ = some (B.next.placement.pos y.1).2 :=
    (congrArg (rackOf B entry) whereHost.symm).trans (rack_present B entry _)
  apply (congrArg (Option.map (fun v : B.next.V =>
    ((g.cast room.groups.symm, v), block.cast (congrArg (2^·) room.radix.symm)))) rack).trans
  exact congrArg some (Prod.ext (Prod.ext groupId.symm rfl) blockId.symm)

/-- Recover the exact native public row and both product coordinates from an occupied lookup. -/
theorem location_coordinates (x : Fin (2^k)) (h : Fin (S.hostSize (age+1))) (g : Fin (S.groupCount (age+1)))
    (u : Host) (located : operandLocation B x h g=some u) :
    x=u.2 ∧ h=((denseOrder B) u.1.2).castLE B.next.valid.host ∧ g=u.1.1:=by
  unfold operandLocation at located
  cases actual : rackOf B entry h with
  | none => simp [actual] at located
  | some z =>
    simp only [actual,Option.map_some,Option.some.injEq] at located
    subst u
    refine ⟨rfl,Fin.ext ?_,rfl⟩
    have addr:=congrArg Fin.val (rack_named B entry h z actual)
    exact addr.symm.trans (dense_physical B base.valid.host z)

theorem candidate_at_location (x : Fin (2^k)) (h : Fin (S.hostSize (age+1))) (g : Fin (S.groupCount (age+1)))
    (j : Fin (2*totalLocal B)) :
    (rackOf B entry h).bind (fun z=>candidateRows B (fieldNames B) ((g,z),x) j)=
      (operandLocation B x h g).bind (fun site=>candidateRows B (fieldNames B) site j):=by
  cases whereAt:rackOf B entry h <;>simp [operandLocation,whereAt]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
