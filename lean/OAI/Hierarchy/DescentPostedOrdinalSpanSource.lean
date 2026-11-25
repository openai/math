import OAI.Hierarchy.DescentResetArchiveValues
import OAI.Hierarchy.DescentResetVenueScalarSpan
import OAI.Hierarchy.DescentPackedSourceUnique
import OAI.Hierarchy.DescentPrimitiveBirthDigits

namespace OAI
/-! # The scalar count read by metadata is the same seventh digit written to the dated archive -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation:max "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)
variable (ok : u.Ready) (small : 2*a.successor.receiver.candidates<2^a.successor.receiver.queryBits) (actorMem : Memory w)

theorem OrdinalRead.range_value (f : Fin 3) (j : Fin (s).slots) (x : Fin (A).blocks) (n : Fin (s).nodes)
    (issued : OrdinalRead u ok small actorMem ((v).operandOrdinal (s) (DescentRetainedRangeDigits.page f) j x n))
    (live : 0<(A).lanes) (signed : (A).signedBits*(A).lanes≤w) :
    issued.amount=issued.kept:=by
  have blank (c : Fin (2*(A).candidates)) : issued.raw c=(fun _ _=>0):=by
    have read:=issued.source_read c
    rw [(v).previous_range (s) b rendered f j x n c] at read
    exact read.determined (DescentPrimitiveBirth.zero _) live signed
  funext h g
  apply Fin.ext
  change (issued.kept h g).val+(selected issued.query
    (fun c h g=>((issued.raw c h g).val:Cell (s).coeff)) h g).val=_
  cases q : issued.query h g with
  | none=>simp [selected,q]
  | some c=>simp [selected,q,blank c]

theorem venue_ordinal_spans (z : u.FinalInputs) (room : z.Room) {m mid : Memory w}
    (before : u.throughOperandDate.Runs m mid) (issued : acted m actorMem)
    (choice : ∀i,OrdinalRead u ok small actorMem i) (live : 0<(A).lanes) (signed : (A).signedBits*(A).lanes≤w) :
    ∀x n j,Source (z.spans x n j)
      (choice ((v).operandOrdinal (s) 6 j (x.cast z.metaBlocks) (n.cast z.metaNodes))).amount
      (A).lanes (z.venueImage mid):=by
  obtain ⟨other,done_,rows⟩:=z.venue_span ok room before
  have eqn : other=actorMem:=ProtocolRAM.exec_unique _ m other actorMem done_ issued
  subst other
  intro x n j
  let i:=(v).operandOrdinal (s) 6 j (x.cast z.metaBlocks) (n.cast z.metaNodes)
  have eqn : (choice i).amount = (choice i).kept := OrdinalRead.range_value u ok small actorMem (2:Fin 3) j
    (x.cast z.metaBlocks) (n.cast z.metaNodes) (choice i) live signed
  exact rows x n j (choice i).amount (eqn.symm ▸ (choice i).kept_read)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
