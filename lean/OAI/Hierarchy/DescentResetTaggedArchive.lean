import OAI.Hierarchy.DescentResetAllTaggedBooks

namespace OAI
/-! # Tagged physical reset books in the next calendar register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "ports" => reset a floor u
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)


open DescentOrdinaryAtomFieldRAM DescentPriorOperandColumns
local notation "L" => (v).rangeLayout

theorem reset_archive_tags (shape : (ports).rangeLayout=L) (z : u.FinalInputs) (ok : u.Ready) (space : z.Room) {m mid dst : Memory w}
    (first : u.throughOperandDate.Runs m mid) (run : (PhysicalReset.date z).Runs m dst)
    (bits : (s).coeff=(v).nodeBits) (two : 2 ≤ (v).nodeBits)
    (small : 2*(A).candidates<2^(A).queryBits)
    (reads : ∀actorMem,acted m actorMem → ∀ f j x n,
      Nonempty (OrdinalRead u ok small actorMem ((v).operandOrdinal (s) f j x n)))
    (tag : ∀actorMem,acted m actorMem → ∀ j x n,
      ∃r : OrdinalRead u ok small actorMem ((v).operandOrdinal (s) 0 j x n),∀h g,
      (r.kept h g).val+(selected r.query (fun i h g=>((r.raw i h g).val:Cell (s).coeff)) h g).val ≤ 2) :
    ∃bks : Books (ports).rangeLayout, BookTags bks ∧ ∀x pg,
      Reads (previousBank (ports).rangeLayout (ports).archive.arguments x pg)
        (bks x pg) (ports).rangeLayout.lanes dst :=by
  have source : (ports).archive=PriorResetArchive.reset (v) b :=rfl
  rw [source,shape]
  exact reset_tagged_books u z ok space first run bits two small reads tag

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
