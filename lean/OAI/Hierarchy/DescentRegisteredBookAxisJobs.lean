import OAI.Hierarchy.DescentRegisteredAcquiredNumerals
import OAI.Hierarchy.DescentDatedOriginalTaggedHeads
import OAI.Hierarchy.DescentReachedPhysicalPinJob

namespace OAI
/-! Both chart presentations of the same registered operand book give identical
complete decoded jobs, including the origin, newborn, and signed ticket reads. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedPriorOperand DescentDatedOperandReadPipeline DescentSIMDLookup
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedOperand DescentOperandVectorArena DescentHaloWalkRAM
open DescentSixParty.SeedNamed.Branch DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) (shape:v.VectorShape)
set_option hygiene false in
local notation "L" => v.resolver
set_option hygiene false in
local notation "A" => v.vector
set_option hygiene false in
local notation "ref" => v.reference
set_option hygiene false in
local notation "fmt" => v.ticket.depotShape v.short
set_option hygiene false in
local notation "E" => v.material
set_option hygiene false in
local notation "B" => v.bornBook
variable (floor:ℕ) (entry:v.ArgumentEntry) (mat:entry.Match v floor)
    (homes:(B).hosts=(A).hosts) (gs:(B).groups=(A).groups*(A).radix) (bits:(B).bits=(L).size+2)
    (pg:Fin (A).pageCount) (chip:Fin (B).hosts→Fin (B).groups→Cell (B).chipBits)
    (blocks:(L).blocks=(E).blocks) (bound:(L).hosts≤(E).hosts) (groups:(L).groups=(E).groups)
    (wide:v.WideHead→Fin (E).hosts→Fin (E).groups→Cell (E).fieldBits)
    (roster:Fin (E).oldHosts→Fin (fmt).degree→Option (Fin (E).oldHosts))
    {nb mb c:ℕ}
set_option hygiene false in
local notation "Rows" cap:arg bits_:arg => References.Rows A (ref).degree (ref).k (ref).oldNodes cap ((L).size+2) bits_ mb
variable (old:Rows c nb) (raw:Rows (ref).capacity nb)
set_option hygiene false in
local notation "previous" rows:arg => v.returnedBook shape rows
set_option hygiene false in
local notation "priorWords" rows:arg => fun j f h k=>booksHeader (previous rows) j h k f
set_option hygiene false in
local notation "mouths" rows:arg => fun j f h k=>take (((L).index.symm j).2.1)
  (v.mouthHeaderValue floor entry mat shape (v.headerMouthRows floor entry mat rows homes gs bits) chip homes gs j f h k)
set_option hygiene false in
local notation "heads" prev:arg rod:arg => v.originalValues (v.sampleHeads blocks bound groups
  (v.originHeaderValue shape ((rod) pg)) (priorWords prev) (mouths rod) wide (v.narrowValue roster))
set_option hygiene false in
local notation "words" prev:arg rod:arg => ticketAt v.ticketReadGeometry (SortedInput.values v.ticketReadGeometry
  (heads prev rod) (v.walkValues (Gather.reaching roster)))
set_option hygiene false in
local notation "route" prev:arg rod:arg => v.ticketRoles (words prev rod)
set_option hygiene false in
local notation "room" prev:arg rod:arg => ∀j h y,11*((route prev rod) j 1 h y).val+((route prev rod) j 2 h y).val<2^((L).size+2)
set_option hygiene false in
local notation "jobs" prev:arg rod:arg fits:arg => decodedBooks (previous prev)
  (fun j h k=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides (words prev rod) j h k))
  (route prev rod) fits

/-- The true-capacity chart is used by the old-operand reader. The mouth and origin
keep the original job's capacity and use the same public name-width conversion. -/
theorem registered_axis_jobs {cap n:ℕ} (capEq:(ref).capacity=cap) (names:nb=n)
    (fits:room raw raw)
    (projected:let donor:=fun x l=>onSourceAxes capEq names id (raw x l)
               let mouth:=fun x l=>onSourceAxes rfl names id (raw x l)
               room donor mouth):
    let donor:=fun x l=>onSourceAxes capEq names id (raw x l)
    let mouth:=fun x l=>onSourceAxes rfl names id (raw x l)
    jobs donor mouth projected=jobs raw raw fits:=by
  subst cap
  subst n
  rfl

/-- The original bound also applies to the projected register, on every row, not
only on a semantic operand. -/
theorem registered_axis_fit {cap n:ℕ} (capEq:(ref).capacity=cap) (names:nb=n)
    (fits:room raw raw) :
    let donor:=fun x l=>onSourceAxes capEq names id (raw x l)
    let mouth:=fun x l=>onSourceAxes rfl names id (raw x l)
    room donor mouth:=by
  subst cap
  subst n
  exact fits

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
