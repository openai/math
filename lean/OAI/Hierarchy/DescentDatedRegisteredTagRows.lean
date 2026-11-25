import OAI.Hierarchy.DescentPackedTagCompaction
import OAI.Hierarchy.DescentDatedRegisteredPointerRows
import OAI.Hierarchy.DescentDatedBooksTagPages

namespace OAI
/-! The first physical operand page alone determines whether a packed W input has a legal tag. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPackedZip DescentSIMDLookup DescentPackedColony DescentOrdinaryOriginMask
open DescentHaloWalkRAM DescentOperandVectorArena DescentOrdinaryAtomFieldRAM
open DescentDatedPriorOperand DescentOperandStateBanks DescentPriorOperandColumns
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (shape : v.VectorShape)
local notation "l₀" => v.resolver
local notation "r₀" => v.reference
local notation "a₀" => v.vector
local notation "n₀" => DescentPackedActorMask.nodes (breadth (r₀).degree*2^(r₀).k) (r₀).oldNodes (r₀).capacity
local notation "Val₀" => References.Rows (a₀) (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity ((l₀).size+2)
variable {nb mb : ℕ} (V : References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity (v.resolver.size+2) nb mb)

local notation "pg" => v.registeredPointerPages shape

theorem registered_input_tags
    (old : ∀arg q block h g node,(ScalarOperand.take node ((V (pg arg 0) q).old block h g)).val≤2)
    (born : ∀arg q block seat arm h g,((V (pg arg 0) q).born block seat arm h g).val≤2) :
    BookTags (v.registeredOperandBooks shape V) :=by
  apply (books_tags_iff _).2
  intro x j arg host group
  let here:=finProdFinEquiv.symm (host.cast shape.hosts)
  let lane:=finProdFinEquiv (group.cast shape.groups,x.cast shape.blocks)
  let value:=V (pg arg 0) here.2
  let bits:=marked value here.1 lane
  let record (u : Fin n₀) : Cell ((l₀).size+2):=
    (DescentSortedRoster.indexed value.walks here.1
      (bookRoot (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u)).elim 0 (fun s=>
        ScalarOperand.item value.old value.born (bookBlock (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u)
          (bookItem (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u) s lane)
  change (ScalarOperand.take j (DescentPackedLocalAtoms.pack ((l₀).size+2) n₀ (l₀).nodes bits
    (encode ((l₀).size+2) n₀ record))).val≤2
  apply DescentPackedLocalAtoms.packed_field_bound bits record
  intro u
  unfold record
  cases route : DescentSortedRoster.indexed value.walks here.1
    (bookRoot (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u) with
  | none=>simp
  | some s=>
    simp only [Option.elim_some]
    let block:=bookBlock (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u
    unfold ScalarOperand.item
    cases side : finSumFinEquiv.symm (bookItem (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u) with
    | inl node=>exact old arg here.2 block s lane node
    | inr t=>exact born arg here.2 block (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 s lane

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
