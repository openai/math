import OAI.Hierarchy.DescentDatedTypedPageReads
import OAI.Hierarchy.DescentDatedRegisteredHeaders

namespace OAI
/-! # Pointer types in the preceding seven-page register of the ordinary scalar resolver -/
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
variable {nb mb : ℕ} (V : References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity (v.resolver.size+2) nb mb)

def registeredOperandBooks : Books (l₀) :=fun x p=>
  previousValues (l₀) (a₀) shape.operands shape.blocks shape.hosts shape.groups
    (References.returnedValue (a₀) V (l₀).nodes) p x

def registeredPointerPages (arg : Fin (l₀).operands) (f : Fin 4) : Fin (a₀).pageCount :=
  (pageOf arg f).cast (congrArg (7*·) shape.operands)

variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor)
local notation "dir₀" => A.directory v floor mat
local notation "pg" => v.registeredPointerPages shape

theorem registered_typed_rows {w : ℕ} (m : Memory w) (pitch : 0<(a₀).lanes*(a₀).radix)
    (pages : ∀p q,ScalarOperand.Measured ((dir₀).refs p q) (V p q) (l₀).nodes ((a₀).lanes*(a₀).radix) (v.vectorStart floor) m)
    (actual : ∀arg q h g (u : Fin n₀) site,
      (encode 1 n₀).symm (marked (V (pg arg 0) q) h g) u≠0 →
      DescentSortedRoster.indexed (V (pg arg 0) q).walks h (bookRoot (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u)=some site →
      TypedHeader (fun f=>ScalarOperand.item (V (pg arg f) q).old (V (pg arg f) q).born
        (bookBlock (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u)
        (bookItem (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u) site g)) :
    BookPointers (v.registeredOperandBooks shape V) :=by
  apply (books_typed_iff _).2
  intro x node arg h g
  let atHost:=finProdFinEquiv.symm (h.cast shape.hosts)
  let atGroup:=finProdFinEquiv (g.cast shape.groups,x.cast shape.blocks)
  exact (dir₀).typed_book_at (pg arg) atHost.2 V (fun f=>pages (pg arg f) atHost.2)
    pitch atHost.1 atGroup node (actual arg atHost.2 atHost.1 atGroup)

theorem registered_input_pointers {w : ℕ} (m : Memory w) (pitch : 0<(a₀).lanes*(a₀).radix)
    (pages : ∀p q,ScalarOperand.Measured ((dir₀).refs p q) (V p q) (l₀).nodes ((a₀).lanes*(a₀).radix) (v.vectorStart floor) m)
    (past : ∀arg q block h g node,TypedHeader (fun f=>ScalarOperand.take node ((V (pg arg f) q).old block h g)))
    (fresh : ∀arg q block seat arm h g,TypedHeader (fun f=>(V (pg arg f) q).born block seat arm h g)) :
    BookPointers (v.registeredOperandBooks shape V) :=by
  apply v.registered_typed_rows shape V floor A mat m pitch pages
  intro arg q h g u site _ _
  let x:=bookBlock (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u
  unfold ScalarOperand.item
  cases eqn : finSumFinEquiv.symm (bookItem (r₀).degree (r₀).k (r₀).oldNodes (r₀).capacity u) with
  | inl j=>exact past arg q x site g j
  | inr s=>exact fresh arg q x (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2 site g

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
