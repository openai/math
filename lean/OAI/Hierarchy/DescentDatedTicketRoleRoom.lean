import OAI.Hierarchy.DescentDatedMatchedTicketFlags
import OAI.Hierarchy.DescentDatedAnchorFieldRoom
import OAI.Hierarchy.DescentDatedTicketKeyRoom

namespace OAI
/-! # The combined role identifier fits on every routed lane, including padding -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry) (v : Data g)

theorem selected_anchor_le (j : Fin g.jobs) (f : Fin 5) (h : Fin g.hosts) (y : Fin g.groups)
    (limit : ℕ) (bound : ∀i,(v.anchor j f i h y).val ≤ limit) : (anchorV g v j f h y).val ≤ limit :=by
  unfold anchorV picked DescentResetStemMux.pick
  split
  · apply bound
  · exact Nat.zero_le _

theorem global_role_fields (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups)
    (old : ∀i,(v.anchor j 1 i h y).val ≤ 2*g.cap) (role : ∀i,(v.anchor j 2 i h y).val ≤ 10)
    (mouth : (v.origin j 0 h y).val=2 → (v.mouth j 1 h y).val ≤ 10) :
    ticketAt g v j h y 6 ≤ 2*g.cap ∧ ticketAt g v j h y 7 ≤ 10 :=by
  let rawKey := rawLaw g.paths (g.blocks*(g.cap*11)) g.digitBits 0 (fun i=>rawInputs g v j i h y)
  exact Ticket.role_fields g.cap g.blocks (v.origin j 0 h y).val (v.prior j 0 h y).val
    (rankV g v j 0 h y).val (v.origin j 2 h y).val rawKey.val (rawV g v j 6 h y).val
    (rawV g v j 7 h y).val (v.mouth j 1 h y).val
    (fun f => (anchorV g v j f h y).val)
    (fun f => (rawV g v j (f.castLE (by decide : 6 ≤ 8)) h y).val)
    (selected_anchor_le g v j 1 h y _ old) (selected_anchor_le g v j 2 h y _ role) mouth

end
end Hierarchy.DescentDatedOperandReadPipeline

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentSharedCableNames DescentPackedColony DescentDatedOperandReadPipeline DescentHaloPackedRebase
open DescentDatedOperandCoordinates ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "l₀" => v.resolver
local notation "g₀" => v.ticketReadGeometry
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "O" => DepotRAM.Material.roles fmt₀
local notation "G" => (e₀).groups
local notation "B" => (e₀).blocks
local notation "b" => (e₀).fieldBits
local notation "J" => (l₀).jobs
local notation "d" => v.operandShortBits
local notation "val₀" => Fin K → Fin G → Cell b
variable (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
  (state : Fin v.material.oldHosts → Fin v.material.oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short))
variable (bands : v.material.oldGroups = v.material.groups * v.material.blocks)
  (serial peer : Fin v.material.blocks →
    Fin (breadth (v.ticket.depotShape v.short).degree * DepotRAM.Material.roles (v.ticket.depotShape v.short)) →
    Fin v.material.hosts → Fin v.material.groups → Cell v.material.fieldBits)
variable (blocks : v.resolver.blocks=v.material.blocks) (bound : v.resolver.hosts≤v.material.hosts)
    (groups : v.resolver.groups=v.material.groups)
variable (orig : Fin v.resolver.jobs → Fin 6 → Values v.ticketReadGeometry v.operandShortBits) (prior : Fin v.resolver.jobs → Fin 4 → Values v.ticketReadGeometry (v.resolver.size+2))
    (born : Fin v.resolver.jobs → Fin 3 → Values v.ticketReadGeometry v.bornBook.bits)
local notation "wide₀" => v.wideMaterialValues R state bands serial peer
local notation "data₀" => v.sampleHeads blocks bound groups orig prior born wide₀ (v.narrowValue R)

private theorem catalog_digit_le (n : Fin (DescentDatedOperandPages.count fmt₀)) (p₀ : Fin P₀)
    (x : Fin B) (h : Fin K) (y : Fin G) (limit : ℕ)
    (before : ∀source,(DescentDatedOperandPages.law fmt₀ v.profile b n.val source).val ≤ limit) :
    (v.matchedFieldValue R state bands n p₀ x h y).val ≤ limit :=by
  cases hit : DepotRAM.Material.Route.selected R v.materialPitch p₀ h with
  | none=>simp [matchedFieldValue,DepotRAM.Material.Route.value,hit]
  | some donor=>
    simpa only [matchedFieldValue,DepotRAM.Material.Route.value,hit,Option.elim_some,
      show DepotRAM.Material.Route.gated (0:DepotRAM.Material.Route.Port)=false by decide,Bool.false_eq_true,ite_false] using
      before (DepotRAM.combine fmt₀ (state donor ((finProdFinEquiv (y,x)).cast bands.symm)))

theorem matched_role_fields (j : Fin J) (h : Fin (l₀).hosts) (y : Fin (l₀).groups)
    (mouth : (orig j 0 h y).val=2 → (born j 1 h y).val ≤ 10) :
    let words:=ticketAt (g₀) (SortedInput.values (g₀) (v.originalValues data₀) (v.walkValues (Gather.reaching R)))
    words j h y 6 ≤ 2*(fmt₀).cap ∧ words j h y 7 ≤ 10 :=by
  intro words
  apply global_role_fields
  · intro idx
    refine (v.original_anchor_number data₀ j 1 idx h y).le.trans ?_
    apply v.catalog_digit_le R state bands (v.matchAnchorIndex idx 1).2 (v.matchAnchorIndex idx 1).1
    intro source
    exact (v.match_anchor_field_room v.profile b idx source).1
  · intro idx
    refine (v.original_anchor_number data₀ j 2 idx h y).le.trans ?_
    apply v.catalog_digit_le R state bands (v.matchAnchorIndex idx 2).2 (v.matchAnchorIndex idx 2).1
    intro source
    exact Nat.le_of_lt_succ (v.match_anchor_field_room v.profile b idx source).2
  · intro flag
    exact (v.original_mouth_number data₀ j 1 h y).le.trans (mouth flag)

theorem matched_role_room (j : Fin J) (h : Fin (l₀).hosts) (y : Fin (l₀).groups)
    (mouth : (orig j 0 h y).val=2 → (born j 1 h y).val ≤ 10) (base : 22*(fmt₀).cap+10<2^((l₀).size+2)) :
    let words:=ticketAt (g₀) (SortedInput.values (g₀) (v.originalValues data₀) (v.walkValues (Gather.reaching R)))
    11*(v.ticketRoles words j 1 h y).val+(v.ticketRoles words j 2 h y).val < 2^((l₀).size+2) :=by
  intro words
  obtain ⟨old,role⟩:=v.matched_role_fields R state bands serial peer blocks bound groups orig prior born j h y mouth
  have a : (v.ticketRoles words j 1 h y).val ≤ words j h y 6 :=Nat.mod_le _ _
  have boundedRole : (v.ticketRoles words j 2 h y).val ≤ words j h y 7 :=Nat.mod_le _ _
  change words j h y 6 ≤ 2*(fmt₀).cap at old
  change words j h y 7 ≤ 10 at role
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
