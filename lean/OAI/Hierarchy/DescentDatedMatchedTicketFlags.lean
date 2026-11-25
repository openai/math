import OAI.Hierarchy.DescentDatedMatchedTicketValues
import OAI.Hierarchy.DescentDatedTicketRouteData

namespace OAI
/-! # Both capture bits and the side mark in the actual eight-column operand source -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry) (v : Data g)

theorem selected_raw_max (j : Fin g.jobs) (f : Fin 8) (h : Fin g.hosts) (k : Fin g.groups) (limit : ℕ)
    (before : ∀i,(v.raw j f i h k).val≤limit) : (rawV g v j f h k).val≤limit :=by
  unfold rawV picked DescentResetStemMux.pick
  split
  · apply before
  · exact Nat.zero_le _

theorem raw_ticket_flags (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups)
    (left : ∀i,(v.raw j 2 i h k).val≤1) (right : ∀i,(v.raw j 3 i h k).val≤1)
    (mark : ∀i,(v.raw j 5 i h k).val≤1) : Ticket.Flags (ticketAt g v j h k) :=by
  let rawKey := rawLaw g.paths (g.blocks*(g.cap*11)) g.digitBits 0 (fun i=>rawInputs g v j i h k)
  exact Ticket.flags_of_material g.blocks (v.origin j 0 h k).val (v.prior j 0 h k).val
    (rankV g v j 0 h k).val (v.origin j 2 h k).val rawKey.val (rawV g v j 6 h k).val
    (rawV g v j 7 h k).val (v.mouth j 1 h k).val
    (fun f => (anchorV g v j f h k).val)
    (fun f => (rawV g v j (f.castLE (by decide : 6 ≤ 8)) h k).val)
    (selected_raw_max g v j 2 h k 1 left) (selected_raw_max g v j 3 h k 1 right)
    (selected_raw_max g v j 5 h k 1 mark)

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

private theorem flag_cast (bits : ℕ) (x : Bool) : ((x.toNat:Cell bits)).val≤1 :=
  (Nat.mod_le _ _).trans (by cases x <;> decide : x.toNat≤1)

theorem material_flag (x : Fin B) (f : Fin 6) (i : Fin (P₀*O)) (h : Fin K) (k : Fin G)
    (flag : f=2 ∨ f=3 ∨ f=5) :
    (v.rawMaterialValue R state bands x f i h k).val≤1 :=by
  obtain ⟨⟨p,t⟩,rfl⟩:=finProdFinEquiv.surjective i
  obtain ⟨z,rfl⟩:=(DepotRAM.Material.seatIndex fmt₀).surjective t
  cases host : DepotRAM.Material.Route.receiver H v.materialPitch h with
  | none=>simp [rawMaterialValue,DepotRAM.Material.Route.value,DepotRAM.Material.Route.selected,host]
  | some recv=>
    cases hit : Gather.select (Gather.reaching R) recv p with
    | none=>simp [rawMaterialValue,DepotRAM.Material.Route.value,DepotRAM.Material.Route.selected,host,hit]
    | some donor=>
      rw [v.raw_value_at_donor R state bands p x z f h k recv donor host hit]
      rcases flag with rfl|rfl|rfl <;> apply flag_cast

theorem matched_ticket_flags (j : Fin J) (h : Fin (l₀).hosts) (k : Fin (l₀).groups) :
    Ticket.Flags (ticketAt (g₀) (SortedInput.values (g₀) (v.originalValues data₀) (v.walkValues (Gather.reaching R))) j h k) :=by
  apply raw_ticket_flags
  · intro i
    exact (v.original_raw_number data₀ j 2 i h k).le.trans
      (v.material_flag R state bands (v.receiverBlock blocks j) 2 i (h.castLE bound) (k.cast groups) (by decide))
  · intro i
    exact (v.original_raw_number data₀ j 3 i h k).le.trans
      (v.material_flag R state bands (v.receiverBlock blocks j) 3 i (h.castLE bound) (k.cast groups) (by decide))
  · intro i
    exact (v.original_raw_number data₀ j 5 i h k).le.trans
      (v.material_flag R state bands (v.receiverBlock blocks j) 5 i (h.castLE bound) (k.cast groups) (by decide))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
