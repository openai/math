import OAI.Hierarchy.DescentDatedSampledMaterialValues
import OAI.Hierarchy.DescentDatedPhysicalMatcherIndex
import OAI.Hierarchy.DescentDatedOperandOriginalHeads
import OAI.Hierarchy.DescentDatedPriorHeaderPorts

namespace OAI
/-! # Recover the original matcher and both directions of the anchor on every real source page -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentPackedColony DescentSharedCableNames DescentDatedOperandPages
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "G" => (e₀).groups
local notation "M" => (e₀).lanes
local notation "B" => (e₀).blocks
local notation "b" => (e₀).fieldBits
local notation "base₀" => v.originMouthEnd floor
local notation "next₀" => v.operandPathStart floor
local notation "mapStart" => (e₀).projectionStart (v.materialStart floor)
local notation "mapEnd" => DepotRAM.Material.Route.Projection.roof b B M K G P₀ mapStart
local notation "rank₀" => v.operandRanks floor
local notation "ports₀" => v.operandRoster floor
local notation "l₀" => v.operandDepotLayout
local notation "priorEnd" => PriorHeader.endAddress H G M D (v.donorEnd floor)

private theorem reindex {hosts fromGroups toGroups bits lanes w : ℕ} (eqn : fromGroups=toGroups) (bank : Bank) (x : Fin hosts → Fin fromGroups → Cell bits)
    (m : Memory w) (read : Reads bank x lanes m) : Reads bank (fun h (g : Fin toGroups)=>x h (g.cast eqn.symm)) lanes m :=by
  subst toGroups
  exact read

theorem matched_fields {w : ℕ} (A : v.ArgumentEntry) (m projected later : Memory w)
    (R : Fin H → Fin D → Option (Fin H)) (state : Fin H → Fin (e₀).oldGroups → DepotRAM.Parts fmt₀)
    (bands : (e₀).oldGroups=G*B) (out : ℕ) (bought : next₀≤out) (room : out<2^w)
    (positive : 0<(e₀).oldLanes) (lanes : 0<M) (blocks : 0<B)
    (previous : A.venue.panel.base+A.venue.panel.size≤base₀)
    (rows : H*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (digits : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) b≤w/2)
    (prev : Reads A.venue.panel (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes m)
    (staged : ∀i,i<next₀→later i=(v.operandDepot floor w A).image m i)
    (prior : priorEnd≤out) (within : mapEnd≤out)
    (mapRead : ∀i,i< mapEnd→later i=(DepotRAM.Material.Route.Projection.stage H K G M P₀ b B
      v.materialPitch mapStart w).image projected i)
    (mounted : Mounted (ports₀) (Gather.reaching R) later G M)
    (ranks : DescentOrdinaryDonorRankDirectory.Reads R (rank₀) later) (safe : H*chunks G M<2^w) :
    ∀j p x,(v.operandDatum floor x p j).Fits w out ∧
      Source (v.operandDatum floor x p j) (v.matchedFieldValue R state bands j p x) M later :=by
  have enough:=bought.trans_lt room
  have printed:=issued fmt₀ l₀ base₀ A.venue.panel m state positive previous rows digits enough prev
  intro j p x
  let src:=resultBank fmt₀ l₀ base₀ j
  let fieldValue:=fun (h : Fin H) (g : Fin (e₀).oldGroups)=>law fmt₀ v.profile b j.val (DepotRAM.combine fmt₀ (state h g))
  have allocated:=returned_room fmt₀ l₀ base₀ enough j
  have shape : chunks (e₀).oldGroups (M*B)=chunks G M:=by rw [bands,chunks_group _ _ _ lanes blocks]
  have capacity : H*chunks G M≤ src.size:=by
    simpa only [src,operandDepotLayout,shape] using allocated.2
  have access := (PriorHeader.accessible_at («H»:=H) («D»:=D) («M»:=M) («G»:=G) (v.donorEnd floor)
    (prior.trans_lt room) src out prior ⟨allocated.1.1,allocated.1.2.1,allocated.1.2.2.trans bought⟩ capacity).2
  have measured : Reads src fieldValue (M*B) later:=by
    intro row_
    have inside : (row H (e₀).oldGroups (M*B) row_).val<src.size:=
      (row H (e₀).oldGroups (M*B) row_).isLt.trans_le allocated.2
    exact (staged _ ((Nat.add_lt_add_left inside _).trans_le allocated.1.2.2)).trans (printed.2.1 j row_)
  have read := DepotRAM.Material.Route.Projection.source_later mapStart out within room R (rank₀) (ports₀) src 0 p x
    (fun h (g : Fin (G*B))=>fieldValue h (g.cast bands.symm)) v.materialPitch projected later lanes blocks mapRead
    (reindex bands src fieldValue later measured) access mounted ranks safe
  have fit:=DepotRAM.Material.Route.Projection.socket_fit («K»:=K) mapStart out within room (rank₀) (ports₀) src 0 p x access
  exact ⟨⟨fit.apply,fit.right,fit.shift,fit.left⟩,read⟩

theorem old_and_anchor {w out : ℕ} (R : Fin H → Fin D → Option (Fin H))
    (state : Fin H → Fin (e₀).oldGroups → DepotRAM.Parts fmt₀) (bands : (e₀).oldGroups=G*B)
    (m : Memory w)
    (measured : ∀j p x,(v.operandDatum floor x p j).Fits w out ∧
      Source (v.operandDatum floor x p j) (v.matchedFieldValue R state bands j p x) M m) :
    (∀x f i,let k:=v.matchOldIndex i f
      (v.oldSlotHead floor x f i).Fits w out ∧ Source (v.oldSlotHead floor x f i) (v.matchedFieldValue R state bands k.2 k.1 x) M m) ∧
    ∀x f i,let k:=v.matchAnchorIndex i f
      (v.anchorHead floor x f i).Fits w out ∧ Source (v.anchorHead floor x f i) (v.matchedFieldValue R state bands k.2 k.1 x) M m :=by
  exact ⟨fun x f i=>measured (v.matchOldIndex i f).2 (v.matchOldIndex i f).1 x,
    fun x f i=>measured (v.matchAnchorIndex i f).2 (v.matchAnchorIndex i f).1 x⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
