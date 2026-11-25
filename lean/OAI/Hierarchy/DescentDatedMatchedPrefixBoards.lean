import OAI.Hierarchy.DescentDatedMatchedTicketValues
import OAI.Hierarchy.DescentDatedTicketPreparationTotal
import OAI.Hierarchy.DescentDatedPriorHeaderHeld

namespace OAI
/-! # The same original one-hop board supplies the matched fields and both narrow fields
at the end of the real signed operand prefix. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentSharedCableNames DescentPackedColony DescentDatedOperandReadPipeline DescentDatedSourcePathDirectory
open DescentPacking.PackedMatch.Local.Stage.Chooser
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ) (A : v.ArgumentEntry)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "G" => (e₀).groups
local notation "B" => (e₀).blocks
local notation "M" => (e₀).lanes
local notation "b" => (e₀).fieldBits
local notation "first₀" => v.donorEnd floor
local notation "prior₀" => PriorHeader.endAddress H G M D first₀
local notation "base₀" => v.originMouthEnd floor
local notation "path₀" => v.operandPathStart floor
local notation "rank₀" => v.operandRankStart floor
local notation "books₀" => v.operandOldHeaderStart floor
local notation "end₀" => v.operandHeaderEnd floor
local notation "map₀" => (e₀).projectionStart (v.materialStart floor)
local notation "mapEnd" => DepotRAM.Material.Route.Projection.roof b B M K G P₀ map₀
variable {w : ℕ} (adj : Bank) (initial projected m : Memory w) (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts → Fin (v.material).oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short)) (bands : (v.material).oldGroups=v.material.groups*v.material.blocks)
local notation "head" => PriorHeader.image H G M D first₀ adj initial
local notation "draw" => (DepotRAM.Material.Route.Projection.stage H K G M P₀ b B v.materialPitch map₀ w).image projected
local notation "out" => (v.operandEarlyPhase floor w A).image m

theorem matched_prefix_boards
    (issued : PriorHeader.Room adj H G M D first₀ w)
    (neighbor : ∀h j,initial (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (previous : prior₀≤base₀) (selected : mapEnd≤base₀)
    (unchanged : ∀a,a<prior₀→m a=head a) (projection : ∀a,a< mapEnd→m a=draw a)
    (early : A.venue.panel.base+A.venue.panel.size≤base₀)
    (sent : H*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (bits : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) b≤w/2)
    (old : DescentPackedColony.Reads A.venue.panel (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes m)
    (past : 0<(e₀).oldLanes) (lanes : 0<M) (blocks : 0<B) (safe : H*chunks G M<2^w) (space : end₀<2^w) :
    (∀j p x,(v.operandDatum floor x p j).Fits w end₀ ∧ Source (v.operandDatum floor x p j)
      (v.matchedFieldValue R state bands j p x) M out) ∧
    ∀key,(v.narrowHead floor key).Fits w end₀ ∧ Source (v.narrowHead floor key) (v.narrowValue R key) M out :=by
  let depot:=(v.operandDepot floor w A).image m
  let bank:=nativeBanks H G M D first₀
  let paths:=v.operandPaths floor w
  let pathRam:=paths.image depot
  let both:=paths.seq (v.operandRankPhase floor w)
  let narrow:=both.image depot
  let books:=v.operandHeaderPhase floor w
  have a : base₀≤path₀:=by rw [operandPathStart,DescentDatedOperandPages.affine];exact Nat.le_add_right ..
  have bnd:=paths_fit_hosts H G M D path₀
  have b₁ : path₀≤rank₀:=(Nat.le_add_right ..).trans bnd
  have b₂ : rank₀≤books₀:=Nat.le_add_right ..
  have b₃ : books₀≤end₀:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have pathRoom:=b₁.trans_lt (b₂.trans_lt (b₃.trans_lt space))
  have before:=DescentDatedOperandPages.any fmt₀ v.operandDepotLayout base₀ A.venue.panel m early sent bits pathRoom
  have frame (i : ℕ) (hi : i<base₀) : depot i=m i:=before.2 i (.inl hi)
  have keep (i : ℕ) (hi : i<prior₀) : depot i=head i:=(frame i (hi.trans_le previous)).trans (unchanged i hi)
  have dir:=PriorHeader.held_directory first₀ adj issued initial R neighbor depot keep
  have seen : DescentDatedSourcePathDirectory.Reads bank (Gather.reaching R) depot:=
    ⟨dir.visit,fun h t=>(PriorHeader.held_eight first₀ adj issued initial R neighbor depot keep h t).1⟩
  obtain ⟨access,ep,rk⟩:=native_header_room H G M D first₀ path₀ w (previous.trans a)
    (bnd.trans_lt (b₂.trans_lt (b₃.trans_lt space)))
  have walk:=all_issued bank path₀ access (b₂.trans_lt (b₃.trans_lt space)) R depot seen
  have rankRead:=PriorHeader.held_directory first₀ adj issued initial R neighbor pathRam
    (fun i hi=>(walk.2.1 i (.inl (hi.trans_le (previous.trans a)))).trans (keep i hi))
  have size:=PriorHeader.limits H G M D
  have actual : DescentDatedSourcePathDirectory.Local.Accessible (v.operandRanks floor) H D w rank₀:=
    ⟨bank_before ep b₁,bank_before rk b₁,size.2.2.1,size.2.2.1,access.sentinel⟩
  have atMap:=v.received_map floor projected depot (selected.trans a) pathRoom blocks
    (fun i hi=>(frame i (hi.trans_le selected)).trans (projection i hi))
  have ns:=v.narrow_heads_from_local floor depot R access actual seen rankRead (b₃.trans_lt space)
    safe atMap.1 atMap.2.1 atMap.2.2
  have dictionaries:=v.header_dictionary_step floor w narrow space
  have same (i : ℕ) (hi : i<path₀) : out i=depot i:=
    (dictionaries.frame i (.inl (hi.trans_le (b₁.trans b₂)))).trans (ns.2.1 i (.inl hi))
  have held (i : ℕ) (hi : i<prior₀) : out i=head i:=(same i (hi.trans_le (previous.trans a))).trans (keep i hi)
  have mapped (i : ℕ) (hi : i< mapEnd) : out i=draw i:=
    (same i (hi.trans_le (selected.trans a))).trans ((frame i (hi.trans_le selected)).trans (projection i hi))
  have rest:=b₁.trans (b₂.trans b₃)
  refine ⟨v.matched_fields floor A m projected out R state bands end₀ rest space past lanes blocks early sent bits old
    same (previous.trans (a.trans rest)) (selected.trans (a.trans rest)) mapped
    (PriorHeader.held_ports first₀ adj issued initial R neighbor out held).1
    (PriorHeader.held_directory first₀ adj issued initial R neighbor out held) safe,?_⟩
  intro key
  obtain ⟨fit,read⟩:=ns.2.2 key
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ b₃ fit,?_⟩
  intro row_
  exact (eval_below _ _ narrow out fit (fun i hi=>dictionaries.frame i (.inl hi))).trans (read row_)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
