import OAI.Hierarchy.DescentDatedMatchedPrefixBoards
import OAI.Hierarchy.DescentDatedMaterialSourceRun

namespace OAI
/-! # A single retained native material image supplies all raw and matched source rows -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentSharedCableNames DescentPackedColony DescentDatedOperandReadPipeline
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
local notation "start₀" => v.materialStart floor
local notation "limit₀" => (e₀).endAddress start₀
local notation "base₀" => v.originMouthEnd floor
local notation "old₀" => v.operandOldHeaderStart floor
local notation "end₀" => v.operandHeaderEnd floor
local notation "map₀" => (e₀).projectionStart start₀
local notation "mapEnd" => DepotRAM.Material.Route.Projection.roof b B M K G P₀ map₀
local notation "reverse₀" => (v.operandRanks floor).reverseRank
variable {w : ℕ} (adj parts : Bank) (initial m : Memory w) (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts → Fin (v.material).oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short)) (bands : (v.material).oldGroups=v.material.groups*v.material.blocks)
local notation "head" => PriorHeader.image H G M D first₀ adj initial
local notation "material" => v.materialAt start₀ parts reverse₀ w
local notation "out" => (v.operandEarlyPhase floor w A).image m

theorem retained_material_boards
    (issued : PriorHeader.Room adj H G M D first₀ w) (bill : v.MaterialRoom start₀ parts reverse₀ w)
    (neighbor : ∀h j,initial (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (start : prior₀=start₀) (earlier : limit₀≤base₀)
    (saved : ∀a,a<limit₀→ out a=(material).image head a)
    (original : DescentPackedColony.Reads parts (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes initial)
    (partLow : parts.base+parts.size≤first₀)
    (panel : DescentPackedColony.Reads A.venue.panel (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes m)
    (early : A.venue.panel.base+A.venue.panel.size≤base₀)
    (sent : H*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (bits : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) b≤w/2)
    (past : 0<(e₀).oldLanes) (lanes : 0<M) (blocks : 0<B) (grow : H≤K) (space : end₀<2^w) :
    (∀j p x,(v.operandDatum floor x p j).Fits w end₀ ∧ Source (v.operandDatum floor x p j)
      (v.matchedFieldValue R state bands j p x) M out) ∧
    (∀x f i,(v.rawFieldHead floor x f i).Fits w end₀ ∧ Source (v.rawFieldHead floor x f i)
      (v.rawMaterialValue R state bands x f i) M out) ∧
    ∀key,(v.narrowHead floor key).Fits w end₀ ∧ Source (v.narrowHead floor key) (v.narrowValue R key) M out :=by
  let «prefix»:=(((v.materialCharts start₀ w).seq (v.materialJoin start₀ parts reverse₀ w)).seq (v.materialSheets start₀ w)).seq
    ((v.materialJob start₀).phase ((e₀).overlapStart start₀) w)
  let prev:=«prefix».image head
  have live : (material).image head=(DepotRAM.Material.Route.Projection.stage H K G M P₀ b B v.materialPitch map₀ w).image prev:=by
    change (v.materialMaps start₀ w).image prev=_
    change (DepotRAM.Material.Route.Projection.stage H K G M (e₀).reach b B v.materialPitch map₀ w).image prev=_
    rw [bill.sameReach]
  have bought : mapEnd≤limit₀:=by rw [←bill.sameReach,v.stampedRoof]
  have kept0 : prior₀≤limit₀:=by rw [start,MaterialExtent.translated];exact Nat.le_add_right ..
  have path : base₀≤v.operandPathStart floor:=by rw [operandPathStart,DescentDatedOperandPages.affine];exact Nat.le_add_right ..
  have book : old₀≤end₀:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have dep:=v.original_header_step floor A m early sent bits (kept0.trans (earlier.trans path)) (book.trans_lt space)
  have copy:=v.header_dictionary_step floor w ((v.operandBeforeHeaders floor w A).image m) space
  have throughStep:=dep.thenStep copy
  have back (i : ℕ) (hi : i<limit₀) : m i=(material).image head i:=
    (throughStep.frame i (.inl (hi.trans_le earlier))).symm.trans (saved i hi)
  have mat:=v.material_any bill head
  have before (i : ℕ) (hi : i<prior₀) : (material).image head i=head i:=mat.2 i (.inl (hi.trans_le start.le))
  have first:=PriorHeader.any H G M D first₀ adj issued initial
  have old : DescentPackedColony.Reads parts (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes head:=by
    intro j
    exact (first.2 _ (.inl ((Nat.add_lt_add_left ((row H (e₀).oldGroups (e₀).oldLanes j).isLt.trans_le bill.sourceSize) _).trans_le partLow))).trans (original j)
  have racks:=PriorHeader.held_directory first₀ adj issued initial R neighbor ((material).image head) before
  have ports:=PriorHeader.held_ports first₀ adj issued initial R neighbor ((material).image head) before
  have safe : H*chunks G M<2^w:=
    (PriorHeader.limits H G M D).2.2.2.2.trans_lt
      (PriorHeader.at_bank H G M D first₀ 0 (P₀+20) (by omega) issued.roof).2.1
  have raw:=v.original_raw_fields floor parts head out R state bands bill past lanes blocks grow
    (PriorHeader.directory first₀ adj issued initial R neighbor).reverse old kept0 safe ports.1 racks saved
  have joint:=v.matched_prefix_boards floor A adj initial prev m R state bands issued neighbor (kept0.trans earlier)
    (bought.trans earlier) (fun i hi=>(back i (hi.trans_le kept0)).trans (before i hi))
    (fun i hi=>(back i (hi.trans_le bought)).trans (congrFun live i)) early sent bits panel past lanes blocks safe space
  refine ⟨joint.1,?_,joint.2⟩
  intro x f i
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (earlier.trans throughStep.order) (raw x f i).1,(raw x f i).2⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
