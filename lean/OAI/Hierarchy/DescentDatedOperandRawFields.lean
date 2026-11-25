import OAI.Hierarchy.DescentDatedSampledMaterialValues
import OAI.Hierarchy.DescentDatedMaterialFits
import OAI.Hierarchy.DescentDatedOperandOriginalHeads

namespace OAI
/-! # The six raw candidate fields come from the original measured material pass -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentPackedColony DescentSharedCableNames DescentHaloPackedRebase
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ)
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "e₀" => v.material
local notation "H" => (e₀).oldHosts
local notation "G" => (e₀).groups
local notation "M" => (e₀).lanes
local notation "B" => (e₀).blocks
local notation "b" => (e₀).fieldBits
local notation "P₀" => breadth (fmt₀).degree
local notation "O" => DepotRAM.Material.roles fmt₀
local notation "base₀" => v.materialStart floor
local notation "end₀" => (e₀).endAddress base₀
local notation "priorEnd" => PriorHeader.endAddress H G M (fmt₀).degree (v.donorEnd floor)
local notation "rank₀" => v.operandRanks floor
local notation "ports₀" => v.operandRoster floor

theorem original_raw_fields {w : ℕ} (parts : Bank) (m later : Memory w)
    (R : Fin H → Fin (fmt₀).degree → Option (Fin H)) (state : Fin H → Fin (e₀).oldGroups → DepotRAM.Parts fmt₀)
    (bands : (e₀).oldGroups=G*B) (reserve : v.MaterialRoom base₀ parts (rank₀).reverseRank w)
    (priorPitch : 0<(e₀).oldLanes) (pitch : 0<M) (blocks : 0<B) (grow : H≤(e₀).hosts)
    (oldRank : ∀h p,m ((rank₀).reverseRank.base+(finProdFinEquiv (h,p)).val)=
      ((DepotRAM.Material.reverseEntries fmt₀ R h p).val:Word w))
    (old : Reads parts (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes m)
    (earlier : priorEnd≤end₀) (safe : H*chunks G M<2^w)
    (mounted : Mounted (ports₀) (Gather.reaching R) ((v.materialAt base₀ parts (rank₀).reverseRank w).image m) G M)
    (rankRead : DescentOrdinaryDonorRankDirectory.Reads R (rank₀) ((v.materialAt base₀ parts (rank₀).reverseRank w).image m))
    (retained : ∀a,a<end₀→later a=(v.materialAt base₀ parts (rank₀).reverseRank w).image m a) :
    ∀x f i,(v.rawFieldHead floor x f i).Fits w end₀ ∧ Source (v.rawFieldHead floor x f i) (v.rawMaterialValue R state bands x f i) M later :=by
  intro x f i
  obtain ⟨⟨p,t⟩,rfl⟩:=finProdFinEquiv.surjective i
  let seat:=(DepotRAM.Material.seatIndex fmt₀).symm t
  let j:=DepotRAM.Material.Sheets.rawId fmt₀ f seat
  let src:=v.receivedBank base₀ j
  have cap:=v.received_fit base₀ end₀ w le_rfl reserve.range pitch blocks bands grow j
  have access:=(PriorHeader.accessible_at («H» := H) (D:=(fmt₀).degree) («M» := M) («G» := G) (v.donorEnd floor)
    (earlier.trans_lt reserve.range) src end₀ earlier cap.1 cap.2).2
  have within : DepotRAM.Material.Route.Projection.roof b B M (e₀).hosts G P₀ ((e₀).projectionStart base₀)≤end₀:=by
    rw [←reserve.sameReach,v.stampedRoof]
  have room:=DepotRAM.Material.Route.Projection.socket_fit (K:=(e₀).hosts) (a:=b) (r:=B) («G» := G) («M» := M)
    ((e₀).projectionStart base₀) end₀ within reserve.range (rank₀) (ports₀) src 0 p x access
  have fit : (v.bankSocket base₀ (rank₀) (ports₀) j p x 0).Fits w end₀ :=⟨room.apply,room.right,room.shift,room.left⟩
  have read:=v.bank_socket_issued base₀ (rank₀) (ports₀) m R state reserve priorPitch pitch blocks bands oldRank old
    p j x 0 end₀ le_rfl reserve.range safe access mounted rankRead
  simp only [rawFieldHead,Equiv.symm_apply_apply,rawSocket,rawMaterialValue]
  refine ⟨fit,?_⟩
  intro row_
  exact (eval_below _ _ _ later fit retained).trans (read row_)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
