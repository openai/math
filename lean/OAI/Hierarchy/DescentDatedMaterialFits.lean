import OAI.Hierarchy.DescentDatedMaterialForward

namespace OAI
/-! Numeric address bounds for original and receiving material expressions on arbitrary memory. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentHaloWalkRAM DescentSharedCableNames DescentHaloPackedRebase DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "e"=>v.material
local notation "fmt"=>v.ticket.depotShape v.short
local notation "P₀"=>breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "H"=>v.material.oldHosts
local notation "G"=>v.material.groups
local notation "M"=>v.material.lanes
local notation "B"=>v.material.blocks
local notation "b"=>v.material.fieldBits
local notation "N"=>DepotRAM.Material.Sheets.count fmt
variable (base out w : ℕ) (endLow : v.material.endAddress base≤out) (room : out<2^w)
include endLow room in
theorem received_fit (hm : 0<M) (hb : 0<B) (bands : (e).oldGroups=G*B) (grows : H≤(e).hosts)
    (j : Fin N) :
    (v.receivedBank base j).Fits w out ∧ H*chunks G M≤(v.receivedBank base j).size :=by
  let n:=H*chunks (e).oldGroups (M*B)
  have eqn : n=H*chunks G M:=by dsimp [n];rw [bands,chunks_group _ _ _ hm hb]
  let job:=v.materialJob base
  have a:=v.material_addresses base
  have high:(e).projectionStart base≤(e).endAddress base:=by
    dsimp [MaterialExtent.endAddress,MaterialExtent.mapsStart]
    omega
  have full:=Overlap.output_fits ((e).overlapStart base) ((e).fields*H) (e).oldGroups (e).oldLanes (M*B) b w
    (high.trans_lt (endLow.trans_lt room))
  have i : j.val<(e).fields:=(v.materials_count ▸ j.isLt)
  have volume : (e).fields*n≤(job.target ((e).overlapStart base)).size :=by
    have h:=full.2.1
    simp only [job,materialJob,Overlap.Job.target,n,Overlap.rows,Nat.mul_assoc] at h ⊢
    exact h
  have atMost : j.val*n≤(job.target ((e).overlapStart base)).size:=(Nat.mul_le_mul_right n i.le).trans volume
  have taken: (job.target ((e).overlapStart base)).base+j.val*n≤(e).projectionStart base:=
    (Nat.add_le_add_left atMost _).trans full.1.2.2
  have num : n≤(e).nextRows+1:=eqn ▸ (Nat.mul_le_mul_right _ grows).trans (Nat.le_succ _)
  have bits : 2^Nat.clog 2 n ≤ 2^Nat.clog 2 ((e).nextRows+1):=
    Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right _ num)
  have space: (e).projectionStart base+2^Nat.clog 2 ((e).nextRows+1)≤(e).endAddress base:=by
    have h:=Nat.mul_le_mul_right (2^Nat.clog 2 ((e).nextRows+1)) (show 1≤(e).reach+2 by omega)
    unfold MaterialExtent.endAddress MaterialExtent.mapsStart
    simp only [one_mul] at h
    omega
  have bound:(v.receivedBank base j).base+(v.receivedBank base j).size≤out:=
    (Nat.add_le_add taken bits).trans (space.trans endLow)
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt room),bound⟩,
    eqn ▸ Nat.le_pow_clog (by decide) n⟩

include endLow room in
theorem material_socket_fits (reach : (e).reach=P₀) (ranks : DescentOrdinaryDonorRankDirectory.Banks)
    (ports : Ports P₀) (path : Fin P₀) (z : DepotRAM.Material.Seat fmt) (x : Fin B) (f : Port)
    (early : Accessible (keepPorts ranks ports) (v.receivedBank base (DepotRAM.Material.Sheets.id fmt (donorField f) z)) H G M w out) :
    (v.materialSocket base ranks ports path z x f).Fits w out :=by
  have bound:Projection.roof b B M (e).hosts G P₀ ((e).projectionStart base)≤out:=by
    rw [←reach,v.stampedRoof];exact endLow
  have t:=Projection.socket_fit (K:=(e).hosts) (a:=b) (r:=B) («G»:=G) («M»:=M) ((e).projectionStart base)
    out bound room ranks ports _ f path x early
  exact ⟨t.apply,t.right,t.shift,t.left⟩

include endLow room in
theorem origin_socket_fits (hm : 0<M) (hb : 0<B) (bands : (e).oldGroups=G*B) (grows : H≤(e).hosts)
    (z : DepotRAM.Material.Seat fmt) (x : Fin B) (low : Bool) :
    (v.originSocket base z x low).Fits w out :=by
  let i := DepotRAM.Material.Sheets.id fmt (if low then 2 else 0) z
  let addr:=(e).projectionStart base
  have core : (v.receivedBank base i).Fits w out := (v.received_fit base out w endLow room hm hb bands grows i).1
  have mapped : Projection.mapBase b B M addr≤out:=by
    calc
      _ ≤ Projection.markBase b B M (e).hosts G addr := Nat.le_add_right ..
      _ ≤ Projection.roof b B M (e).hosts G (e).reach addr := Nat.le_add_right ..
      _ = (e).endAddress base := v.stampedRoof base
      _ ≤ out := endLow
  let launch:=Projection.launchBank b B M addr low x
  have last : launch.base+launch.size≤out:=(Projection.launch_before b B M addr low x).trans mapped
  have lf : launch.Fits w out:=⟨Nat.two_pow_pos _,
    (Nat.le_add_left _ _).trans_lt (last.trans_lt room),last⟩
  exact ⟨lf,core,trivial⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
