import OAI.Hierarchy.DescentDatedMaterialRuns

namespace OAI
/-! Read each true original donor field, at its new SIMD width, after installing the receiving maps. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "e" => v.material
local notation "s" => v.ticket.depotShape v.short
local notation "n" => v.material.sourceRows
local notation "P₀" => breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "L" => v.material.oldLanes
local notation "H" => v.material.oldHosts
local notation "G₀" => v.material.oldGroups
local notation "N" => DepotRAM.Material.Sheets.count s
variable {base w : ℕ} {parts reverse : Bank} (ok : v.MaterialRoom base parts reverse w) (m : Memory w)
variable (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts)) (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
local notation "cal" => DepotRAM.Material.reverseEntries s R
local notation "rev" => fun h (_:Fin G₀)=>digest (cal h)
local notation "words" => DepotRAM.Material.Sheets.fields s v.materialFormat state rev
local notation "b₁" => v.material.joinBase base
local notation "b₂" => v.material.observationsStart base
local notation "b₃" => v.material.overlapStart base
local notation "b₄" => v.material.projectionStart base
local notation "end₀" => v.material.endAddress base
local notation "join" => v.joinBank base
local notation "job" => v.materialJob base
local notation "one" => v.materialCharts base w
local notation "two" => v.materialJoin base parts reverse w
local notation "three" => v.materialSheets base w
local notation "four" => Overlap.Job.phase job b₃ w
local notation "five" => v.materialMaps base w
include ok in
theorem material_issued (positive : 0<L) (rank : ∀h p,m (reverse.base+(finProdFinEquiv (h,p)).val)=
    ((cal h p).val:Word w)) (original : Reads parts (fun h g=>DepotRAM.combine s (state h g)) L m)
    (j : Fin N) :
    Reads (v.receivedBank base j) (words j) ((e).lanes*(e).blocks) ((v.materialAt base parts reverse w).image m) :=by
  obtain ⟨b₀,b₁',b₂',b₃',b₄',b₅',b₆'⟩:=v.material_order (base:=base)
  obtain ⟨address,stop,prev,overlapEnd,_⟩:=v.material_addresses base
  have finish:=ok.range
  have chart:base+DonorChartBook.words H G₀ L P₀≤b₁:=by
    rw [←v.material_chartEnd base ok.sameReach];exact ((Nat.le_add_right (base+DonorChartBook.words H G₀ L P₀) _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have warm:=DonorChartBook.mount H G₀ L P₀ base m (by omega)
  have fixed:DonorChartBook.Static H G₀ L P₀ base ((one).image m):=warm.2.1
  have keep (addr : ℕ) (lt : addr<base) : (one).image m addr=m addr:=warm.2.2 addr (Or.inl lt)
  have old : Reads parts (fun h g=>DepotRAM.combine s (state h g)) L ((one).image m) :=fun p=>
    (keep _ ((Nat.add_lt_add_left ((row H G₀ L p).isLt.trans_le ok.sourceSize) _).trans_le ok.source.2.2)).trans (original p)
  have nr:H*P₀≤reverse.size:=by rw [←ok.sameReach];exact ok.reverseSize
  have actual (h : Fin H) (p : Fin P₀) : (one).image m (reverse.base+(finProdFinEquiv (h,p)).val)=((cal h p).val:Word w) :=
    (keep _ ((Nat.add_lt_add_left ((finProdFinEquiv (h,p)).isLt.trans_le nr) _).trans_le ok.reverse.2.2)).trans (rank h p)
  have pf:=v.material_header_fit ok
  have table:=DonorChartBook.ready H G₀ L P₀ base reverse cal ((one).image m) fixed actual
  have value:=DescentHaloPackedRebase.source _ b₁ pf cal ((one).image m) table
  have input:parts.Fits w b₁:=⟨ok.source.1,ok.source.2.1,ok.source.2.2.trans b₀⟩
  have both:=RegisterJoin.physical (DepotRAM.totalBits s) (DepotRAM.chartBits s) b₁ _ _ ((one).image m)
    (by exact ⟨input,trivial⟩) (context_fits _ b₁ pf) (by change (join).base+n<2^w;rw [address];omega)
    _ _ (source_column parts b₁ input _ _ ok.sourceSize old) value
  have count:n≤(join).size:=(Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _)
  have edge:RoleScans.limit (DepotRAM.Material.Sheets.bits s) H G₀ L b₂ N=(e).valuesStart base+(e).fields*n:=by
    change (job).src.base+N*n=_;rw [prev,v.materials_count]
  have issued:=DepotRAM.Material.Sheets.run s v.materialFormat b₂ join ((two).image ((one).image m))
    stop.le count ok.purchase (by rw [edge];omega) state rev both
  let before:=(three).image ((two).image ((one).image m))
  have jobFit:(job).src.Fits w b₃:=⟨Nat.two_pow_pos _,(Nat.le_add_left (job).src.size (job).src.base).trans_lt (overlapEnd.trans_lt (b₅'.trans_lt (b₆'.trans_lt finish))),overlapEnd.le⟩
  have jobSize:N*H*chunks G₀ L≤(job).src.size:=by
    change N*H*chunks G₀ L≤2^Nat.clog 2 (N*(H*chunks G₀ L)+1)
    rw [Nat.mul_assoc]
    exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have roof₀:=Overlap.output_fits b₃ (job).hosts (job).groups (job).old (job).new_ (job).bits w (by change b₄<2^w;omega)
  have sameCount:N*H=(e).fields*H:=congrArg (·*H) v.materials_count
  have space:Overlap.finish b₃ (N*H) G₀ L ((e).lanes*(e).blocks) (e).fieldBits<2^w:=by
    rw [sameCount];exact roof₀.2.2.trans_lt (b₆'.trans_lt finish)
  have pulled:=DescentActorRaster.change_pitch words b₃ (job).src before positive jobFit jobSize space issued
  have final:=DepotRAM.Material.Route.Projection.any (D:=(s).degree) (e).oldHosts (e).hosts (e).groups (e).lanes
    (e).fieldBits (e).blocks v.materialPitch b₄ ((four).image before) (by
      rw [←ok.sameReach,v.stampedRoof];exact finish)
  intro p
  let ix:=j.val*(H*chunks G₀ ((e).lanes*(e).blocks))+(row H G₀ ((e).lanes*(e).blocks) p).val
  have inside:ix<N*(H*chunks G₀ ((e).lanes*(e).blocks)):=by
    refine (Nat.add_lt_add_left (row H G₀ ((e).lanes*(e).blocks) p).isLt _).trans_le ?_
    rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ j.isLt
  have safe:((job).target b₃).base+ix<b₄:=by
    have small : ix<(e).fields*H*chunks G₀ ((e).lanes*(e).blocks):=by simpa only [Nat.mul_assoc,v.materials_count] using inside
    exact (Nat.add_lt_add_left small _).trans_le roof₀.2.2
  have saved:(five).image ((four).image before) (((job).target b₃).base+ix)=(four).image before (((job).target b₃).base+ix):=by
    simpa only [materialMaps,MaterialProgram.materialMaps,materialProgram,materialFormat,ok.sameReach] using final.2 _ (Or.inl safe)
  change (five).image ((four).image before) (_+j.val*_+_)=_
  rw [Nat.add_assoc]
  refine saved.trans ?_
  have yes:=pulled.2.1 j p
  simp only [sameCount,Overlap.Job.target,Overlap.Job.phase,Nat.add_assoc,ix] at yes ⊢
  exact yes

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
