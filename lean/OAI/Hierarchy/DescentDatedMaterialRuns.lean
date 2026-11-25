import OAI.Hierarchy.DescentDatedMaterialRoom

namespace OAI
/-! Arbitrary input memories run the same dated ordinary receiving program with the same bounds. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony
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
variable {base w : ℕ} {parts reverse : Bank} (ok : v.MaterialRoom base parts reverse w)
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
private theorem source_end : base+DonorChartBook.words H G₀ L P₀≤b₁ :=by
  have proof:=v.material_chartEnd base ok.sameReach
  rw [←proof]
  exact ((Nat.le_add_right (base+DonorChartBook.words H G₀ L P₀) _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)

include ok in
private theorem overlap_fit : (job).src.Fits w b₃ :=by
  obtain ⟨_,_,_,_,_,lt,high⟩:=v.material_order (base:=base)
  have end_:=ok.range
  have sep:(job).src.base+(job).src.size=b₃:=(v.material_addresses base).2.2.2.1
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left (job).src.size (job).src.base).trans_lt (sep.trans_lt (lt.trans_lt (high.trans_lt end_))),sep.le⟩

include ok in
theorem material_any (m : Memory w) :
    (v.materialAt base parts reverse w).Runs m ∧
    ∀x,x<base ∨ end₀≤x→(v.materialAt base parts reverse w).image m x=m x :=by
  obtain ⟨b₀,b₁',b₂',b₃',b₄',b₅',b₆'⟩:=v.material_order (base:=base)
  obtain ⟨address,stop,prev,overlapEnd,_⟩:=v.material_addresses base
  have chart:=source_end v (base:=base) (ok:=ok)
  have finish:=ok.range
  have warm:=DonorChartBook.mount H G₀ L P₀ base m (by omega)
  have pf:=v.material_header_fit ok
  have jf:=RegisterJoin.any (DepotRAM.totalBits s) (DepotRAM.chartBits s) b₁ (.lookup parts .row) (context (v.rankHeader base reverse)) ((one).image m)
    (by exact ⟨⟨ok.source.1,ok.source.2.1,ok.source.2.2.trans b₀⟩,trivial⟩)
    (context_fits _ b₁ pf) («H»:=H) (G:=G₀) (M:=L) (by change (v.joinBank base).base+n<2^w;rw [address];omega)
  have count:n≤(join).size:=(Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _)
  have shape:RoleScans.limit (DepotRAM.Material.Sheets.bits s) H G₀ L b₂ N=(e).valuesStart base+(e).fields*n:=by
    change (job).src.base+N*n=_
    rw [prev,v.materials_count]
  have material:=DepotRAM.Material.Sheets.any s v.materialFormat b₂ join ((two).image ((one).image m))
    stop.le count ok.purchase (by rw [shape];omega)
  let before:=(three).image ((two).image ((one).image m))
  have endJob:=Overlap.output_fits b₃ (job).hosts (job).groups (job).old (job).new_ (job).bits w (by
    change b₄<2^w;omega)
  have clipped:Overlap.finish b₃ (job).hosts (job).groups (job).old (job).new_ (job).bits≤b₄:=endJob.2.2
  have write:=Overlap.any b₃ (job).hosts (job).groups (job).old (job).new_ (job).bits (job).src before
    (overlap_fit v ok) (clipped.trans_lt (by omega))
  have there : ∀m':Memory w,(five).Runs m' ∧ ∀x,x<b₄ ∨ end₀≤x→(five).image m' x=m' x :=by
    intro m'
    have boundary:=v.stampedRoof base
    rw [ok.sameReach] at boundary
    have run:=DepotRAM.Material.Route.Projection.any (D:=(s).degree) (e).oldHosts (e).hosts (e).groups (e).lanes
      (e).fieldBits (e).blocks v.materialPitch b₄ m' (boundary.trans_lt finish)
    change (DepotRAM.Material.Route.Projection.stage _ _ _ _ (e).reach _ _ _ _ _).Runs _ ∧ _
    simpa only [materialMaps,MaterialProgram.materialMaps,materialProgram,materialFormat,ok.sameReach,boundary] using run
  have last:=there ((four).image before)
  constructor
  · exact NativePhase.seq_runs _ five m
      (NativePhase.seq_runs _ four m
        (NativePhase.seq_runs _ three m (NativePhase.seq_runs one two m warm.1 jf.1) material.1) write.1) last.1
  · intro x away
    have outside (lo hi : ℕ) (l : base≤lo) (h : hi≤end₀) : x<lo ∨ hi≤x :=by rcases away with small|big <;> omega
    change (five).image _ x=m x
    refine (last.2 _ (outside _ _ (by omega) le_rfl)).trans ((write.2.1 _ (outside _ _ (by omega) (by omega))).trans ?_)
    refine (material.2 _ (outside _ _ (by omega) (by rw [shape];omega))).trans ?_
    refine (jf.2 _ (outside _ _ b₀ (by change (join).base+n≤_;rw [address];omega))).trans ?_
    exact warm.2.2 _ (outside _ _ le_rfl (by omega))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
