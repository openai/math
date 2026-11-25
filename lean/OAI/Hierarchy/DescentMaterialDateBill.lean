import OAI.Hierarchy.DescentMaterialRootTariff
import OAI.Hierarchy.DescentMaterialOverlapFee
import OAI.Hierarchy.DescentMaterialIssuedDigit
import OAI.Hierarchy.DescentDatedBeforeSignedMaterial

namespace OAI
/-! # All six timed components of the native signed-material setup -/

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
open MaterialProgram SignedExtent.FeedBound
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem material_date_bill (floor w ratio : ℕ) (parts adj : Bank) (capacity : 256≤v.prior.placement.cap)
    (oldRoom : 2*v.ticket.installedDonorWidth v.short v.profile≤v.payload)
    (newRoom : 2*v.signedLayout.unit≤v.payload) (machine : w≤ratio*v.payload) :
    let x:=v.withIssuedSigned
    let e:=x.material
    let U:=v.ticket.installedDonorWidth v.short v.profile
    let volume:=scanVolume e.oldHosts e.hosts e.oldGroups e.groups e.oldLanes e.lanes e.blocks v.payload
    phaseCost (x.beforeSignedMaterial floor parts adj w)*w≤
      materialFactor v.prior.placement.degree e.blocks e.fields U*volume*(ratio*v.payload) := by
  let x:=v.withIssuedSigned
  let e:=x.material
  let q:=x.materialProgram
  let D:=v.prior.placement.degree
  let U:=v.ticket.installedDonorWidth v.short v.profile
  let h:=v.payload
  let start:=x.donorEnd floor
  let base:=x.materialStart floor
  let reverse:=PriorHeader.reverseRank e.oldHosts e.groups e.lanes D start
  let R:=scanVolume e.oldHosts e.hosts e.oldGroups e.groups e.oldLanes e.lanes e.blocks h
  let N:=e.fields
  have power_pos : 0 < 2 ^ (h / 2) := Nat.pow_pos (by decide)
  have one:1≤R:=by dsimp only [R,scanVolume];omega
  have H:Covers R 1 e.oldHosts:=single (by dsimp only [R,scanVolume];omega)
  have old:Covers R 1 e.sourceRows:=single (by dsimp only [R,scanVolume,MaterialExtent.sourceRows];omega)
  have target:Covers R 1 e.nextRows:=single (by dsimp only [R,scanVolume,MaterialExtent.nextRows];omega)
  have cross:Covers R 1 (e.oldHosts*chunks e.groups e.lanes):=single (by dsimp only [R,scanVolume];omega)
  have repack:Covers R 1 (e.oldHosts*chunks e.oldGroups (e.lanes*e.blocks)):=single (by dsimp only [R,scanVolume];omega)
  have book:Covers R 1 (2^(h/2)):=single (by dsimp only [R,scanVolume];omega)
  have lane:Covers R 1 e.oldLanes:=single ((Nat.div_le_self h (2*U)).trans (by dsimp only [R,scanVolume];omega))
  have fmt:=v.ticket.installed_donor_widths v.short v.profile
  have thick:DepotRAM.totalBits q.depot+DepotRAM.chartBits q.depot≤U:=by
    have full:2*DepotRAM.totalBits q.depot+1≤U:=fmt.2.2
    have chart:DepotRAM.chartBits q.depot≤DepotRAM.totalBits q.depot:=by unfold DepotRAM.totalBits;omega
    omega
  have sourceKey: (DepotRAM.totalBits q.depot+DepotRAM.chartBits q.depot)*e.oldLanes≤h/2 :=
    (Nat.mul_le_mul_right _ thick).trans (by rw [Nat.mul_comm]; exact lanes_fit h U)
  have sourcePage:Covers R 1 (2^((DepotRAM.totalBits q.depot+DepotRAM.chartBits q.depot)*e.oldLanes)) :=
    (Nat.pow_le_pow_right (by decide) sourceKey).trans book
  have resultPage:Covers R 1 (2^((e.fieldBits*e.blocks+e.fieldBits)*e.lanes)) :=
    (Nat.pow_le_pow_right (by decide) (v.signedLayout.material_width h)).trans book
  have h0:= (header_fee e.oldHosts e.groups e.lanes D start adj w).trans (prior_rows one H cross)
  have h1:= (q.chart_fee base w).le.trans (q.chart_rows one old lane)
  have h2:= (q.join_fee base parts reverse w).trans (q.join_rows one old sourcePage)
  have h3:= q.sheets_rows base w one old sourcePage
  have h5:= (q.map_fee base w).le.trans (q.map_rows one target resultPage)
  have ordinary:=add (add (add (add h0 h1) h2) h3) h5
  have honest:=v.material_overlap_fee base w ratio (v.signed_digit_fits capacity) oldRoom newRoom machine
  let overlap:=((q.materialJob base).phase (e.overlapStart base) w)
  have raw:Covers R ((4*U*e.blocks+3)+N+N+1)
      ((4*U*e.blocks+3)*2^(h/2)+(N*e.oldHosts)*chunks e.oldGroups e.oldLanes+
        (N*e.oldHosts)*chunks e.oldGroups (e.lanes*e.blocks)+1) :=by
    simpa only [Nat.mul_one,Nat.mul_assoc,MaterialExtent.sourceRows] using add (add (add (left _ book) (left N old)) (left N repack)) (constant one 1)
  have ov : phaseCost overlap*w≤(2048*((4*U*e.blocks+3)+N+N+1))*R*(ratio*h) :=
    honest.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (ratio*h) (left 2048 raw))
  have count : DepotRAM.Material.Sheets.count q.depot=N:= by
    change 15*(q.depot.blocks*(q.depot.cap*11))=15*((q.depot.blocks*q.depot.cap)*11)
    rw [Nat.mul_assoc q.depot.blocks]
  rw [count] at ordinary
  have normal:=Nat.mul_le_mul ordinary machine
  change phaseCost ((PriorHeader.phase e.oldHosts e.groups e.lanes D start adj w).seq
    (((((q.materialCharts base w).seq (q.materialJoin base parts reverse w)).seq (q.materialSheets base w)).seq overlap).seq
      (q.materialMaps base w)))*w≤_
  simp only [phaseCost_seq]
  change _≤ materialFactor D e.blocks N U*R*(ratio*h)
  let rest:=phaseCost (PriorHeader.phase e.oldHosts e.groups e.lanes D start adj w)+
    phaseCost (q.materialCharts base w)+phaseCost (q.materialJoin base parts reverse w)+
    phaseCost (q.materialSheets base w)+phaseCost (q.materialMaps base w)
  change rest*w ≤ (priorFactor D + chartFactor D + joinFactor D + sheetFactor N + mapFactor e.blocks (DescentHaloWalkRAM.breadth D))*R*(ratio*h) at normal
  calc
    _ = rest*w+phaseCost overlap*w :=by dsimp only [rest];ring
    _ ≤ _ :=(Nat.add_le_add normal ov).trans_eq (by unfold materialFactor;ring)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
