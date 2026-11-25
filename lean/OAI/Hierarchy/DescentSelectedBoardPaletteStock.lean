import OAI.Hierarchy.DescentSelectedBoardPaletteBirth
import OAI.Hierarchy.DescentRegisteredBirthRoleToken

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 6000
set_option maxHeartbeats 900000
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "J" => (S).groupCount v.age
local notation "H" => v.area.H
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤v.area.H) (R:Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

variable (B:v.SelectedBoard oldFit R selected m parts)


open DescentOrdinaryBorn DescentOrdinaryPaletteBirth DescentPrimitivePalette
variable (choiceEq : HEq selected v.choice)
local notation "same_" => (atSelected v selected choiceEq).link.donorChart.same
local notation "raw" h:arg g:arg => DepotRAM.chip fmt (A).cap v.profile (G).b (phys).materialFormat.slots (B.material h g)
local notation "pos_" => DescentSharedCableNames.Stage.Positive A
local notation "q₀" j:arg => (⟨(rr).pick (j,0),(A).quantum_positive _ ((rr).picked (j,0))⟩ : pos_)
local notation "seat_" => DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
local notation "bytes" => donorNameBits v.stage.k v.stage.Δ

local notation "dateRows" => BitDescription.scannedRows v.nonnegative v.stage
local notation "dateSeed" i:arg =>
  (⟨(dateRows).pick (i,0),(A).quantum_positive _ ((dateRows).picked (i,0))⟩ : pos_)
local notation "L" => v.paletteShape
local notation "tok" => token G v.palette.seedWidth v.palette.grainLimit v.palette.rotor
variable (floor : ℕ) (entry : ArgumentEntry v) («matching» : entry.Match v floor)
    (birth : entry.BirthShape v)
    (parts₀ : Fin entry.clip.venue.hosts→Fin entry.clip.venue.groups→DepotRAM.Parts entry.clip.venue.socket)
    (socket : entry.clip.venue.socket=v.ticket.depotShape v.short) (profileEq : entry.clip.venue.profile=v.profile)
    (slotsEq : entry.clip.venue.slots=v.withIssuedSigned.materialFormat.slots)
    (blocks : v.bornBook.blocks= (v.ticket.depotShape v.short).blocks) (cap : v.bornBook.cap= (v.ticket.depotShape v.short).cap)
    (names : v.bornBook.names= (v.ticket.depotShape v.short).names) (widths : v.bornBook.widths= (v.ticket.depotShape v.short).widths)
    (past : Fin v.paletteShape.blocks→Fin v.paletteShape.hosts→Fin v.paletteShape.oldGroups→Cell (v.paletteShape.primitiveBits*v.paletteShape.oldNodes))
    (hostGrid : v.paletteShape.hosts=v.bornBook.hosts) (groupGrid : v.paletteShape.oldGroups=v.bornBook.groups)
    (origin : Fin v.paletteShape.blocks→Fin v.paletteShape.successors→Fin v.paletteShape.groups→Cell (v.paletteShape.originBits*v.paletteShape.newNodes))
    (next : Fin v.paletteShape.hosts→Fin v.paletteShape.ports→Option (Fin v.paletteShape.hosts))
local notation "stock" => v.paletteStock floor entry «matching» past (entry.nativeChips v birth parts₀) hostGrid groupGrid origin next
local notation "homeSite" i:arg => v.world.graph.src ((dateRows).pick (i,0))
local notation "site_" i:arg => ((A).block (homeSite i)).cast (blocks.symm.trans «matching».newBlocks)
local notation "slot_" i:arg => (seat_ (dateSeed i)).cast (cap.symm.trans «matching».newCap)

/-- The retained board as an argument-entry grid, with the host and group
inclusions used by the public coordinate chart. -/
def SelectedBoard.palette_parts (hMap : Fin entry.clip.venue.hosts→Fin H)
    (gMap : Fin entry.clip.venue.groups→Fin J) :
    Fin entry.clip.venue.hosts→Fin entry.clip.venue.groups→DepotRAM.Parts entry.clip.venue.socket :=
  fun h g=>cast (congrArg DepotRAM.Parts socket.symm) (B.material (hMap h) (gMap g))

theorem SelectedBoard.palette_parts_at (hMap : Fin entry.clip.venue.hosts→Fin H)
    (gMap : Fin entry.clip.venue.groups→Fin J) (h : Fin entry.clip.venue.hosts) (g : Fin entry.clip.venue.groups)
    (who : Fin H) (cohort : Fin J) (atHost : hMap h=who) (atGroup : gMap g=cohort) :
    HEq (SelectedBoard.palette_parts v oldFit R selected m parts B entry socket hMap gMap h g)
      (B.material who cohort) :=by
  subst who;subst cohort
  exact cast_heq _ _

include choiceEq socket profileEq slotsEq names widths in
/-- At the actual paired original source, the newborn primitive field holds the
precise coefficient token for this party and the dated ballot. -/
theorem SelectedBoard.registered_palette_birth
    (scale : v.bornBook.scale=v.stage.z) (under : v.stage.z≤v.palette.grainLimit)
    (i : (dateRows).pairs) (party : Fin 6) (h : Fin v.paletteShape.hosts) (g : Fin v.paletteShape.oldGroups)
    (mounted : let u:=homeSite i
      HEq (parts₀ ((h.cast hostGrid).cast birth.hosts) ((g.cast groupGrid).cast birth.groups))
        (B.material (hosts ((A).pos u).2) ((A).pos u).1)) :
    (stock).newborn ((L).bornIndex (site_ i) (slot_ i) party) h g=
      tok (bornLabel (s:=v.palette.seedWidth) v.palette.rotor (c:=v.choice) under i party) :=by
  have achieved:=SelectedBoard.native_palette_party v oldFit R selected m parts B choiceEq entry birth parts₀
    socket profileEq slotsEq blocks cap names widths v.palette.seedWidth v.palette.grainLimit v.palette.rotor under
    i party (h.cast hostGrid) (g.cast groupGrid) mounted
  have achievedRow:=palette_birth_at v floor entry «matching» past (entry.nativeChips v birth parts₀)
    hostGrid groupGrid origin next (site_ i) (slot_ i) party h g
  rw [scale] at achievedRow
  exact achievedRow.trans achieved

include choiceEq socket profileEq slotsEq names widths in
/-- On the original selected board, matching the two physical coordinates
suffices for the emitted palette field. -/
theorem SelectedBoard.registered_material_birth
    (hMap : Fin entry.clip.venue.hosts→Fin H) (gMap : Fin entry.clip.venue.groups→Fin J)
    (scale : v.bornBook.scale=v.stage.z) (under : v.stage.z≤v.palette.grainLimit)
    (i : (dateRows).pairs) (party : Fin 6) (h : Fin v.paletteShape.hosts) (g : Fin v.paletteShape.oldGroups)
    (atHost : hMap ((h.cast hostGrid).cast birth.hosts)=hosts ((A).pos (homeSite i)).2)
    (atGroup : gMap ((g.cast groupGrid).cast birth.groups)=((A).pos (homeSite i)).1) :
    let cells:=SelectedBoard.palette_parts v oldFit R selected m parts B entry socket hMap gMap
    let book:=v.paletteStock floor entry «matching» past (entry.nativeChips v birth cells) hostGrid groupGrid origin next
    book.newborn ((L).bornIndex (site_ i) (slot_ i) party) h g=
      tok (bornLabel (s:=v.palette.seedWidth) v.palette.rotor (c:=v.choice) under i party) :=by
  apply SelectedBoard.registered_palette_birth (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (choiceEq:=choiceEq) (floor:=floor) (entry:=entry) («matching»:=«matching»)
    (birth:=birth) (parts₀:=SelectedBoard.palette_parts v oldFit R selected m parts B entry socket hMap gMap)
    (past:=past) (hostGrid:=hostGrid) (groupGrid:=groupGrid) (origin:=origin) (next:=next)
    (socket:=socket) (profileEq:=profileEq) (slotsEq:=slotsEq) (blocks:=blocks) (cap:=cap)
    (names:=names) (widths:=widths) (scale:=scale) (under:=under) (i:=i) (party:=party) (h:=h) (g:=g)
  exact SelectedBoard.palette_parts_at v oldFit R selected m parts B entry socket hMap gMap _ _ _ _ atHost atGroup

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
