import OAI.Hierarchy.TaggedWideInstalledFloors
import OAI.Hierarchy.TaggedWideTerminalROM
import OAI.Hierarchy.TaggedWideInverseAccepted

namespace OAI
/-! # Purchased-window ROM reads from the original signed tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute HistoryRoles Tagged WireTelescope
open Computability.VPVNP.RAMMemory Tagged.WideControlJoin StripChart CatalystArchive ReportSockets
open ProtocolRAMFrozenWindow ProtocolRAMSupergroupDirectory ProtocolRAMPackedRanked
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) {κ A : ℝ} (x : WideParent κ A)
set_option quotPrecheck false
set_option maxRecDepth 16384
set_option maxHeartbeats 3500000
local notation "P" => v.widePlacement x.h x.w
local notation "D" => 2^v.W
local notation "W" => Native.wordBits x.h D Native.copies
local notation "root" => v.wideInstalledRoot x
local notation "bits" => v.maxBits
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "es" => events v.mesh

/-- All selector cells lie strictly below the first installed ROM address. -/
theorem wide_selector_header_installed (age : v.wideStockHeight≤x.h)
    (budget : v.keepLimit*x.w+1≤2^x.h) (small : x.w≤2^x.h)
    (word : Bits (CalendarTape.bits (v.wideSelector x.h x.w age budget small).format.slot es))
    (highSeed : Memory W) (j : ℕ) (above : root≤j) :
    (v.wideSelector x.h x.w age budget small).format.windows.header es word highSeed j=highSeed j := by
  let reader:=v.wideSelector x.h x.w age budget small
  let arena:=v.privateArena P x.h x.w
  let boards:=v.nativeBoards P x.h x.w
  apply (reader.header_frame es word highSeed j ?_).symm
  rintro ⟨e,active,lo,hi⟩
  have cutoff : arena.endAddress v.mesh≤j:=
    (v.wide_funded_extent x.h x.w bits).trans ((v.wide_funded_le_installed_root x).trans above)
  cases e with
  | feed a => have h : j<0:=hi; omega
  | attempt a =>
    have fit : reader.format.windows.cells (.attempt a)≤Slab.selectorSpan boards:=reader.fits a
    have allocated : Slab.selectorSpan boards≤arena.stride:=by
      change Slab.selectorSpan boards≤Slab.stride (v.slab (v.seed P x.h x.w) P x.w) boards
      simp only [Slab.stride,PostLayout.column,PostLayout.startColumns,Slab.mask,Slab.flags,Slab.first,
        Nat.zero_add,Nat.add_assoc]
      exact Nat.le_add_right ..
    have last:=arena.within v.mesh (.attempt a) active
    change j<arena.base v.mesh (.attempt a)+reader.format.windows.cells (.attempt a) at hi
    omega

variable (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (dated : WideCPU.Dated (events v.mesh).length)
  (sites : dated.siteDirectorySize=SiteDirectory.size x.h (2^v.W) k)
  (edges : dated.rawEdges=(v.widePlacement x.h x.w).catalogue.rows)
local notation "cap" => v.wideInstalledCap unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost dated
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "gROM" => v.wideGroupROM x dated bits root
local notation "layerROM" => v.wideLayersROM x dated bits root
local notation "fmtROM" => v.wideFormatROM x dated bits root
local notation "header" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated sites edges
local notation "terminal" => v.wideTerminalWords x.h x.w bits (dated.romEnd root) (dated.workEnd S)
local notation "words" => v.wideWindowWords x m ell short u δ ξ cap dated bits root

/-- The three immutable inputs of the priced program are cuts of one installed image.
The interval starts at the first headroom cell left by the counted prefix. -/
theorem wide_funded_rom_reads (raw before : Memory W)
    (keep : ∀j,root≤j→j<S→before j=header raw j) :
    let installed := terminal (v.wideTerminalPreimage x dated sites edges raw)
    (∀j,gROM≤j→j<gROM+2*span (dir).groups→before j=words installed j) ∧
    (∀j,(l).layers.base≤j→j<(l).layers.base+(l).layers.size→before j=words installed j) ∧
    (∀t j,((l).windows t).rom≤j→j<((l).windows t).adviceEnd→before j=words installed j) := by
  intro installed
  change ∀j,root≤j→j<S→before j=words installed j at keep
  have grouped : root≤gROM:=by
    unfold wideGroupROM
    simp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,
      WideCPU.endOf,WideCPU.Dated.firstROM,WideCPU.Dated.siteROM]
    omega
  have beforeLayers : gROM≤layerROM:=Nat.le_add_right ..
  have beforeFormats : layerROM≤fmtROM:=Nat.le_add_right ..
  have beforeEnd : fmtROM≤S:=Nat.le_add_right ..
  refine ⟨?_,?_,?_⟩
  · intro j lo hi
    exact keep j (grouped.trans lo) (hi.trans_le (beforeFormats.trans beforeEnd))
  · intro j lo hi
    change layerROM≤j at lo
    change j<fmtROM at hi
    exact keep j (grouped.trans (beforeLayers.trans lo)) (hi.trans_le beforeEnd)
  · intro t j lo hi
    change fmtROM+t.val*v.wideWindowStride x ell cap≤j at lo
    exact keep j (grouped.trans (beforeLayers.trans (beforeFormats.trans (by omega))))
      (hi.trans_le (v.wideWindow_rom_bound x m ell short u δ ξ cap fmtROM t))


/-- The counted archive supplies the original dated mask and site tables and the
following terminal geometry directly to the issuers. -/
theorem wide_funded_issuer_rom (highRaw archive : Memory W)
    (keep : ∀j,root≤j→j<S→archive j=header highRaw j) :
    let pre:=v.wideTerminalPreimage x dated sites edges highRaw
    (∀j,root≤j→j<dated.romEnd root→archive j=pre j) ∧
    (∀j,dated.romEnd root≤j→
      j<v.wideTerminalROMEnd x.h x.w bits (dated.romEnd root) (dated.workEnd S)→
      archive j=terminal pre j) := by
  intro pre
  have first : root≤dated.romEnd root:=by
    simp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,
      WideCPU.endOf,WideCPU.Dated.firstROM,WideCPU.Dated.siteROM]
    omega
  have start : dated.romEnd root≤v.wideTerminalROMEnd x.h x.w bits (dated.romEnd root) (dated.workEnd S):=by
    unfold wideTerminalROMEnd ProtocolRAMTurnWindow.Layout.readOnlyEnd
      ProtocolRAMTurnWindow.Layout.halfBase ProtocolRAMTurnWindow.Layout.directoryBase
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have endGroup : gROM≤S:=by
    unfold wideInstalledSize wideFormatEnd wideFormatROM wideLayersROM
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have beforeSize:=(v.wide_terminal_before_groups x dated bits root (dated.workEnd S)).trans endGroup
  have mounted (j : ℕ) (lo : root≤j)
      (hi : j<v.wideTerminalROMEnd x.h x.w bits (dated.romEnd root) (dated.workEnd S)) :
      archive j=terminal pre j :=
    (keep j lo (hi.trans_le beforeSize)).trans
      (v.wideInstalledHeader_terminal x m ell short u δ ξ unitCost dated sites edges highRaw j hi)
  constructor
  · intro j lo hi
    exact (mounted j lo (hi.trans_le start)).trans
      ((v.wideTurnWindow x.h x.w bits (dated.workEnd S)).outside _ _ _ pre j (Or.inl hi))
  · intro j lo hi
    exact mounted j (first.trans lo) hi

/-- Specialize the archive's physical high-memory frame to the original inverse tag and
the actual installed image. Its second projection is the immutable interval of the
counted program's own output. -/
abbrev wide_inverse_installed_rom (highRaw : Memory W)
    (age : v.wideStockHeight≤x.h) (budget : v.keepLimit*x.w+1≤2^x.h) (small : x.w≤2^x.h)
    {E : Type} (label : Row x.h×Fin x.h→E) (ready : CountedReady v x.h x.w bits)
    (room : S+2*(2^x.h)<2^W) (e : E→Bool)
    (word : Bits (CalendarTape.bits (v.wideSelector x.h x.w age budget small).format.slot es))
    (π : Equiv.Perm (Row x.h)) (auth : ∀i,CalendarTape.WordSlots.exposed label e i=π i)
    (found : let slot:=(v.wideSelector x.h x.w age budget small).format.slot
      let stock:=v.fixedTerminalStock P x.h x.w
      let origin:=v.wideSignedMidAt x.h x.w S stock v.radius π.symm (wideRouteOrder x.h D k)
        (v.wideFundedRaw x.h x.w bits (header highRaw))
      ∃! j : CalendarTape.Path slot es origin,CalendarTape.encode slot es origin j=word) :=
  let limits:=v.wide_installed_tape_bounds x m ell unitCost dated
  let checked:=v.wide_inverse_accepted x.h x.w age budget small S (header highRaw) label ready
    limits.2.2 (limits.1.trans (limits.2.1.trans limits.2.2)) room e word π auth found
  And.intro checked (fun (j : ℕ) (lo : root≤j) (hi : j<S)=>
    (checked.1.2.2 j lo hi).trans (v.wide_selector_header_installed x age budget small word
      (header highRaw) j lo))

/-- Transport the counted receipt through the dated and terminal run. The only
frame needed from that run is its public low-address conclusion. -/
abbrev wide_funded_local_rom (highRaw archive out : Memory W)
    (high : ∀j,root≤j→j<S→archive j=header highRaw j)
    (localRun : ∀j,j<S → out j=archive j) :=
  v.wide_funded_rom_reads x m ell short u δ ξ unitCost dated sites edges highRaw out
    (fun j lo hi=>(localRun j hi).trans (high j lo hi))


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
