import OAI.Hierarchy.TaggedWideCalendarOuterCarried
import OAI.Hierarchy.TaggedWideCalendarReceipt
import OAI.Hierarchy.TaggedWidePathRoleCells
import OAI.Hierarchy.TaggedWideCalendarLeaf
import OAI.Hierarchy.ProbeFixedWideNeighborCapacity

namespace OAI
/-! # Physical party bits on both sides of the selected calendar date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
set_option cleanup.letToHave false
attribute [local irreducible] Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "es" => events v.mesh
local notation "start" => v.wideOrigin h width size seed π
local notation "table" => v.widePlacement h width
local notation "ceiling" => (v.privateArena table h width).endAddress v.mesh
local notation "stock" => v.fixedTerminalStock table h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
variable (j : Path slots es start)
open ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
local notation "wire" => WireTelescope.CalendarTape.Prefix.atWidth («slot»:=slots) («events»:=es) («x₀»:=start) («S»:=siteLast h (2^v.W) k+1) (fun {_ _} path => v.wideCursorWidth h width size π seed age budget small path)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans expanse
local notation "cap" c => HistoryRoles.ceiling v.sampler («h»:=h) («W»:=v.W) («k»:=k) («attempts»:=v.wideJobs)
  v.mesh c v.keepLimit (CatalystArchive.fuel v.mesh) width
variable (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)


local notation "records" => v.widePathRoles h width size π seed age budget small expanse late room j unitCost replay measure bounded
local notation "current" => WireTelescope.CalendarTape.Prefix.atCursor (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slots es start es start)
local notation "pin" => v.widePathCells h width size π seed age budget small expanse late room j
  unitCost replay measure bounded
open Tagged.WideStack Tagged.WideStack.Leaf Tagged.WideCalendarSites Tagged.WideControlJoin
open ThreeFlat Routing TaggedShorterBudget TaggedPrune PhysicalTerm
local notation "K" => siteLast h (2^v.W) k+1
local notation "roles" => Public v.sampler h v.W k v.wideJobs
local notation "T" => Fin (((es).length+1)*Fintype.card ((r:roles)×Fin ((cap unitCost) r)))
local notation "tree" => WireTelescope.CalendarTape.Prefix.cursorSlot («slot»:=slots) («events»:=es) («x₀»:=start)
local notation "branch" => WireTelescope.CalendarTape.Prefix.histories (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slots es start es start) j
local notation "place" => timelineFin tree wire pin es current branch
variable {Ex Se Data:Type} [Fintype Ex] [Fintype Se] [Fintype Data] (B:Gate) {L n groups ports lanes m view:ℕ}
    (key:Fin L↪ℕ×ℕ) (out:Fin n→ProtocolRAMEmit.Row)
    (live:Fin n→Prop) (stage:Fin n→ℕ)
    (bank:∀t,Installed F groups ports lanes width m (key t).2 (atScale live stage (key t).1 out))
    (freeCap:{i:Fin n//¬live i}→ℕ)
    (ord:Pin (banks bank) freeCap T ((Fin groups×Fin ports)×Fin view)≃Data)


open LinearAlgebra.SpectralBooks.SiteTensor
local notation "degree" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "socket" => shelfSlot («h»:=h) («W»:=v.W) («k»:=k) («attempts»:=v.wideJobs) v.sampler
local notation "ends" => sorted v.sampler π.symm v.depth (records).mark ∘ (records).order
local notation "role" => named v.sampler π.symm v.depth (records).mark (records).exclusive (records).order
local notation "addr" => EntryOrder.timePin ord
local notation "bound" => v.wideNeighborCap width unitCost

theorem wide_outer_lane (r : roles) : (cap unitCost) r≤bound := by
  have fit : (cap unitCost) r≤v.wideHistoryUnit unitCost*width :=
    HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit (fuel v.mesh) width r
  have pos : 0<degree := by unfold HistoryRoles.stride; omega
  have enlarge := Nat.le_mul_of_pos_left (v.wideHistoryUnit unitCost*width) pos
  have dyadic := Nat.le_pow_clog («b»:=2) (by decide)
    (degree*v.wideHistoryUnit unitCost*width+1)
  exact fit.trans (enlarge.trans ((by rw [Nat.mul_assoc]; omega :
    degree*(v.wideHistoryUnit unitCost*width)≤degree*v.wideHistoryUnit unitCost*width+1).trans dyadic))

variable (date : Fin (es).length) (after : Bool)
local notation "t" => if after then date.succ else date.castSucc
local notation "qty" => (records).bits t
variable (states : SiteChoices tree wire es current branch) (s : Fin K)
  (port : (bitGraph (rowGraph ends) qty).Port s)
local notation "rowID" => port.1.1.1
local notation "digit" => port.1.1.2
local notation "label" => role (rowID,port.1.2)
local notation "offset" => TaggedShorterCommonScan.earlier (NamedAperture.key ends) qty (rowID).val
  (NamedAperture.key ends rowID)+(digit).val
local notation "slotId" => (⟨HistoryRoles.code v.sampler label,HistoryRoles.code_bound v.sampler label⟩ : Fin degree)
local notation "within" => ((records).fits t rowID port.1.2).trans (v.wide_outer_lane h width unitCost label)
local notation "bitId" => (digit).castLE within
local notation "realState" => cast (congrArg (fun U=>State U s) ((records).atWidth t).symm)
  (datedState tree wire s es current branch t (states s))
variable (a : ∀i,Fin (2^(out i).width)) (ext : Ex→Bool) (sel : Se→Bool) (mem : Memory B.W)
local notation "hist" => placedBits tree wire es current branch place states
local notation "packed" => nativePins («view»:=view) key out live stage bank freeCap a hist
local notation "pins" => CalendarTerms.readPins («B»:=B) ord ext sel (B.terminal mem) packed
local notation "word" => LedgerStep.outerWord («Ex»:=Ex) («Sel»:=Se) («cap»:=bound) B es (cap unitCost) socket addr date s

private theorem atOrderedPin {α β γ : Type*} (ord : α ≃ β) (value : α → γ) (x : α) :
    value (ord.symm (ord x)) = value x := congrArg value (ord.symm_apply_apply x)

omit [Fintype Ex] [Fintype Se] [Fintype Data] in
/-- On either side of a real attempt or feed, the numbered terminal pin for
an original port contains its bit of the party state. Parallel rows use the
prefix of earlier rows on that chord, in the native row order. -/
theorem wide_calendar_outer_bits :
    Sum.elim pins id (word after slotId bitId)=
      (realState (sourcePort ends qty port)).val.testBit offset := by
  have timed (z : T) : (packed ∘ ord.symm) (addr z)=hist z := by
    exact atOrderedPin ord packed (.inr (.inr (.inl z)))
  have atSite : name (site v.sampler label)=s := by
    apply (named_site v.sampler π.symm v.depth (records).mark (records).exclusive (records).order rowID port.1.2).trans
    exact (sourcePort ends qty port).property
  have location : socket label=finProdFinEquiv (s,slotId) := by
    change finProdFinEquiv (name (site v.sampler label),slotId)=_
    exact congrArg (fun vertex : Fin K => finProdFinEquiv (vertex,slotId)) atSite
  exact LedgerStep.outer_original_row tree wire es current branch (cap unitCost) socket pin states
    addr date s after B ext sel (packed ∘ ord.symm) mem ends qty role ((records).fits t)
    ((records).atWidth t)
    (v.wide_path_cells_numbered h width size π seed age budget small expanse late room j unitCost replay measure bounded t)
    timed port slotId location (bitId).isLt

omit [Fintype Ex] [Fintype Se] [Fintype Data] in
/-- The signed substep's old word and its clipping successor's new word
have the same physical interpretation for every intermediate assignment. -/
theorem wide_calendar_substep_outer_bits (mid : Fin (degree*bound)→Bool) :
    let augmented:=Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim (packed ∘ ord.symm) mid) (B.terminal mem)))
    Sum.elim augmented id
      (LedgerStep.substepWord («cap»:=bound) B es (cap unitCost) socket addr date s after after slotId bitId)=
      (realState (sourcePort ends qty port)).val.testBit offset := by
  intro augmented
  exact (LedgerStep.substepWord_outer B es (cap unitCost) socket addr date s ext sel (packed ∘ ord.symm)
    mem mid after slotId bitId).trans
      (v.wide_calendar_outer_bits h width size π seed age budget small expanse late room j unitCost
        replay measure bounded B key out live stage bank freeCap ord date after states s port a ext sel mem)

open PassiveWindow

/-- The public degree-slot chart of the native old or new snapshot uses the
physical site of its original sorted port. -/
theorem wide_calendar_socket (e : Fin (records).count) (b : Bool) :
    (finProdFinEquiv.symm (socket (role (e,b)))).1=(portGraph K).vertex (ends e) b := by
  change (finProdFinEquiv.symm (finProdFinEquiv (_, _))).1=_
  rw [Equiv.symm_apply_apply]
  exact named_site v.sampler π.symm v.depth (records).mark (records).exclusive (records).order e b

theorem wide_outer_quantity (r : Fin (records).count) : qty r≤bound :=
  ((records).fits t r false).trans (v.wide_outer_lane h width unitCost (role (r,false)))

local notation "fitQ" => v.wide_outer_quantity h width size π seed age budget small expanse late room j
  unitCost replay measure bounded date after
local notation "here" => v.wide_calendar_socket h width size π seed age budget small expanse late room j
  unitCost replay measure bounded
local notation "localSlot" => PacketNeighbor.localSlot ends qty role socket here s
local notation "chosenDate" => (records).atWidth t

omit [Fintype Ex] [Fintype Se] [Fintype Data] in
/-- The complete occupied role slots read the original carried state of the
selected calendar, at the actual base of the corresponding parallel row. -/
theorem wide_calendar_outer_carried_bits {total : Widths K} (target : installedWidths ends qty=total) :
    let parts:=carried ends qty s fitQ localSlot target
    let original:=cast (congrArg (fun U=>State U s) ((chosenDate).symm.trans target))
      (datedState tree wire s es current branch t (states s))
    ∀slot p,parts.owner slot=some p→∀u : Fin (parts.width slot),
      Sum.elim pins id (word after slot (u.castLE (parts.within slot)))=
        (original p).val.testBit (parts.base slot+u.val) := by
  apply LedgerStep.outer_carried_read tree wire es current branch (cap unitCost) socket pin states addr
    date s after B ext sel (packed ∘ ord.symm) mem ends qty role ((records).fits t) fitQ here chosenDate
    (v.wide_path_cells_numbered h width size π seed age budget small expanse late room j
      unitCost replay measure bounded t) target
  intro z
  exact atOrderedPin ord packed (.inr (.inr (.inl z)))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
