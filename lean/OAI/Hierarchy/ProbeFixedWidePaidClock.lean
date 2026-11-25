import OAI.Hierarchy.ProbeFixedWidePaidWork
import OAI.Hierarchy.ProtocolRAMCalendarSliceCounts
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix

namespace OAI
/-! # Uniform native text and clock for the five charged width sources -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "C" => v.wideSignedChart h width stock


def wideSliceLength := (events v.mesh).length*max 4 (FeedLayout.lanes (publicStages v.W) k)

def wideSliceFactor := max (Classical.choose v.wideArena) (CatalystArchive.slotFactor D k)

private theorem header_rows (hdr : PortHeader) : hdr.count≤hdr.stop := by
  have enough:=ProtocolRAMPurchaseSampler.lt_span (2*hdr.count)
  change hdr.count≤hdr.parity.base+ProtocolRAMPurchaseSampler.span (2*hdr.count)
  omega

theorem wide_paid_shape (bits : ℕ) (budget : v.keepLimit*width+1≤2^h) :
    let ss:=v.widePaidSlices h width bits
    ss.length≤v.wideSliceLength ∧ (∀t∈ss,t.count≤v.wideSliceFactor*2^h) ∧
      (ss.map PaidWidths.Slice.count).sum≤(v.wideSliceLength*v.wideSliceFactor)*2^h := by
  intro ss
  let fmt:=v.nativeFormats P h width
  let layout:=FeedLayout.atEvent («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let feeds:=feedColumns («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let recipe:=routeBanks start cnt r
  let sink:=(P).catalogue.sink r banks src tab dst owners
  let compile:=v.wideEventSlices h width bits
  let branches:=max 4 (FeedLayout.lanes (publicStages v.W) k)
  let volume:=v.wideSliceFactor*2^h
  have arena : (A).first≤volume := (Nat.le_add_right ..).trans
    ((Classical.choose_spec v.wideArena h width budget).trans (Nat.mul_le_mul_right _ (le_max_left ..)))
  have slots : r≤volume := (slot_count h D k (Nat.two_pow_pos _)).trans (Nat.mul_le_mul_right _ (le_max_right ..))
  have event (e : Event) (he : e∈events v.mesh) : (compile e).length≤branches ∧ ∀t∈compile e,t.count≤volume := by
    cases e with
    | attempt a =>
      obtain ⟨⟨_,_,occ,low⟩,⟨_,_,paths,top⟩⟩:=v.paid_economic_headers P h width a he
      have walked:=early_positions_le_card recipe route v.sampler v.wideJobs order
        (v.catalystPairOwners P h width) (v.catalystPairParity P h width)
      have shape:=(fmt a).paid_shape sink (P).catalogue.idBase (StripChart.header F s a).fieldTerm (StripChart.id F s (P).catalogue a)
        (v.nativeTrees P h width a) (v.paidSpillPath P h width recipe route order a) bits volume
        (occ.le.trans ((header_rows _).trans (low.trans arena))) (paths.le.trans ((header_rows _).trans (top.trans arena)))
        (walked.trans slots)
      exact ⟨shape.1.trans (le_max_left ..),shape.2⟩
    | feed b =>
      constructor
      · change ((feeds b).map _).length≤branches
        simp only [List.length_map,feeds,feedColumns,FeedLayout.columns,List.length_finRange]
        have stage : N = publicStages v.W := fixed_stage_count h v.W
        rw [stage]
        exact le_max_right ..
      · intro t ht
        obtain ⟨c,_,rfl⟩:=List.mem_map.mp ht
        exact (boundary_positions_le_card route v.sampler v.wideJobs (layout b) (v.catalystPairOwners P h width)
          (v.catalystPairParity P h width) c).trans slots
  have len : ss.length≤v.wideSliceLength := sparse_length (events v.mesh) compile branches (fun e he=>(event e he).1)
  have individual (t) (ht : t∈ss) : t.count≤volume := by
    obtain ⟨e,he,printed⟩:=List.mem_flatMap.mp ht
    exact (event e he).2 t printed
  refine ⟨len,individual,(sparse_count ss volume individual).trans ?_⟩
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right volume len

def widePaidClockFactor (bits : ℕ) :=
  8+6*v.rowFactor+7*v.wideSliceLength+v.wideSliceLength*v.wideSliceFactor*(4*v.wideIssueCost bits+20)

theorem wide_paid_clock (bits : ℕ) (budget : v.keepLimit*width+1≤2^h) :
    let ss:=v.widePaidSlices h width bits
    PaidWidths.clock (banks).width (P).catalogue.rows ss≤v.widePaidClockFactor bits*2^h ∧
      (ss.map (fun t=>rowText (RepairHistogram.pair (t.columns (banks).width (P).catalogue.rows))+22)).sum≤
        v.wideSliceLength*(33+4*v.wideIssueCost bits) := by
  intro ss
  have bill:=v.wide_paid_invoice h width bits
  have shape:=v.wide_paid_shape h width bits budget
  have pos:=Nat.two_pow_pos h
  have original:=v.wideCatalogueRows h width
  have paid:=Nat.mul_le_mul_right (4*v.wideIssueCost bits+20) shape.2.2
  have staticCount:=Nat.le_mul_of_pos_right v.wideSliceLength pos
  constructor
  · apply bill.1.trans
    calc
      _≤8*2^h+6*(v.rowFactor*2^h)+7*(v.wideSliceLength*2^h)+
        ((v.wideSliceLength*v.wideSliceFactor)*2^h)*(4*v.wideIssueCost bits+20) := by
        have eight:=Nat.mul_le_mul_left 8 pos
        nlinarith only [eight,original,shape.1.trans staticCount,paid]
      _=_ := by unfold widePaidClockFactor;ring
  · exact bill.2.trans (Nat.mul_le_mul_right _ shape.1)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
