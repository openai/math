import OAI.Hierarchy.ProtocolRAMCatalogueCoreMount
import OAI.Hierarchy.ProtocolRAMCatalystOwnerLedger
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout
import OAI.Hierarchy.ProtocolRAMCoreRouteDirectory
import OAI.Hierarchy.ProtocolRAMPaidCatalogueBoard

namespace OAI
/-! # Checkout geometry at the allocated signed terminal -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.ReportSockets CoreBoard AdaptiveProbe
variable {attempts K w : ℕ}

/-- The original descriptor and the affirmative bought readers of the native
catalogue with its actual permanent row count. -/
abbrev liveCoreMount (d : BoughtSockets.Directory attempts) (S : PurchaseSampler)
    (h W k depth R groups bins height bits idBase : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (place : Site h (2^W) k→Fin K) (order : Fin R≃Edges S h (2^W) k) (m : Memory w) :=
  (liveBoard d S h W k depth R groups bins height bits idBase).coreMount π place order m

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Calendar Calendar.CoreRoute Calendar.CatalogueRows Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe
open scoped Classical Fin.CommRing

variable {c : Mesh} {A : Arena} {L : OwnerLedger} {cat : Board}
  {z W k count n start bits w : ℕ} {stock : Bank}
local notation "r" => Fintype.card (Slots z (2^W) k)
local notation "b" => settlement bits stock
local notation "recipes" => routeBanks start n r
local notation "arch" => reserve start n bits

/-- The geometry loaded at checkout survives the two route passes, the
dated owner scans, paid width accumulation and the final reserve tally. -/
theorem Ready.checkout (room : Ready c A L cat z W k count n start bits w stock)
    (S : PurchaseSampler) (ops : Calendar.CoreRoute.Source) (attempts supply : ℕ)
    {entries : ℕ} (use : Fin entries→Fin count) (debit : Fin entries→ℕ) (slices : List PaidWidths.Slice) (chk : Memory w)
    (fits : ∀u∈slices,u.Fits (b).width cat.rows (source bits) w) :
    let rt:=Calendar.CoreRoute.stages b recipes ops S z W k attempts
    let paid:=PaidWidths.output (b).width cat.rows (source bits) slices chk
    let closed:=ReserveUse.output arch b supply use debit (result rt (result (L.scans c count) paid))
    ∀x,x<A.endAddress c→closed x=chk x := by
  intro rt paid closed
  rcases room.flagLow with ⟨owner,reserved,used,scratch,width,_⟩
  apply checkout_frame b cat.rows (source bits) slices (L.scans c count) rt arch supply use debit chk
    (A.endAddress c) fits width.le
  · intro p hp
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp hp
    exact owner.le.trans (Nat.le_add_right ..)
  · have hkind : (b).width.base≤(b).kind.base := Nat.mul_le_mul_right (2^bits) (by decide : 1≤4)
    have hindex : (b).width.base≤(b).index.base := Nat.mul_le_mul_right (2^bits) (by decide : 1≤5)
    intro p hp
    change p ∈ Calendar.CoreRoute.stages b recipes ops S z W k attempts at hp
    simp only [Calendar.CoreRoute.stages,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · exact width.le.trans hkind
    · exact width.le.trans hindex
  · exact reserved.le
  · exact used.le
  · exact scratch.le

/-- On every acquired catalogue ordinal, the actual terminal serializer reads
the two endpoints and other non-width fields of its original checkout row. -/
theorem Ready.bought_read (room : Ready c A L cat z W k count n start bits w stock)
    (S : PurchaseSampler) (ops : Calendar.CoreRoute.Source) (attempts supply : ℕ)
    {entries : ℕ} (use : Fin entries→Fin count) (debit : Fin entries→ℕ) (slices : List PaidWidths.Slice) (chk : Memory w)
    (fits : ∀u∈slices,u.Fits (b).width cat.rows (source bits) w)
    (geo : ∀f : Fin 7,f≠4→(cat.geometry f).Fits w (A.endAddress c)) (ids : cat.idBase+cat.rows<2^w)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (ord : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (j : Fin cat.boughtRows) :
    let rt:=Calendar.CoreRoute.stages b recipes ops S z W k attempts
    let paid:=PaidWidths.output (b).width cat.rows (source bits) slices chk
    let closed:=ReserveUse.output arch b supply use debit (result rt (result (L.scans c count) paid))
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    Reads (sink.terminalRows closed ord ci cj (cat.boughtIndex j))
      (cat.bought.view chk (j.val:Word w)) (cat.idBase+(cat.boughtIndex j).val) := by
  intro rt paid closed sink
  have wide : 0<w := Nat.lt_trans (by decide : 0<3) room.sink.wide
  exact cat.bought_reads_checkout b (source bits) (table bits) (destination bits) _ chk closed ord ci cj j ids
    (Nat.one_lt_two_pow wide.ne') (fun f keep=>ProtocolRAMGeneratedWrite.fits_mono _ room.flagLow.2.2.2.2.1.le (geo f keep))
    room.sink.width geo (room.checkout S ops attempts supply use debit slices chk fits)

/-- The same native terminal columns expose every unchanged core-row descriptor from checkout. -/
theorem Ready.core_read (room : Ready c A L cat z W k count n start bits w stock)
    (S : PurchaseSampler) (ops : Calendar.CoreRoute.Source) (attempts supply : ℕ)
    {entries : ℕ} (use : Fin entries→Fin count) (debit : Fin entries→ℕ) (slices : List PaidWidths.Slice) (chk : Memory w)
    (fits : ∀u∈slices,u.Fits (b).width cat.rows (source bits) w)
    (geo : ∀f : Fin 7,f≠4→(cat.geometry f).Fits w (A.endAddress c)) (ids : cat.idBase+cat.rows<2^w)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (ord : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (j : Fin cat.coreRows) :
    let rt:=Calendar.CoreRoute.stages b recipes ops S z W k attempts
    let paid:=PaidWidths.output (b).width cat.rows (source bits) slices chk
    let closed:=ReserveUse.output arch b supply use debit (result rt (result (L.scans c count) paid))
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    Reads (sink.terminalRows closed ord ci cj (cat.coreIndex j))
      (cat.core.view chk (j.val:Word w)) (cat.idBase+(cat.coreIndex j).val) := by
  intro rt paid closed sink
  exact cat.core_reads_checkout b (source bits) (table bits) (destination bits) _ chk closed ord ci cj j ids
    (fun f keep=>ProtocolRAMGeneratedWrite.fits_mono _ room.flagLow.2.2.2.2.1.le (geo f keep))
    room.sink.width geo (room.checkout S ops attempts supply use debit slices chk fits)

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
end

end OAI
