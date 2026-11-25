import OAI.Hierarchy.ProbeFixedBroadcastDate
import OAI.Hierarchy.ProbeFixedBroadcastOrigin
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedWideStockLayout

namespace OAI
/-! # Word bounds on the actual selector charge written by every signed attempt -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows StockCommit StockBound Filter
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "rows" => declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "C" => v.wideSignedChart h width stock
local notation "fm" => v.nativeFormats P h width

def BroadcastBounds (a : Attempt) (m : Memory w) : Prop :=
  let f:=fm a
  f.occurrences≤2^w ∧ v.maxBits<2^w ∧ f.board.batch.copies<2^w ∧
  (∀ i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≤v.maxBits) ∧
  ∀ i : Fin f.pricedArea.rows,f.board.batch.copies*(m (f.pricedArea.broadcast+i.val)).val<2^w

/-- The five numerical inputs to the native repair invoice hold in both memories
on every original signed tape, independent of the address word used for the packet. -/
theorem wide_broadcast_bits (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
    (height : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (bits : v.maxBits≤h) (a : Attempt) (scheduled : Event.attempt a∈events v.mesh) :
    let init:=v.wideSignedMidAt h width size stock M π order raw
    v.BroadcastBounds h width a (run C (events v.mesh) init) ∧
    v.BroadcastBounds h width a (v.wideSignedCheckoutAt h width size stock M π order raw) := by
  intro init
  have sizes:=v.wide_stock_sizes h width height budget small
  have runStock:=v.wide_stock_at h width size extent M π raw height budget small
  obtain ⟨before,tail,split⟩:=List.append_of_mem scheduled
  let entry:=run C before init
  have cut:=slot_of_split C init (.attempt a) before tail entry split rfl runStock.mounted_all
  have layout:=(v.wide_stock_layout h width size extent M π raw sizes.words budget
    sizes.width sizes.alphabet sizes.rowsMass sizes.roles a scheduled).1
  obtain ⟨left,right⟩:=v.wide_broadcast_origin h width size extent stock M π order raw
  have recorded:=v.broadcast_date P h width r banks src tab dst owners a init entry before tail
    cut layout sizes.strip small left right
  let f:=fm a
  let x:=f.pricedArea
  have occ : f.occurrences≤x.stop := by
    change x.occurrences≤x.stop
    unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast
    omega
  have room:=sizes.words.addresses
  have fit:=occ.trans ((v.attempt_room P h width a).trans (((A).within v.mesh _ scheduled).trans room.le))
  have copies : f.board.batch.copies≤2^h :=
    (v.ordinary_dimensions P h width a).2.le.trans ((Nat.div_le_self ..).trans small)
  have copyWord:(2^h:ℕ)<2^w:=v.date_prefix_fit h
  have cap : v.maxBits<2^w:=bits.trans_lt ((Nat.lt_two_pow_self (n:=h)).trans copyWord)
  have product:=GlobalTests.linear_room h D v.maxBits bits
  have pack (m : Memory w) (read : ∀i : Fin x.rows,(m (x.broadcast+i.val)).val≤v.maxBits) :
      v.BroadcastBounds h width a m :=
    ⟨fit,cap,copies.trans_lt copyWord,read,fun i=>(Nat.mul_le_mul copies (read i)).trans_lt product⟩
  exact ⟨pack _ (fun i=>(recorded i).1),pack _ (fun i=>(recorded i).2)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
