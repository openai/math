import OAI.Hierarchy.ProtocolRAMCalendarStockActual
import OAI.Hierarchy.ProtocolRAMCalendarStockTrials
import OAI.Hierarchy.ProtocolRAMCalendarStripOrigin
import OAI.Hierarchy.ProtocolRAMCalendarEconomicPrices
import OAI.Hierarchy.ProtocolRAMCalendarThresholdFit

namespace OAI
/-! # The true zero reserve, stock pointers and signed threshold of the strip chart -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StockBound
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe PurchaseFrozen PurchaseCT
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z d k N letters depth w phases digits ports : ℕ}

/-- Recover both empty commodity banks from the authentic price header and the
padded all-selector readback of the initial reserve. -/
theorem boot_zeros (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (m : Memory w) (empty : Bank)
    (active : InitialPrices b z N k phase (fun _=>0) m) (zero : ∀r : Word w,empty.read m r=0)
    (goods : PurchaseInventory.footprint z N k≤ empty.size) (fit : PurchaseInventory.footprint z N k≤2^w) :
    (∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock b.initial m i=0) ∧
    ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock empty.base m i=0 := by
  refine ⟨active.empty,?_⟩
  intro i
  have cell := PurchaseInventory.slot_lt i
  have read := congrArg Fin.val (zero (PurchaseInventory.slot i:Word w))
  simpa only [PurchaseInventory.stock,Bank.read,Fin.val_cast_of_lt (cell.trans_le fit),Nat.mod_eq_of_lt (cell.trans_le goods),Fin.val_zero] using read

/-- Read the original public division-by-two table after subdivision and native
market initialization. The fixture outside the division interval is arbitrary. -/
theorem boot_half {jobs : ℕ} (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest fixture : Boot.Tape z d)
    (markets : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout markets size)
    (hd : 1≤ d) (first : 2^z≤ b.initial) (heap : Native.heapEnd z d Native.copies≤ b.initial)
    (fits : JointHeader.stop b z N k phases≤ size) (before : ∀i,JointHeader.stop b z N k phases≤ Boot.low (markets i)) :
    let table:=JointHeader.half b z N k
    let m:=Boot.booted markets size (JointHeader.words b z d N k phase π stock rest)
    ∀x,table.base≤ x → x< table.base+table.size → m x=FeedROM.halfAdvice table fixture x := by
  intro table m x lo hi
  have low : b.initial≤ table.base := by
    change b.initial ≤ b.initial+GlobalTests.rows z N k+_
    omega
  have kept := JointHeader.low_origin b phase π stock rest markets layout hd first fits before x (heap.trans (low.trans lo)) hi
  have inside : table.base≤ x ∧ x< table.base+table.size := ⟨lo,hi⟩
  change m x=FeedROM.halfAdvice table _ x at kept
  rw [kept]
  simp only [FeedROM.halfAdvice,fillSegment,ite_eq_left inside]

/-- Both zeros at the same booted memory used by the priced calendar, even
with the inverse core-route catalogue mounted inside the public ports. -/
theorem economic_zeros {X Y steps jobs : ℕ} (H : StripChart.EconomicHeader phases X Y steps) (ord : H.Ordered)
    (p : MenuROM.Charges) (placed : p.payload.base=H.stop) (adjacent : p.purchase.base=p.payload.stop)
    (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (empty : Bank) (atEnd : empty.base=p.stop) (rest : Boot.Tape z d) (markets : Fin jobs→Market z d k)
    {size : ℕ} (layout : Boot.Layout markets size) (hd : 1≤ d) (first : 2^z≤ b.initial)
    (heap : Native.heapEnd z d Native.copies≤ b.initial) («prefix» : Native.heapEnd z d Native.copies≤ H.ports.base)
    (score : JointHeader.stop b z N k phases≤ H.ports.base) (weight : JointHeader.stop b z N k phases≤ size)
    (early : ∀i,JointHeader.stop b z N k phases≤ Boot.low (markets i))
    (within : empty.base+empty.size≤ size) (before : ∀i,empty.base+empty.size≤ Boot.low (markets i))
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤ x→low m x=m x)
    (goods : PurchaseInventory.footprint z N k≤ empty.size) (fit : PurchaseInventory.footprint z N k≤2^Native.wordBits z d Native.copies) :
    let high := H.scalar.words (H.vectorMemory (p.words (StripChart.reserveWords empty rest)))
    let words := JointHeader.words b z d N k phase π (fun _=>0) (H.ports.words (low high))
    let start := Boot.booted markets size words
    (∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock b.initial start i=0) ∧
    ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock empty.base start i=0 := by
  intro high words start
  refine boot_zeros b phase start empty
    (start_prices (N:=N) b phase π (fun _=>0) (H.ports.words (low high)) markets layout hd first heap weight early)
    ?_ goods fit
  intro u
  let x := empty.base + u.val % empty.size
  have lo : empty.base ≤ x := Nat.le_add_right ..
  have hi : x < empty.base + empty.size := Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
  have pastPurchase : p.purchase.stop ≤ x := atEnd.ge.trans lo
  have pastPayload : p.payload.stop ≤ x := adjacent.ge.trans ((Nat.le_add_right ..).trans pastPurchase)
  have pastHeader : H.stop ≤ x := placed.ge.trans ((Nat.le_add_right ..).trans pastPayload)
  have pastScalar : H.scalar.stop ≤ x := by
    have menus := StripChart.EconomicHeader.Ordered.menu_bounds H ord
    obtain ⟨_,hp,hb,hm,_,ht,ht'⟩ := ord
    have payload : H.payload.base ≤ H.payload.stop := Nat.le_add_right ..
    have bought : H.bought.base ≤ H.bought.stop := Nat.le_add_right ..
    have left : H.payloadTree.base ≤ H.payloadTree.stop := Nat.le_add_right ..
    have right : H.boughtTree.base ≤ H.stop := Nat.le_add_right ..
    omega
  have scalar : H.scalar.base ≤ x := (Nat.le_add_right ..).trans pastScalar
  have port : H.ports.stop ≤ x := ord.scalarBase.le.trans scalar
  have base : H.ports.base ≤ x := (Nat.le_add_right ..).trans port
  have authentic := JointHeader.authentic (N:=N) (k:=k) b phase π (fun _=>0) (H.ports.words (low high)) first
  have boot := (Boot.start markets layout hd π words authentic).2
  have keep := boot.kept x («prefix».trans base) (fun i reach=>Nat.not_lt_of_ge reach.1 (hi.trans_le (before i)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le within)] at keep
  change start x=0
  calc
    start x = words x := keep
    _ = H.ports.words (low high) x := JointHeader.tail_words b phase π _ _ x first (score.trans base)
    _ = low high x := H.ports.frame _ x (.inr port)
    _ = high x := above high x scalar
    _ = H.vectorMemory (p.words (StripChart.reserveWords empty rest)) x := H.scalar.frame _ x (.inr pastScalar)
    _ = p.words (StripChart.reserveWords empty rest) x := H.vector_above ord _ x pastHeader
    _ = p.payload.words (StripChart.reserveWords empty rest) x := p.purchase.outside _ (.inr pastPurchase)
    _ = StripChart.reserveWords empty rest x := p.payload.outside _ (.inr pastPayload)
    _ = 0 := StripChart.reserveWords_read empty rest u

local notation "n" => (permutationFabric z d).shapes.length

theorem strip_pointers (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns n) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : StripChart.Boards z d k letters depth)
    (c : Mesh) (A : Arena) (initial : ℕ) (empty : Bank) (a : Attempt) :
    let boards := StripChart.withReserveSource F s c A initial empty
    let f := StripChart.formats F c A initial boards
    let bank := pricedBanks c A f initial empty.base
    (f a).stockSource.old.base=bank.previous c (.attempt a) ∧ (f a).stockSource.reserve.base=bank.reserve (.attempt a) := by
  cases a <;> exact StripChart.source_banks F s c A initial empty _

theorem Bounded.pass {base ceiling : ℕ} {m : Memory w} (h : Bounded z N k base ceiling m) (p : Pass)
    (higher : base+PurchaseInventory.footprint z N k≤ p.out) : Bounded z N k base ceiling (p.apply m) := by
  intro i
  have before := (Nat.add_lt_add_left (PurchaseInventory.slot_lt i) base).trans_le higher
  simpa [PurchaseInventory.stock,Pass.apply,image,fillSegment,not_le.mpr before] using h i

theorem Bounded.prepared {base ceiling q goods : ℕ} {m : Memory w} (h : Bounded z N k base ceiling m)
    (C : Chart w q goods) (a : Attempt) (ran : ready C (.attempt a) m)
    (safe : ∀i : Commodity (Fin (2^z)) N k,protected C (base+PurchaseInventory.slot i) (.attempt a)) :
    Bounded z N k base ceiling (Calendar.prepared C a m) := by
  intro i
  change ((Calendar.prepared C a m) (base+PurchaseInventory.slot i)).val≤ ceiling
  rw [prepared_prior C a m _ ran (safe i)]
  exact h i

/-- Any actual frozen inventory satisfying the chronological ceiling has enough
physical threshold table rows for every tile and sign. -/
theorem threshold (s : StripChart.Boards z d k letters depth) (b : StripDirectory.Boards z d k letters digits ports)
    (header cap width base origin : ℕ) (m : Shelf.Mem z d) (size : width≤2^z)
    (ptr : b.market.shelf.stockBase=origin) (bound : Bounded z (2*rounds d+1) k origin (cap*width) m) :
    let u := StripChart.Slab.forCap header cap
    let sh := (u.localize s b base).market.shelf
    ∀v : Tile z d,∀a : Fin k×Bool,stockBits sh.stockBase k m v a< sh.table.size := by
  apply StripChart.Slab.threshold_reads s b header cap width base m size
  rwa [ptr]

theorem Run.threshold {q goods : ℕ} (C : Chart (Native.wordBits z d Native.copies) q goods)
    (bank : Banks) (start : Shelf.Mem z d) (cap width : ℕ)
    (r : Run C bank start z (CoreBoard.Stages z d) k (cap*width))
    (s : StripChart.Boards z d k letters depth) (b : StripDirectory.Boards z d k letters digits ports)
    (e : Event) (live : e∈events C.mesh) (header base : ℕ) (widthFit : width≤2^z)
    (ptr : b.market.shelf.stockBase=bank.previous C.mesh e) :
    let sh := ((StripChart.Slab.forCap header cap).localize s b base).market.shelf
    ∀v : Tile z d,∀a : Fin k×Bool,stockBits sh.stockBase k (state C start (position C.mesh e)) v a< sh.table.size := by
  have stock := (r.event_inputs e live).1
  have stages : CoreBoard.Stages z d=2*rounds d+1 := template_length ..
  apply StockBound.threshold s b header cap width base (bank.previous C.mesh e) _ widthFit ptr
  rwa [stages] at stock

end Hierarchy.ProtocolRAM.Calendar.StockBound
end

end OAI
