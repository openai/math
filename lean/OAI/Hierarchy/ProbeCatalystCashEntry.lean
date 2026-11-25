import OAI.Hierarchy.ProtocolRAMCatalystLiveOwners
import OAI.Hierarchy.ProbeCatalystStripInput
import OAI.Hierarchy.ProbeStripGeometryFormats
import OAI.Hierarchy.ProtocolRAMStockStageFrame
import OAI.Hierarchy.ProbeCatalystPortSupport
import OAI.Hierarchy.ProbeCatalystPlacedDebit
import OAI.Hierarchy.ProtocolRAMCatalystArchiveChronology

namespace OAI
/-! # The external catalyst archive reads the second physical signed-cash column -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d count payload K : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "req" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap

variable {e : Role C H (A⊕B) k → Chord sites}

namespace StripInput
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}
  (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)

def raw := nativeStrip (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) (z:=z) (d:=d) (q:=q) menu x.addr x.active x.board x.prior
def slots := nativeSlot (B:=B) (C:=C) (H:=H) (k:=k) x.addr x.active
def form := PortPadding.format D x.start x.slots x.raw
def ballot := enabledBatch x.raw.market.layout x.form.board
def plan := PortPadding.occurrencePlan x.raw x.start x.slots x.mem x.loaded x.portFit x.termFit x.copyFit x.sumFit
def picked (j : Fin x.raw.market.rows) := menuIndex menu.index (x.ballot.packet.eval x.mem (j.val:Word w)).val
def nominal (j : Fin x.raw.market.rows) := (x.picked j).elim 1 (fun i=>(menu.packet i).width)
def rate (j : Fin x.raw.market.rows) := (x.picked j).elim 0 (fun i=>cashRate M (menu.packet i).width)

omit [Nonempty (Fin k)] in
/-- The one-indexed recommended word recovers the original heterogeneous
packet width and its effective catalyst rate in this committed row. -/
theorem frozen_rate (j : Fin x.raw.market.rows) (i : menu.index)
    (hit : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1) :
    x.nominal j=(menu.packet i).width ∧ x.rate j=cashRate M (menu.packet i).width := by
  have pick : x.picked j=some i := by rw [picked,hit,menuIndex_code]
  simp [nominal,rate,pick]

omit [Nonempty (Fin k)] in
theorem rate_le (j : Fin x.raw.market.rows) : x.rate j≤x.nominal j := by
  unfold rate nominal
  cases x.picked j with
  | none => exact Nat.zero_le 1
  | some i => exact cashRate_le M _

/-- The physical stock address bound is needed only on an ordinary field of
a live original record. A true geometric read suffices for that bound. -/
def Addresses := ∀ j,j∈liveRows x.ballot x.mem x.raw.market.rows →
  ∀ a,(x.addr a |>.eval x.mem (j.val:Word w)).val<x.raw.coordinates

omit [Nonempty (Fin k)] in
theorem actual (addr : x.Addresses) (j : Fin x.raw.market.rows)
    (live : j∈liveRows x.ballot x.mem x.raw.market.rows) (v : Roles) :
    cashWord x.plan (j,PortPadding.inject x.ports (Fintype.equivFin Roles v))=
      released v (x.ballot.copies*x.rate j) :=
  strip_realRead menu x.addr x.active x.board x.prior x.start x.ports x.mem x.loaded x.portFit x.termFit
    x.copyFit x.sumFit x.codeFit x.maximum x.fieldFit x.wide x.bankFit j live (addr j live) v

omit [Nonempty (Fin k)] in
theorem padding (j : Fin x.raw.market.rows) (i : Fin D) (tail : Fintype.card Roles≤ i.val) :
    cashWord x.plan (j,i)=0 :=
  placed_pad x.raw x.start x.slots x.mem x.loaded x.portFit x.termFit x.copyFit x.sumFit x.ports x.fieldFit j i tail

omit [Nonempty (Fin k)] in
/-- Both catalogues share this copy count. Each selected entry retains
its own width in the bound, without identifying the two term alphabets. -/
theorem nominal_copies {J : Type*} [Fintype J] (catalogue : PacketWidths J) (includeMenu : menu.index→J)
    (widths : ∀ i,catalogue.width (includeMenu i)=(menu.packet i).width)
    (multiplicity : x.board.copies=catalogue.copiesAt K payload) (scale : 0<K) (j : Fin x.raw.market.rows) :
    x.ballot.copies≤copied K (x.nominal j) payload := by
  change x.board.copies≤_
  rw [multiplicity]
  unfold nominal
  cases hit : x.picked j with
  | none =>
    have low : 1≤commonWidth catalogue.width := by unfold commonWidth;omega
    change payload / (K * commonWidth catalogue.width) ≤ payload / (K * 1)
    exact Nat.div_le_div_left (Nat.mul_le_mul_left K low) (Nat.mul_pos scale Nat.zero_lt_one)
  | some i =>
    have size : 0<(menu.packet i).width := Nat.zero_lt_of_lt (menu.wide i)
    change catalogue.copiesAt K payload ≤ copied K (menu.packet i).width payload
    simpa only [widths] using (catalogue.copy_bounds (includeMenu i) K payload ((widths i).symm ▸ size) scale).2

end StripInput
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}
  (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D) {R G J : Type*} [Fintype J]
  (ballsAt : R ↪ Fin x.raw.market.rows) (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count)
  (idle : Fin count) (scale : 0<K) (stock : x.Addresses) (catalogue : PacketWidths J) (includeMenu : menu.index→J)
  (widths : ∀ i,catalogue.width (includeMenu i)=(menu.packet i).width)
  (mass : x.board.copies=catalogue.copiesAt K payload)

def cashEntry : Entry count payload :=
  readEntry x.plan ballsAt x.ports columns keys idle scale (fun r=>x.nominal (ballsAt r))
    (fun r=>x.nominal_copies catalogue includeMenu widths mass scale (ballsAt r)) (by
      intro r live c axis
      exact (x.actual stock (ballsAt r) live (.catalyst c axis)).le.trans
        (Nat.mul_le_mul_left _ (x.rate_le (ballsAt r))))

include scale stock catalogue includeMenu widths mass in
omit [Nonempty (Fin k)] in
private theorem cash_slot_le_payload (slot : R × C × Fin k) :
    cashWord x.plan (portCell ballsAt x.ports slot) ≤ payload := by
  obtain ⟨r,c,j⟩ := slot
  by_cases live : ballsAt r ∈ liveRows x.ballot x.mem x.raw.market.rows
  · have priced := x.actual stock (ballsAt r) live (.catalyst c j)
    change cashWord x.plan (portCell ballsAt x.ports (r,c,j)) = x.ballot.copies * x.rate (ballsAt r) at priced
    rw [priced]
    exact (Nat.mul_le_mul_left _ (x.rate_le (ballsAt r))).trans
      (catalyst_bits_le scale (x.nominal_copies catalogue includeMenu widths mass scale (ballsAt r)))
  · have off := x.plan.off (x.plan.enum ⟨ballsAt r,catalystPort x.ports (c,j)⟩)
      (by rw [Equiv.symm_apply_apply]; exact live)
    simp [portCell,cashWord,off.2]

omit [Nonempty (Fin k)] in
theorem cash_entry_positive :
    PositivePorts (fun c j=>(.catalyst c j : Roles)) x.raw.market.rows D
      (cashEntry x ballsAt columns keys idle scale stock catalogue includeMenu widths mass) := by
  exact repair_positive_ports ballsAt x.ports columns keys idle (cashWord x.plan)
    (cash_slot_le_payload x ballsAt scale stock catalogue includeMenu widths mass)

omit [Nonempty (Fin k)] in
/-- Every padded cell of the archive agrees with the literal signed debit,
including inactive material and fields whose actual frozen price is zero. -/
theorem cash_entry_read
    (covered : ∀j,j∈liveRows x.ballot x.mem x.raw.market.rows → ∃r,ballsAt r=j)
    (cell : Fin x.raw.market.rows × Fin D) :
    (cashEntry x ballsAt columns keys idle scale stock catalogue includeMenu widths mass).bits (finProdFinEquiv cell)=
      cashWord x.plan cell := by
  refine repair_bits ballsAt x.ports columns keys idle (cashWord x.plan)
    (cash_slot_le_payload x ballsAt scale stock catalogue includeMenu widths mass) ?_ cell
  intro j hit
  exact positive_cell x.plan ballsAt x.ports covered (fun j=>x.ballot.copies*x.rate j)
    (fun j live=>x.actual stock j live) x.padding j hit

omit [Nonempty (Fin k)] in
/-- At the chronological commit boundary, read the archive ordinal itself
from the negative half of the signed direct column. Both use original
ball-major order, including all padding and every inactive row. -/
theorem cash_entry_word (chart : Chart w q D) (event : Attempt) (input : Memory w) (labels : LabelSource)
    (physical : chart.commit event=pricedSegment x.form.pricedArea x.form.stockSource labels w x.ballot)
    (ready : Calendar.ready chart (.attempt event) input)
    (board : EventBoard (fresh x.form.pricedArea x.form.stockSource) w)
    (snapshot : x.mem=stageInput x.form.pricedArea x.form.stockSource labels
      (postOutput (chart.layout event) (Calendar.repair chart event) (prepared chart event input)))
    (covered : ∀j,j∈liveRows x.ballot x.mem x.raw.market.rows → ∃r,ballsAt r=j)
    (i : Fin (x.raw.market.rows*D)) :
    Calendar.after chart (.attempt event) input (x.form.pricedArea.direct+x.form.occurrences+i.val)=
      ((cashEntry x ballsAt columns keys idle scale stock catalogue includeMenu widths mass).bits i:Word w) := by
  let cell := finProdFinEquiv.symm i
  have position : ((x.plan.enum ⟨cell.1,cell.2⟩).val)=i.val :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
  have stored := priced_debit chart event input x.form.pricedArea x.form.stockSource labels x.ballot
    physical ready board (x.plan.enum ⟨cell.1,cell.2⟩)
  change Calendar.after chart (.attempt event) input
    (x.form.pricedArea.direct+x.form.occurrences+(x.plan.enum ⟨cell.1,cell.2⟩).val)=_ at stored
  rw [position] at stored
  have bits := cash_entry_read x ballsAt columns keys idle scale stock catalogue includeMenu widths mass covered cell
  change (cashEntry x ballsAt columns keys idle scale stock catalogue includeMenu widths mass).bits
    (finProdFinEquiv (finProdFinEquiv.symm i))=_ at bits
  rw [Equiv.apply_symm_apply] at bits
  rw [bits]
  rw [←snapshot] at stored
  exact stored

/-- The common finite width entry bound covers the payload half of the
installed catalogue and every coefficient of that local menu. -/
theorem left_maximum {L P : Type*} [Fintype L] [Fintype P] (l : PacketWidths L) (p : PacketWidths P) :
    l.maximum≤(l.either p).maximum :=
  Finset.sup_le (fun i _ => (l.either p).maximum_ge (.inl i))

theorem right_maximum {L P : Type*} [Fintype L] [Fintype P] (l : PacketWidths L) (p : PacketWidths P) :
    p.maximum≤(l.either p).maximum :=
  Finset.sup_le (fun i _ => (l.either p).maximum_ge (.inr i))

/-- Finite physical capacity fields for an already specified catalogue board. -/
structure StripSizes.Room {n : ℕ} (raw : Format z d k q n) (slots : Fin n→Option Expr)
    (start D entries maximum w : ℕ) : Prop where
  ports : n≤D
  portFit : D≤2^w
  termFit : q≤2^w
  copyFit : raw.histMass<2^w
  sumFit : q*raw.histMass<2^w
  codeFit : 1+entries≤2^w
  maximumFit : maximum≤raw.batch.batch.maxWidth
  fieldFit : raw.batch.batch.maxWidth<2^w
  wide : raw.histMass*raw.batch.batch.maxWidth<2^w
  bankFit : (PortPadding.format D start slots raw).pricedArea.start+raw.coordinates<2^w

structure StripSizes {n : ℕ} (raw : Format z d k q n) (slots : Fin n→Option Expr) (start D entries maximum : ℕ)
    (mem : Memory w) : Prop extends StripSizes.Room raw slots start D entries maximum w where
  loaded : (⟨start,raw.market.rows,D⟩ : PortHeader).Loaded mem

omit [Nonempty (Fin k)] in
theorem StripSizes.of_header {n : ℕ} {raw : Format z d k q n} {slots : Fin n→Option Expr}
    {start D entries maximum : ℕ} {mem : Memory w}
    (room : StripSizes.Room raw slots start D entries maximum w)
    (loaded : (⟨start,raw.market.rows,D⟩ : PortHeader).Loaded mem) :
    StripSizes raw slots start D entries maximum mem := ⟨room,loaded⟩

def StripInput.ofBoard (menu : Probe.FixedMenu F e req prices ε tree N)
    (addr : A→Expr) (active : Expr) (board : StripDirectory.Boards z d k q (Fintype.card A) (Fintype.card Roles))
    (prior start : ℕ) (mem : Memory w)
    (bounds : StripSizes (nativeStrip menu addr active board prior) (nativeSlot (B:=B) (C:=C) (H:=H) (k:=k) addr active)
      start D (Fintype.card menu.index) (PacketWidths.ofMenu menu).maximum mem) : StripInput menu w z d q D :=
  ⟨addr,active,board,prior,start,mem,bounds.ports,bounds.loaded,bounds.portFit,bounds.termFit,bounds.copyFit,
    bounds.sumFit,bounds.codeFit,bounds.maximumFit,bounds.fieldFit,bounds.wide,bounds.bankFit⟩

/-- The snapshot used by the charged commit includes both physical overlays. -/
def commitMemory (chart : Chart w q D) (event : Attempt) (before : Memory w) (area : Area) (src : Sources)
    (labels : LabelSource) :=
  stageInput area src labels (postOutput (chart.layout event) (Calendar.repair chart event) (prepared chart event before))

theorem retained_operand (chart : Chart w q D) (event : Attempt) (before : Memory w) (area : Area) (src : Sources)
    (labels : LabelSource) (ready : Calendar.ready chart (.attempt event) before)
    (x : ℕ) (atBirth : Calendar.protected chart x (.attempt event)) (low : x<labels.out)
    (order : labels.out≤area.start) : commitMemory chart event before area src labels x=before x :=
  (stage_frame area src labels _ x low order).trans (postOutput_prior chart event before x ready atBirth)

/-- The literal row and key operands can be loaded in the birth memory:
the price-label pass and fresh stock copy preserve the complete header. -/
theorem retained_header (chart : Chart w q D) (event : Attempt) (before : Memory w) (area : Area) (src : Sources)
    (labels : LabelSource) (ready : Calendar.ready chart (.attempt event) before)
    (header : PortHeader) (loaded : header.Loaded before) (room : header.stop≤labels.out)
    (order : labels.out≤area.start)
    (frozen : ∀ x,header.start≤x → x<header.stop → Calendar.protected chart x (.attempt event)) :
    header.Loaded (commitMemory chart event before area src labels) :=
  loaded.frame (fun x lo hi=>retained_operand chart event before area src labels ready x (frozen x lo hi)
    (hi.trans_le room) order)

/-- Every true original core tile survives market tests, sign posting and
the seed copy at the same address. -/
theorem retained_tiles {rows positions n : ℕ} (chart : Chart w q D) (event : Attempt) (before : Memory w)
    (area : Area) (src : Sources) (labels : LabelSource) (ready : Calendar.ready chart (.attempt event) before)
    (bank : Bank) (table : Fin rows→Fin positions→Fin n) (loaded : ProtocolRAMPurchaseGateColumns.TileRows bank table before)
    (room : bank.base+positions*rows≤labels.out) (order : labels.out≤area.start)
    (frozen : ∀ x,bank.base≤x → x<bank.base+positions*rows → Calendar.protected chart x (.attempt event)) :
    ProtocolRAMPurchaseGateColumns.TileRows bank table (commitMemory chart event before area src labels) := by
  intro i j
  have high : j.val*rows+i.val<positions*rows :=
    (Nat.add_lt_add_left i.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ j.isLt)
  have bound := Nat.add_lt_add_left high bank.base
  exact (retained_operand chart event before area src labels ready _ (frozen _ (Nat.le_add_right ..) bound)
    (bound.trans_le room) order).trans (loaded i j)

section payload
set_option maxHeartbeats 1200000
open ProbeStage StripDirectory PurchaseFrozen
local notation "stages" => (permutationFabric z d).shapes.length
variable [SiteNaming (ColumnSite (PayloadStrip.Columns ((permutationFabric z d).shapes.length)) k)]
  (hk : 0<k) (M : ℝ) (hM : 0≤M) (eps : ℝ) (he : 0<eps) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
  (board : StripDirectory.Boards z d k q (Fintype.card (PayloadStrip.Quotes ((permutationFabric z d).shapes.length) k)) (Fintype.card (PayloadRole ((permutationFabric z d).shapes.length) k)))
  (prior start : ℕ) (mem : Memory w)
local instance : Nonempty (PayloadRole stages k) := ⟨.catalyst (PayloadStrip.first stages 0) (Classical.choice inferInstance)⟩
local notation "menuP" => payloadMenu F stages k hk M hM eps he tree ht minimum
local notation "sourceP" => board.build (payloadFormat F z d k q hk M hM eps he tree ht minimum) prior
variable (size : StripSizes (board.build (payloadFormat F z d k q hk M hM eps he tree ht minimum) prior) (payloadChannels z ((permutationFabric z d).shapes.length) k).slot start D
  (Fintype.card ((payloadMenu F ((permutationFabric z d).shapes.length) k hk M hM eps he tree ht minimum)).index) (PacketWidths.ofMenu (payloadMenu F ((permutationFabric z d).shapes.length) k hk M hM eps he tree ht minimum)).maximum mem)

def StripInput.of_payload : StripInput menuP w z d q D :=
  StripInput.ofBoard menuP (payloadSlot z) (payloadChannels z stages k).live board prior start mem size

local notation "instanceP" => StripInput.of_payload hk M hM eps he tree ht minimum board prior start mem size

omit [Nonempty (Fin k)] in
theorem payload_native : (instanceP).form=PortPadding.format D start (payloadChannels z stages k).slot sourceP := rfl

omit [Nonempty (Fin k)] in
/-- Payload stock addresses at an original ball are literal global commodity slots. -/
theorem payload_addresses (original : ∀ j,j∈liveRows (instanceP).ballot mem (sourceP).market.rows → j.val<2^z) :
    (instanceP).Addresses := by
  intro j live a
  let p : Fin (2^z) := ⟨j.val,original j live⟩
  change ((payloadSlot z a).eval mem (p.val:Word w)).val<PurchaseInventory.footprint z stages k
  rw [payloadSlot_read mem p a]
  exact (Nat.mod_le ..).trans_lt (PurchaseInventory.slot_lt _)

omit [Nonempty (Fin k)] in
/-- Original indexed row coverage discharges the address bound without
requiring a second stock or ballot invariant. -/
theorem payload_addresses_of_coverage (room : 2^z≤ (sourceP).market.rows)
    (covered : ∀ j,j∈liveRows (instanceP).ballot mem (sourceP).market.rows →
      ∃ r : Fin (2^z),payloadBalls z (sourceP).market.rows room r=j) :
    (instanceP).Addresses := by
  apply payload_addresses hk M hM eps he tree ht minimum board prior start mem size
  intro j live
  obtain ⟨r,rfl⟩ := covered j live
  exact r.isLt

end payload
section purchased
set_option maxHeartbeats 1200000
open ProbeStage StripDirectory PurchaseFrozen
local notation "stages" => (permutationFabric z d).shapes.length
variable (depth keyBase : ℕ) [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (sh : Shelf) (sampler : PurchaseSampler) (hk : 0<k) (M : ℝ) (hM : 0≤M)
  (eps : ℝ) (he : 0<eps) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
  (board : StripDirectory.Boards z d k q (Fintype.card (ChainStrip.Axes depth k)) (Fintype.card (PurchasedRole depth k)))
  (prior start : ℕ) (mem : Memory w)
local instance : Nonempty (PurchasedRole depth k) := ⟨.catalyst (ChainStrip.inlet depth 0) (Classical.choice inferInstance)⟩
local notation "menuB" => purchasedMenu F depth k hk M hM eps he tree ht minimum
local notation "sourceB" => board.build (purchasedFormat F z d k q depth keyBase sh sampler hk M hM eps he tree ht minimum) prior
local notation "chan" => purchasedChannels (z:=z) (d:=d) (k:=k) sh sampler depth keyBase
variable (size : StripSizes (board.build (purchasedFormat F z d k q depth keyBase sh sampler hk M hM eps he tree ht minimum) prior) ((purchasedChannels (z:=z) (d:=d) (k:=k) sh sampler depth keyBase)).slot start D (Fintype.card ((purchasedMenu F depth k hk M hM eps he tree ht minimum)).index) (PacketWidths.ofMenu (purchasedMenu F depth k hk M hM eps he tree ht minimum)).maximum mem)

def StripInput.of_purchased : StripInput menuB w z d q D :=
  StripInput.ofBoard menuB (chan).address (chan).live board prior start mem size

omit [Nonempty (Fin k)] in
theorem purchased_native : (StripInput.of_purchased depth keyBase sh sampler hk M hM eps he tree ht minimum
    board prior start mem size).form=PortPadding.format D start (chan).slot sourceB := rfl

omit [Nonempty (Fin k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
/-- An admitted DFS path reads the global stock slot of its actual tile.
The ranked occurrence comes from the affirmative purchase at its birth. -/
theorem candidate_slot_lt (π : Equiv.Perm (Fin (2^z))) (snapshot : Shelf.Mem z d)
    (headers : (stratumHeader z d k sampler.degree depth keyBase).Loaded snapshot)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L sampler depth key).source
      (Shelf.pathRows sampler π depth key) snapshot)
    (keys : PurchaseFrozen.count z d k≤2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z sampler.degree depth≤2^(Native.wordBits z d Native.copies))
    (marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z)))
    (path : LiveChains sampler π depth marked) (u : ChainStrip.Axes depth k) :
    ((chan).address u |>.eval snapshot ((BoughtLocation.relative path).val:Word (Native.wordBits z d Native.copies))).val <
      PurchaseInventory.footprint z stages k := by
  have printed := relative_stock sh keyBase marked path snapshot tiles headers keys room u
  change ((allChainSlot (z:=z) (d:=d) sh sampler depth _ u).eval snapshot _).val < _
  rw [printed]
  exact (Nat.mod_le ..).trans_lt (PurchaseInventory.slot_lt _)

omit [Nonempty (Fin k)] in
theorem purchased_addresses (snapshot : Shelf.Mem z d)
    (actualSize : StripSizes sourceB (chan).slot start D (Fintype.card (menuB).index) (PacketWidths.ofMenu menuB).maximum snapshot)
    (π : Equiv.Perm (Fin (2^z)))
    (headers : (stratumHeader z d k sampler.degree depth keyBase).Loaded snapshot)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L sampler depth key).source
      (Shelf.pathRows sampler π depth key) snapshot)
    (keys : PurchaseFrozen.count z d k≤2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z sampler.degree depth≤2^(Native.wordBits z d Native.copies))
    (marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z)))
    (pathsAt : ∀ j, j ∈ liveRows (enabledBatch (sourceB).market.layout
      (PortPadding.format D start (chan).slot sourceB).board) snapshot (sourceB).market.rows →
      ∃ path : LiveChains sampler π depth marked, (BoughtLocation.relative path).val = j.val) :
    (StripInput.of_purchased depth keyBase sh sampler hk M hM eps he tree ht minimum board prior start snapshot actualSize).Addresses := by
  intro j live u
  obtain ⟨path,equal⟩ := pathsAt j live
  change (Expr.eval snapshot (j.val : Word (Native.wordBits z d Native.copies)) ((chan).address u)).val <
    PurchaseInventory.footprint z stages k
  rw [← equal]
  exact candidate_slot_lt depth keyBase sh sampler π snapshot headers tiles keys room marked path u

omit [Nonempty (Fin k)] in
/-- A rectangular purchased board can also contain more positions than
the true DFS inventory. Only the actually entered original rows need a tile. -/
theorem purchased_addresses_of_coverage {R : Type*} (snapshot : Shelf.Mem z d)
    (actualSize : StripSizes sourceB (chan).slot start D (Fintype.card (menuB).index) (PacketWidths.ofMenu menuB).maximum snapshot)
    (π : Equiv.Perm (Fin (2^z)))
    (headers : (stratumHeader z d k sampler.degree depth keyBase).Loaded snapshot)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L sampler depth key).source
      (Shelf.pathRows sampler π depth key) snapshot)
    (keys : PurchaseFrozen.count z d k≤2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z sampler.degree depth≤2^(Native.wordBits z d Native.copies))
    (ballsAt : R ↪ Fin (sourceB).market.rows)
    (marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z)))
    (original : ∀ r, ∃ path : LiveChains sampler π depth marked, (BoughtLocation.relative path).val = (ballsAt r).val)
    (covered : ∀ j,j∈liveRows (enabledBatch (sourceB).market.layout
      (PortPadding.format D start (chan).slot sourceB).board) snapshot (sourceB).market.rows → ∃r,ballsAt r=j) :
    (StripInput.of_purchased depth keyBase sh sampler hk M hM eps he tree ht minimum
      board prior start snapshot actualSize).Addresses := by
  apply purchased_addresses depth keyBase sh sampler hk M hM eps he tree ht minimum board prior start
    snapshot actualSize π headers tiles keys room marked
  intro j live
  obtain ⟨r,rfl⟩ := covered j live
  exact original r

omit [Nonempty (Fin k)] in
/-- In the chronological priced commit the geometric source operands are
read at the exact same addresses as in the genuine before-date CT memory. -/
theorem purchased_addresses_at_commit (π : Equiv.Perm (Fin (2^z)))
    (chart : Chart (Native.wordBits z d Native.copies) q D) (event : Attempt) (before : Shelf.Mem z d)
    (area : Area) (src : Sources) (labels : LabelSource)
    (ready : Calendar.ready chart (.attempt event) before)
    (actualSize : StripSizes sourceB (chan).slot start D (Fintype.card (menuB).index) (PacketWidths.ofMenu menuB).maximum
      (commitMemory chart event before area src labels))
    (headerRead : (stratumHeader z d k sampler.degree depth keyBase).Loaded before)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L sampler depth key).source
      (Shelf.pathRows sampler π depth key) before)
    (savedHeader : ∀ x,keyBase≤x → x<(stratumHeader z d k sampler.degree depth keyBase).stop →
      Calendar.protected chart x (.attempt event))
    (savedTiles : ∀ (key : Key z d k) x,(sh.L sampler depth key).source.base≤x →
      x<(sh.L sampler depth key).source.base+(depth+1)*paths z sampler.degree depth →
      Calendar.protected chart x (.attempt event))
    (headerRoom : (stratumHeader z d k sampler.degree depth keyBase).stop≤labels.out)
    (tileRoom : ∀key : Key z d k,(sh.L sampler depth key).source.base+(depth+1)*paths z sampler.degree depth≤labels.out)
    (order : labels.out≤area.start)
    (keys : PurchaseFrozen.count z d k≤2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z sampler.degree depth≤2^(Native.wordBits z d Native.copies))
    (marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z)))
    (pathsAt : ∀ j, j ∈ liveRows (enabledBatch (sourceB).market.layout
      (PortPadding.format D start (chan).slot sourceB).board) (commitMemory chart event before area src labels)
      (sourceB).market.rows → ∃ path : LiveChains sampler π depth marked, (BoughtLocation.relative path).val = j.val) :
    (StripInput.of_purchased depth keyBase sh sampler hk M hM eps he tree ht minimum board prior start
      (commitMemory chart event before area src labels) actualSize).Addresses := by
  apply purchased_addresses depth keyBase sh sampler hk M hM eps he tree ht minimum board prior start
    _ actualSize π _ _ keys room marked pathsAt
  · exact retained_header chart event before area src labels ready _ headerRead headerRoom order
      savedHeader
  · intro key
    exact retained_tiles chart event before area src labels ready _ _ (tiles key)
      (by simpa only [PurchaseDFS.length_layout,PurchaseFrozen.paths] using tileRoom key) order
      (by simpa only [PurchaseDFS.length_layout,PurchaseFrozen.paths] using savedTiles key)

end purchased

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
