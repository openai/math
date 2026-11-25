import OAI.Hierarchy.ProbeStripPlacedInputs
import OAI.Hierarchy.ProbeFixedElectionPages

namespace OAI
/-! # The placed stock, packet, wire, and scatter operands on the fixed calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StripDirectory
open PurchaseStage PurchaseFrozen StockCommit
open scoped Classical Fin.CommRing
private structure ReaderBanks {z radix k q digits ports : ℕ}
    (b : StripDirectory.Boards z radix k q digits ports) (active cut : ℕ) : Prop where
  report : b.report.inputEnd ≤ cut
  terms : b.terms.base+b.terms.size ≤ cut
  menu : b.menu.base+b.menu.size ≤ cut
  selectors : b.selectors.base+b.selectors.size ≤ cut
  stock : active+b.old.size ≤ cut
  price : b.price.base+b.price.size ≤ cut
  offsets : (GlobalTests.offsets b.globalTests).base+(GlobalTests.offsets b.globalTests).size ≤ cut

section
variable {z radix k q depth : ℕ} (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z radix)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (s : StripChart.Boards z radix k q depth)

private theorem payload_readers (phase trial active cut : ℕ)
    (banks : ReaderBanks (s.outer phase trial) active cut) :
    let t := Attempt.outer phase trial
    let x := build F s t active
    x.board.repairBits.base+x.board.repairBits.size ≤ cut →
    (x.occurrenceHeader (StripChart.start s t)).stop ≤ cut →
    PlacedInputs x cut ∧ ∀j,(x.board.reportWidth j).inputEnd≤cut := by
  let stages := (permutationFabric z radix).shapes.length
  let t := Attempt.outer phase trial
  let b := s.outer phase trial
  let m : Market z radix k :=
    {b.market with sampler:=s.sampler,depth:=depth,shelf:={b.market.shelf with stockBase:=active}}
  let menu := payloadMenu F stages k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    (s.tree t) (s.tree_nonneg t) s.minimum
  exact placed_inputs (F:=F) (payloadChannels z stages k) menu b m
    (max (Fintype.card (PayloadRole stages k)) (Fintype.card (PurchasedRole depth k)))
    (StripChart.start s t) cut (payload_before z stages k cut)
    banks.report banks.terms banks.menu banks.selectors banks.stock banks.price banks.offsets

private theorem purchased_readers (phase trial j u active cut : ℕ)
    (banks : ReaderBanks (s.inner phase trial j u) active cut)
    (channels : (purchasedChannels (z:=z) (d:=radix) (k:=k) (s.outer phase trial).market.shelf
      s.sampler depth (s.stratumHeader phase trial)).Before cut) :
    let t := Attempt.inner phase trial j u
    let x := build F s t active
    x.board.repairBits.base+x.board.repairBits.size ≤ cut →
    (x.occurrenceHeader (StripChart.start s t)).stop ≤ cut →
    PlacedInputs x cut ∧ ∀j,(x.board.reportWidth j).inputEnd≤cut := by
  let stages := (permutationFabric z radix).shapes.length
  let t := Attempt.inner phase trial j u
  let b := s.inner phase trial j u
  let m : Market z radix k :=
    {b.market with sampler:=s.sampler,depth:=depth,shelf:={b.market.shelf with stockBase:=active}}
  let ch := purchasedChannels (z:=z) (d:=radix) (k:=k) (s.outer phase trial).market.shelf
    s.sampler depth (s.stratumHeader phase trial)
  let menu := purchasedMenu F depth k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    (s.tree t) (s.tree_nonneg t) s.minimum
  exact placed_inputs (F:=F) ch menu b m
    (max (Fintype.card (PayloadRole stages k)) (Fintype.card (PurchasedRole depth k)))
    (StripChart.start s t) cut channels
    banks.report banks.terms banks.menu banks.selectors banks.stock banks.price banks.offsets

end

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "d" => 2^v.W
local notation "W" => wordBits z d copies
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "sized" => v.sized (v.seed P z width) width
local notation "slab" => v.slab (v.seed P z width) P width

theorem stock_occurrence_end (a : Attempt) :
    ((f a).occurrenceHeader (StripChart.start B a)).stop ≤ (G).first := by
  have h:= (shape_header F B v.mesh G P.joint.initial a).1
  change (f a).occurrenceHeader (StripChart.start B a)=StripChart.header F B a at h
  rw [h]
  have eq : StripChart.header F B a=(H).ports.header 0 := by
    cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl
  rw [eq]
  exact ((H).ports.end_le 0).trans (v.stock_port_room P z width)

private theorem stock_format_keys {h radix lanes letters goods : ℕ} (ff : Format h radix lanes letters goods) :
    ff.market.shelf.firstBase ≤ ff.board.keys ∧ ff.board.keys ≤ ff.labelStart := by
  have tests : ff.market.shelf.firstBase ≤ ff.testsStart := by
    unfold Format.testsStart Market.flags PurchaseFrozen.Shelf.flagsBase
    omega
  have mask : ff.testsStart ≤ ff.maskStart := by
    unfold Format.maskStart PostLayout.afterTests
    omega
  have keys : ff.maskStart ≤ ff.board.keys := Nat.le_add_right ..
  have final : ff.board.keys ≤ ff.board.verdict := by
    change ff.maskStart+2^ff.indexBits ≤ PostLayout.column ff.maskStart ff.indexBits ff.market.rows _
    unfold PostLayout.column PostLayout.startColumns
    omega
  exact ⟨tests.trans (mask.trans keys),final.trans (Nat.le_add_right ..)⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 600000 in
theorem stock_keys (a : Attempt) :
    (G).base v.mesh (.attempt a)+Slab.selectorSpan sized ≤ (f a).board.keys ∧
      (f a).board.keys ≤ (f a).labelStart := by
  let ff := f a
  let base := (G).base v.mesh (.attempt a)
  have shelfBase : ff.market.shelf.firstBase = Slab.first slab sized base := by cases a <;> rfl
  obtain ⟨low, high⟩ := stock_format_keys ff
  refine ⟨le_trans ?_ low, high⟩
  rw [shelfBase]
  exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

set_option cleanup.letToHave false in
set_option maxHeartbeats 1600000 in
theorem stock_reader_extents (a : Attempt)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    PlacedInputs (f a) (f a).board.keys ∧ (∀j,((f a).board.reportWidth j).inputEnd≤(f a).board.keys) := by
  let cut:=(f a).board.keys
  let base:=(G).base v.mesh (.attempt a)
  have sel : base+Slab.selectorSpan sized≤cut := (v.stock_keys P z width a).1
  have low : base≤cut := (Nat.le_add_right ..).trans sel
  have ports : ((f a).occurrenceHeader (StripChart.start B a)).stop≤cut :=
    (v.stock_occurrence_end P z width a).trans ((Nat.le_add_right ..).trans low)
  have mask : (f a).board.repairBits.base+(f a).board.repairBits.size≤cut := le_rfl
  obtain ⟨price,scores,menuL,menuR,termsL,termsR,_,_⟩ := v.election_public P z width a
  let page:=DeadlineROM.scorePage v.mesh (JointHeader.scores P.joint z N k) z N k a
  have off : (GlobalTests.offsets page).base+(GlobalTests.offsets page).size≤cut := by
    change page.base+2^(GlobalTests.bits z N k)≤cut
    change GlobalTests.stop page z N k+2^(GlobalTests.bits z N k)≤base at scores
    unfold GlobalTests.stop at scores
    omega
  have old:=v.stock_padded_old P z width a
  rw [←v.stock_raw_old_size P z width a] at old
  let active := resolvedStock v.mesh G P.joint.initial (build F B)
  cases a with
  | outer p a =>
    let t := Attempt.outer p a
    apply payload_readers F B p a (active t) cut _ mask ports
    exact ⟨Nat.zero_le _,termsL.trans low,menuL.trans low,sel,old.trans low,price.trans low,off⟩
  | inner p a j u =>
    let t := Attempt.inner p a j u
    let ch := purchasedChannels (z:=z) («d»:=d) (k:=k) ((B).outer p a).market.shelf
      (B).sampler v.depth ((B).stratumHeader p a)
    have chFits : ch.Before base := by
      obtain ⟨flags,sources⟩:=v.catalyst_bought_bank_room P z width p a j u
      apply purchased_before _ _ _ _ _ sources flags
      let h:=stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase
      have head : h.stop≤base := core.trans ((v.catalyst_initial_le_first P z width).trans (Nat.le_add_right ..))
      change h.start+h.small≤base ∧ h.start+h.small+h.small≤base
      change h.start+2*h.small+h.large+h.large≤base at head
      omega
    have channels : ch.Before cut := ⟨fun i=>(chFits.address i).trans low,chFits.live.trans low⟩
    apply purchased_readers F B p a j u (active t) cut _ channels mask ports
    exact ⟨Nat.zero_le _,termsR.trans low,menuR.trans low,sel,old.trans low,price.trans low,off⟩

theorem stock_batch_report (a : Attempt)
    (_cap : v.menu.maximum<2^W) (_threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    PlacedInputs (f a) (f a).board.keys ∧ (∀j,((f a).board.reportWidth j).inputEnd≤(f a).board.keys) :=
  v.stock_reader_extents P z width a core

theorem stock_batch_operands (a : Attempt)
    (cap : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    PlacedInputs (f a) (f a).board.keys :=
  (v.stock_batch_report P z width a cap threshold core).1

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
