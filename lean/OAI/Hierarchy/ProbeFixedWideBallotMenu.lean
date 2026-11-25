import OAI.Hierarchy.ProbeFixedWideBallotRead
import OAI.Hierarchy.ProbeFixedDatedRepairs
import OAI.Hierarchy.ProbeFixedRepairWordRoom

namespace OAI
/-! # Admissible native menu ordinals of elected physical ballots -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory PurchaseFrozen CatalogueRows WireTelescope
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "H" => v.publicHeader P z width
local notation "f" => v.nativeFormats P z width
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "FEE" => charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "arena" => v.privateArena P z width

section
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.outer phase trial) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.payloadTest P z width phase trial

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
set_option cleanup.letToHave false in
include fitted s in
omit [Nonempty (Fin k)] in
theorem payload_ballot_menu (_geom : v.PayloadRepairGeometry P z width r banks src tab dst owners phase trial entry)
    (maxWord : (H).payload.maxWord<2^W)
    (j : Fin (f ev).market.rows) (activeRow : committed (v.ballot P z width r banks src tab dst owners ev)
      (HistogramShelf.snapshot C ev entry) (j.val:Word W)) :
    ∃i : (v.payloadPacketMenu N).index, (v.ballot P z width r banks src tab dst owners ev).packet.eval
      (HistogramShelf.snapshot C ev entry) (j.val:Word W)=(((Fintype.equivFin _ i).val+1:ℕ):Word W) := by
  classical
  have date:=dateInTable_of_event v.mesh ev s.event
  have timeMin : (v.finish:ℝ)/2≤t := by
    have positive : 0<(v.finish:ℝ):=by exact_mod_cast v.clock.finish_pos
    exact (show (v.finish:ℝ)/2≤v.finish by linarith).trans (v.real_times date).1
  have positive : 0<t := (half_pos (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos)).trans_le timeMin
  have pages:=s.pages
  have room:=v.purchased_table_room z s.late
  have saved:=v.row_buffer_stock P z width r banks src tab dst owners ev entry live bills
  have first:=v.row_quote_cells P z width bills ev entry pre date pages.guard.header.scalar pages.guard.scores
    room.2.2.2 (fun i=>(saved i).1) s.limit
  have last:=v.row_quote_cells P z width bills ev entry stage date pages.stage.header.scalar pages.stage.scores
    room.2.2.2 (fun i=>(saved i).2.2) s.limit
  have active:=v.payload_repair_live P z width r banks src tab dst owners phase trial entry fitted s
  have keep : j∈(T).selected :=
    (v.wide_ballot_in_tape_iff P z width r banks src tab dst owners ev entry s.layout live π j).2 activeRow
  have high : (test).failure.cut < (test).failure.value pre j :=
    v.selected_high P z width r banks src tab dst owners ev entry s.layout live π s.threshold j keep j.isLt
  have original := v.payload_live_lt P z width phase trial pre j
    (j.isLt.trans_le (v.market_rows_fit P z width s.late ev)) (active j keep)
  have packet := v.payload_packet_read P z width r banks src tab dst owners phase trial entry
    t positive j original pre stage pages.guard.header pages.stage.header maxWord first last high
  have legal := v.payload_key_legal P z width bills ev t positive entry (⟨j.val, original⟩ : Fin (2^z))
  obtain ⟨discrepancy, decoded⟩ := packet
  let choice := (v.payloadPacketMenu N).select ⟨_, legal, discrepancy⟩
  have atStage := v.wide_ballot_packet_at_stage P z width r banks src tab dst owners ev entry s.layout live j
  exact ⟨choice, atStage.symm.trans decoded.1⟩

end

section
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial slice inner entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.inner phase trial slice inner) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.purchasedTest P z width phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
set_option cleanup.letToHave false in
include fitted s in
omit [Nonempty (Fin k)] in
theorem purchased_ballot_menu (_geom : v.PurchasedRepairGeometry P z width r banks src tab dst owners phase trial slice inner entry)
    (maxWord : (H).bought.maxWord<2^W)
    (perm : Equiv.Perm (Fin (2^z))) (headLow : (h₀).stop≤(arena).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S perm v.depth ((bs).stratumHeader phase trial) entry k)
    (j : Fin (f ev).market.rows) (activeRow : committed (v.ballot P z width r banks src tab dst owners ev)
      (HistogramShelf.snapshot C ev entry) (j.val:Word W)) :
    ∃i : v.purchasePacketMenu.index, (v.ballot P z width r banks src tab dst owners ev).packet.eval
      (HistogramShelf.snapshot C ev entry) (j.val:Word W)=(((Fintype.equivFin _ i).val+1:ℕ):Word W) := by
  classical
  have date:=dateInTable_of_event v.mesh ev s.event
  have timeMin : (v.finish:ℝ)/2≤t := (v.real_times date.1).2 slice
  have positive : 0<t := (half_pos (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos)).trans_le timeMin
  have pages:=s.pages
  have room:=v.purchased_table_room z s.late
  have saved:=v.row_buffer_stock P z width r banks src tab dst owners ev entry live bills
  have first:=v.row_quote_cells P z width bills ev entry pre date pages.guard.header.scalar pages.guard.scores
    room.2.2.2 (fun i=>(saved i).1) s.limit
  have last:=v.row_quote_cells P z width bills ev entry stage date pages.stage.header.scalar pages.stage.scores
    room.2.2.2 (fun i=>(saved i).2.2) s.limit
  let archive:=v.purchased_row_archive P z width r banks src tab dst owners phase trial slice inner entry perm live headLow born
  have witness := v.purchased_archive_live_rows P z width r banks src tab dst owners phase trial slice inner
    entry perm s.late archive
  have active:=v.purchased_repair_live P z width r banks src tab dst owners phase trial slice inner entry fitted s
  have keep : j∈(T).selected :=
    (v.wide_ballot_in_tape_iff P z width r banks src tab dst owners ev entry s.layout live π j).2 activeRow
  have high : (test).failure.cut < (test).failure.value pre j :=
    v.selected_high P z width r banks src tab dst owners ev entry s.layout live π s.threshold j keep j.isLt
  obtain ⟨hits, signed, before, after⟩ := v.purchased_raw_slots P z width phase trial slice inner perm
    pre stage archive.preHeader archive.stageHeader archive.preTiles archive.stageTiles
    room.1 room.2.1 j (witness j (active j keep))
  have packet := v.purchased_packet_read P z width r banks src tab dst owners phase trial slice inner entry
    t positive j hits pre stage pages.guard.header pages.stage.header maxWord first last before after signed high
  have legal := v.purchased_key_legal P z width bills ev t positive entry hits signed
  obtain ⟨discrepancy, decoded⟩ := packet
  let choice := v.purchasePacketMenu.select ⟨_, legal, discrepancy⟩
  have atStage := v.wide_ballot_packet_at_stage P z width r banks src tab dst owners ev entry s.layout live j
  exact ⟨choice, atStage.symm.trans decoded.1⟩

end

/-- Cardinality of the physical menu in the original strip species. -/
def ballotAtoms : Attempt→ℕ
  | .outer ..=>Fintype.card (v.payloadPacketMenu N).index
  | .inner ..=>Fintype.card v.purchasePacketMenu.index

omit [Nonempty (Fin k)] in
theorem ballotAtoms_le (a : Attempt) : v.ballotAtoms z a≤v.menuCodes N := by
  cases a
  · exact le_max_left ..
  · exact le_max_right ..

section Native
variable {v P z width r banks src tab dst owners}
variable {perm : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners perm mem fixture)

private theorem inner_indices (c : Mesh) (p h j b : ℕ) (incl : Event.attempt (.inner p h j b)∈events c) :
    p<c.inject+c.cool ∧ h<c.outerFuel ∧ j<c.reserveSteps ∧ b<c.innerFuel := by
  obtain ⟨u,hu,phase⟩:=List.mem_flatMap.mp incl
  rcases List.mem_append.mp phase with attempts|endPhase
  · obtain ⟨a,ha,trial⟩:=List.mem_flatMap.mp attempts
    rcases List.mem_cons.mp trial with outer|inside
    · cases outer
    · obtain ⟨v,hv,slice⟩:=List.mem_flatMap.mp inside
      rcases List.mem_append.mp slice with actions|endSlice
      · obtain ⟨t,ht,same⟩:=List.mem_map.mp actions
        cases same
        exact ⟨List.mem_range.mp hu,List.mem_range.mp ha,List.mem_range.mp hv,List.mem_range.mp ht⟩
      · simp at endSlice
  · simp at endPhase

private theorem outer_indices (c : Mesh) (p h : ℕ) (incl : Event.attempt (.outer p h)∈events c) :
    p<c.inject+c.cool ∧ h<c.outerFuel := by
  obtain ⟨u,hu,phase⟩:=List.mem_flatMap.mp incl
  rcases List.mem_append.mp phase with attempts|endPhase
  · obtain ⟨a,ha,trial⟩:=List.mem_flatMap.mp attempts
    rcases List.mem_cons.mp trial with same|inside
    · cases same
      exact ⟨List.mem_range.mp hu,List.mem_range.mp ha⟩
    · obtain ⟨v,_,sl⟩:=List.mem_flatMap.mp inside
      rcases List.mem_append.mp sl with inner|tip
      · obtain ⟨_,_,bad⟩:=List.mem_map.mp inner
        cases bad
      · simp at tip
  · simp at endPhase

include D in
omit [Nonempty (Fin k)] in
/-- The native financial election, true slot mask, and purchased archives determine
an ordinal of the original strip menu on every committed row. -/
theorem ReadbackRun.ballot_menu (bounds : RepairWordBounds v P z width) (a : Attempt)
    (prior tail : List Event) (entry : Memory W) (slot : Slot C mem (.attempt a) prior tail entry)
    (j : Fin ((C).layout a).candidates)
    (active : committed (v.ballot P z width r banks src tab dst owners a)
      (HistogramShelf.snapshot C a entry) (j.val:Word W)) :
    ∃i : Fin (v.ballotAtoms z a), (v.ballot P z width r banks src tab dst owners a).packet.eval
      (HistogramShelf.snapshot C a entry) (j.val:Word W)=((i.val+1:ℕ):Word W) := by
  classical
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  have present : Event.attempt a∈events v.mesh := by
    change Event.attempt a∈events (C).mesh
    rw [slot.events]
    simp
  let raw:=repair C a
  let L:=(C).layout a
  let entered:=prepared C a entry
  have layout:=(D.boards a present).1
  have cutoff:=slot.currentReady.2.2.2.2.2.1
  change raw.repairBits.base+L.candidates<2^W at cutoff
  have room : L.candidates≤2^W := by omega
  have selected:=(post_selected L raw entered j layout.window.wide room layout.padded).1 active.1
  have failed := (layout.space.mode L raw entered).trans selected.1.1
  let signed := D.failed_event bounds a prior tail entry slot failed
  cases a with
  | outer phase trial =>
    obtain ⟨hp,hh⟩:=outer_indices v.mesh phase trial present
    obtain ⟨_,other⟩:=outer_slot C mem phase trial hp hh D.nativeStock.mounted_all
    have same : trialState C mem phase trial=entry:=other.entryMemory.symm.trans slot.entryMemory
    have geo:=D.payloadRows ⟨phase,hp⟩ ⟨trial,hh⟩
    rw [same] at geo
    let fit:=v.payload_fit_at_slot P z width r banks src tab dst owners phase trial entry signed D.payload
    obtain ⟨i,code⟩:=v.payload_ballot_menu P z width r banks src tab dst owners phase trial entry fit signed geo
      bounds.payloadWord j active
    exact ⟨Fintype.equivFin _ i,code⟩
  | inner phase trial slice inner =>
    obtain ⟨hp,hh,hs,hi⟩:=inner_indices v.mesh phase trial slice inner present
    obtain ⟨_,other⟩:=inner_slot C mem phase trial slice inner hp hh hs hi D.nativeStock.mounted_all
    have same : innerState C mem phase trial slice inner=entry:=other.entryMemory.symm.trans slot.entryMemory
    have geo:=D.boughtRows ⟨phase,hp⟩ ⟨trial,hh⟩ ⟨slice,hs⟩ ⟨inner,hi⟩
    have born:=D.purchased ⟨phase,hp⟩ ⟨trial,hh⟩ ⟨slice,hs⟩ ⟨inner,hi⟩
    rw [same] at geo born
    let fit:=v.purchased_fit_at_slot P z width r banks src tab dst owners phase trial slice inner entry signed D.payload
    have low:=((D.keys phase trial).1).trans
      (show (arena).first≤(arena).base v.mesh (.attempt (.inner phase trial slice inner)) from Nat.le_add_right ..)
    obtain ⟨i,code⟩:=v.purchased_ballot_menu P z width r banks src tab dst owners phase trial slice inner entry fit signed geo
      bounds.boughtWord perm low born j active
    exact ⟨Fintype.equivFin _ i,code⟩

end Native

omit [Nonempty (Fin k)] in
/-- At large heights the whole menu-party product, including its reserved idle
zero, fits the actual native word. Both public menu and party counts are fixed. -/
theorem wide_ballot_tag_room : ∀ᶠ h : ℕ in Filter.atTop,∀a:Attempt,
    let K:=v.menuCodes (Stages h (2^v.W))
    let w:=wordBits h (2^v.W) copies
    1+K≤2^w ∧ K*v.wideBallotParties h a+1≤2^w := by
  let K:=v.menuCodes (publicStages v.W)
  let L:=max (Fintype.card (ColumnSite (PayloadStrip.Columns (publicStages v.W)) k))
    (Fintype.card (ColumnSite (ChainStrip.Columns v.depth) k))
  filter_upwards [Filter.eventually_ge_atTop (1+K*(L+1))] with h large
  intro a S w
  have low : h≤2^w := (Nat.lt_two_pow_self (n:=h)).le.trans
    (Nat.pow_le_pow_right (by decide) (by change h≤wordBits h _ _;rw [wordBits_linear];omega))
  have st : Stages h (2^v.W)=publicStages v.W:=fixed_stage_count h v.W
  have menu : S=K:=congrArg v.menuCodes st
  rw [menu]
  have parties : v.wideBallotParties h a≤L := by
    cases a with
    | outer phase trial=>change Fintype.card (ColumnSite (PayloadStrip.Columns (Stages h (2^v.W))) k)≤_;rw [st];exact le_max_left ..
    | inner phase trial slice rep=>exact le_max_right ..
  have bound:=(Nat.mul_le_mul_left K parties)
  rw [Nat.mul_add] at large
  omega

omit [Nonempty (Fin k)] in
/-- On every genuine attempt, the native committed ballot selects one actual strip
menu atom. Inactive rows have zero selected word by the same authenticated read. -/
theorem wide_elected_ballot :
    ∀ᶠ z : ℕ in Filter.atTop,∀(P : v.Placement) (width r : ℕ) (banks:RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (perm : Equiv.Perm (Fin (2^z)))
      (mem fixture out : Memory (wordBits z (2^v.W) copies)),
      v.ReadbackRun P z width r banks src tab dst owners perm mem fixture →
      let issuedChart:=v.nativeChart P z width r banks src tab dst owners
      let issuedArena:=v.privateArena P z width
      (∀ a : ℕ, a < issuedArena.endAddress v.mesh → out a = checkedOut issuedChart (issuedArena.endAddress v.mesh) mem a) →
      ∀ siteROM (a : Attempt) (prior tail:List Event) (entry : Memory (wordBits z (2^v.W) copies)),
      Slot issuedChart mem (.attempt a) prior tail entry → ∀i:Fin (issuedChart.layout a).candidates,
      committed (v.ballot P z width r banks src tab dst owners a) (HistogramShelf.snapshot issuedChart a entry)
        (i.val:Word (wordBits z (2^v.W) copies)) →
      ∃ atom:Fin (v.ballotAtoms z a),∀party:Fin (v.wideBallotParties z a),
        let X:=v.wideFields P z width siteROM (.attempt a)
        (X.selected party).eval out (i.val:Word (wordBits z (2^v.W) copies))=(((atom.val+1):ℕ):Word (wordBits z (2^v.W) copies)) ∧
        ((X.value party (0 : Fin ((catalogue F (v.configured (v.seed P z width)) v.cost).alphabet+2))).eval out (i.val:Word (wordBits z (2^v.W) copies))).val=atom.val*v.wideBallotParties z a+party.val+1 := by
  filter_upwards [v.repair_word_room,v.wide_ballot_tag_room] with z numeric tags
  intro P width r banks src tab dst owners perm mem fixture out D issuedChart issuedArena archive siteROM a prior tail entry cut i active
  have n:=numeric P width D.payload
  let B : RepairWordBounds v P z width:=⟨n.1,n.2.1,n.2.2.1,n.2.2.2.1,n.2.2.2.2.1,n.2.2.2.2.2⟩
  obtain ⟨atom,read⟩:=D.ballot_menu B a prior tail entry cut i active
  let full:Fin (v.menuCodes (Stages z (2^v.W))):=atom.castLE (v.ballotAtoms_le z a)
  have small:=tags a
  have menuRoom : v.menuCodes (Stages z (2^v.W))+1≤2^(wordBits z (2^v.W) copies) := by
    simpa only [Nat.add_comm 1] using small.1
  have room : atom.val+1<2^(wordBits z (2^v.W) copies) :=
    (Nat.succ_lt_succ full.isLt).trans_le menuRoom
  have val := (congrArg Fin.val read).trans (Fin.val_cast_of_lt room)
  have present : Event.attempt a∈events v.mesh := by
    change Event.attempt a∈events issuedChart.mesh
    rw [cut.events]
    simp
  have layout:=(D.boards a present).1
  have cutoff:=cut.currentReady.2.2.2.2.2.1
  change _+(issuedChart.layout a).candidates<2^(wordBits z (2^v.W) copies) at cutoff
  have fits : (issuedChart.layout a).candidates≤2^(wordBits z (2^v.W) copies):=by omega
  refine ⟨atom,?_⟩
  intro party X
  have saved:=v.wide_ballot_code P z width r banks src tab dst owners siteROM a prior tail mem entry out cut archive
    layout.board fits party i
  have enabled : committed (enabledBatch (issuedChart.layout a) (repair issuedChart a))
      (HistogramShelf.snapshot issuedChart a entry) (i.val:Word (wordBits z (2^v.W) copies)) := active
  rw [ite_eq_left enabled] at saved
  have head:=v.wide_ballot_tag P z width r banks src tab dst owners siteROM a prior tail mem entry out cut archive
    layout.board fits party i active full val small.1 small.2
  refine ⟨saved.trans read,head.trans ?_⟩
  change party.val+v.wideBallotParties z a*atom.val+1=_
  rw [Nat.mul_comm (v.wideBallotParties z a)];omega


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
