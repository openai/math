import OAI.Hierarchy.TaggedWireEarnedTreeMeasure
import OAI.Hierarchy.ProbeFixedWideBallotMenu
import OAI.Hierarchy.ProbeFixedBroadcastDate
import OAI.Hierarchy.ProbeFixedForestCheckout

namespace OAI
/-! # Selector bits on the original two dated broadcast pages -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram StockBound CatalystArchive StripDirectory CatalogueRows Strip
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
    (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "fm" => v.nativeFormats P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "stage" => v.stage P z width r banks src tab dst owners
local notation "st" => v.taskCommit P z width
local notation "H" => v.publicHeader P z width

/-- Exact charge of this public packet number in its own dated species. -/
def ballotSelectorBits : (a : Attempt)→Fin (v.ballotAtoms z a)→ℕ
  | .outer ..,i=>((v.payloadPacketMenu N).packet ((Fintype.equivFin _).symm i)).selectorBits
  | .inner ..,i=>(v.purchasePacketMenu.packet ((Fintype.equivFin _).symm i)).selectorBits

theorem ballot_selector_le (a : Attempt) (i : Fin (v.ballotAtoms z a)) :
    v.ballotSelectorBits z a i ≤ v.maxBits := by
  cases a with
  | outer phase trial =>
    let menu:=v.payloadPacketMenu N
    exact (Finset.le_sup (f:=fun j:menu.index=>(menu.packet j).selectorBits)
      (Finset.mem_univ ((Fintype.equivFin _).symm i))).trans (v.payload_selector_bits N (fixed_stage_count z v.W))
  | inner phase trial slice rep =>
    let menu:=v.purchasePacketMenu
    exact (Finset.le_sup (f:=fun j:menu.index=>(menu.packet j).selectorBits)
      (Finset.mem_univ ((Fintype.equivFin _).symm i))).trans v.purchased_selector_bits

def ballotTreeEdges : Attempt→ℕ
  | .outer ..=>PayloadStrip.edgeCount N
  | .inner ..=>ChainStrip.edgeCount v.depth

/-- Original primary operands of the selected broadcast tree. -/
def ballotTreePort : (a : Attempt)→TreeLink (v.ballotTreeEdges z a) k→Expr
  | .outer ..,l=>(v.payloadPricePorts P z width).primary P.catalogue (treeRole _ k l : PayloadRole N k)
  | .inner p t _ _,l=>(v.purchasedPricePorts P z width p t).primary P.catalogue
      (treeRole _ k l : PurchasedRole v.depth k)

section
variable {v P z width r banks src tab dst owners} {π : Equiv.Perm (Fin (2^z))}
    {mem fixture : Memory (wordBits z (2^v.W) copies)}
variable (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)
variable (a : Attempt) (prior tail : List Event) (entry out : Memory (wordBits z (2^v.W) copies))
    (cut : Slot (v.nativeChart P z width r banks src tab dst owners) mem (.attempt a) prior tail entry)
    (archive : ∀ x, x < (v.privateArena P z width).endAddress v.mesh →
      out x = checkedOut (v.nativeChart P z width r banks src tab dst owners)
        ((v.privateArena P z width).endAddress v.mesh) mem x)
local notation "ar" => (fm a).pricedArea
local notation "snap" => WireTelescope.HistogramShelf.snapshot C a entry

include D cut archive in
/-- The physical price word at any later prefix-preserving memory. Both
the commit predicate and packet ordinal come from the original repair snapshot. -/
theorem ReadbackRun.broadcast_word (late : v.stripHeight≤z) (i : Fin ((C).layout a).candidates) :
    out ((ar).broadcast+i.val)=
      if committed (b a) snap (i.val:Word W)
      then (st a).price.read (stage a entry) ((b a).packet.eval snap (i.val:Word W)) else 0 := by
  have live : Event.attempt a∈events v.mesh := by
    change Event.attempt a ∈ events (C).mesh
    rw [cut.events]
    simp
  have layout:=(D.boards a live).1
  have rates:=v.strip_scalar_room P z width late D.payload
  have copiesEq : (b a).copies=v.menu.copiesAt v.copyScale width := (v.ordinary_dimensions P z width a).2
  have bc:=fresh_broadcastRoom _ _ (b a) layout.inputs layout.window.room
  let pricedRow : Fin (ar).rows := ⟨i.val,i.isLt⟩
  have read := (st a).read_broadcast (b a) (stage a entry) pricedRow
    (v.entered P z width r banks src tab dst owners a entry cut.currentReady) bc.fits rates.termFit
    (by simpa only [copiesEq] using rates.copyFit) (by simpa only [copiesEq] using rates.sumFit) (bc.keeps pricedRow)
  have before:=v.ballot_before P z width r banks src tab dst owners a
  have room:=layout.window.wide
  have same:=priced_liveRows ((C).layout a) (repair C a) ar (fm a).stockSource
    (v.stamp P z width r banks src tab dst owners a) (prepared C a entry)
    cut.currentReady.2.2.2.2.2.2.1 cut.currentReady.2.2.2.2.2.2.2.1
    (by omega) before (before.trans (Nat.le_succ _)) layout.window.label
  have votes : committed (b a) (stage a entry) (i.val:Word W) ↔ committed (b a) snap (i.val:Word W) := by
    have membership : i ∈ StockCommit.liveRows (b a) (stage a entry) ((C).layout a).candidates ↔
        i ∈ StockCommit.liveRows (b a) snap ((C).layout a).candidates := Finset.ext_iff.mp same i
    simpa only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and] using membership
  have samePacket : (b a).packet.eval (stage a entry) (i.val:Word W) =
      (b a).packet.eval snap (i.val:Word W) :=
    v.wide_ballot_packet_at_stage P z width r banks src tab dst owners a entry layout cut.currentReady i
  have addr : (ar).broadcast+i.val<(ar).stop := by
    have h : i.val<(ar).rows:=i.isLt
    unfold Area.stop Area.output Area.excess Area.clip Area.src
    omega
  have slab:=addr.trans_le (v.attempt_room P z width a)
  rw [archive _ (slab.trans_le ((G).within v.mesh _ live)),
    v.paid_slab_cell P z width r banks src tab dst owners (.attempt a) mem entry prior tail cut _ slab]
  change ((((st a).native W (ar).rows (b a)).after (stage a entry)) ((st a).broadcast+i.val))=_
  by_cases active : committed (b a) snap (i.val:Word W)
  · simpa only [pricedRow,ite_eq_left active,ite_eq_left (votes.mpr active),samePacket] using read
  · simpa only [pricedRow,ite_eq_right active,ite_eq_right (fun yes => active (votes.mp yes))] using read

include D cut archive in
/-- A supplied authentic packet ordinal has its own exact selector charge,
including for a zero-copy receipt. -/
theorem ReadbackRun.broadcast_selected (late : v.stripHeight≤z) (bits : v.maxBits<2^W)
    (i : Fin ((C).layout a).candidates) (atom : Fin (v.ballotAtoms z a))
    (active : committed (b a) snap (i.val:Word W))
    (code : (b a).packet.eval snap (i.val:Word W)=((atom.val+1:ℕ):Word W)) :
    (out ((ar).broadcast+i.val)).val=v.ballotSelectorBits z a atom := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  rw [D.broadcast_word a prior tail entry out cut archive late i,ite_eq_left active,code]
  have pages:=v.paid_row_pages_at_slot P z width r banks src tab dst owners a prior tail mem entry cut
    D.resident _ D.prices D.charges
  have bound:=(v.ballot_selector_le z a atom).trans_lt bits
  cases a with
  | outer phase trial =>
    let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    let menu:=v.payloadPacketMenu N
    let j := (Fintype.equivFin menu.index).symm atom
    obtain ⟨table,resident⟩:=v.payload_charge_page P z width phase trial (stage (.outer phase trial) entry) pages.charges
    have fetch:=MenuROM.charge_lookup menu (H).stop _ resident j
    rw [show Fintype.equivFin menu.index j=atom from Equiv.apply_symm_apply ..] at fetch
    change (menu.packet j).selectorBits < 2^W at bound
    rw [table]
    exact (congrArg (fun word : Word W => word.val) fetch).trans (Fin.val_cast_of_lt bound)
  | inner phase trial slice rep =>
    let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    let menu:=v.purchasePacketMenu
    let j := (Fintype.equivFin menu.index).symm atom
    obtain ⟨table,resident⟩:=v.purchased_charge_page P z width phase trial slice rep
      (stage (.inner phase trial slice rep) entry) pages.charges
    have fetch:=MenuROM.charge_lookup menu _ _ resident j
    rw [show Fintype.equivFin menu.index j=atom from Equiv.apply_symm_apply ..] at fetch
    change (menu.packet j).selectorBits < 2^W at bound
    rw [table]
    exact (congrArg (fun word : Word W => word.val) fetch).trans (Fin.val_cast_of_lt bound)

include D cut archive in
theorem ReadbackRun.broadcast_idle (late : v.stripHeight≤z) (i : Fin ((C).layout a).candidates)
    (idle : ¬committed (b a) snap (i.val:Word W)) : (out ((ar).broadcast+i.val)).val=0 := by
  rw [D.broadcast_word a prior tail entry out cut archive late i,ite_eq_right idle];rfl

include D cut archive in
/-- The native tape produces the elected atom and its width together. -/
theorem ReadbackRun.broadcast_elected (bounds : RepairWordBounds v P z width) (bits : v.maxBits<2^W)
    (i : Fin ((C).layout a).candidates) (active : committed (b a) snap (i.val:Word W)) :
    ∃atom : Fin (v.ballotAtoms z a),
      (b a).packet.eval snap (i.val:Word W)=((atom.val+1:ℕ):Word W) ∧
      (out ((ar).broadcast+i.val)).val=v.ballotSelectorBits z a atom := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  obtain ⟨atom,code⟩:=D.ballot_menu bounds a prior tail entry cut i active
  exact ⟨atom,code,D.broadcast_selected a prior tail entry out cut archive bounds.late bits i atom active code⟩

local notation "kept" => fun i : Fin ((C).layout a).candidates => committed (b a) snap (i.val : Word W)
local notation "links" => TreeLink (v.ballotTreeEdges z a) k

include D cut archive in
/-- Exact native broadcast load on a permanent edge. Both branches consume
the elected atom used by the tender and the horizontal/radial operands of the
original strip. The numerical charge and the row enumerate the same receipt. -/
theorem ReadbackRun.forest_broadcast_load (late : v.stripHeight≤z) (bits : v.maxBits<2^W)
    (noWrap : (b a).copies*v.maxBits<2^W) (room : P.catalogue.rows<2^W)
    (pos : 0<P.catalogue.coreRows)
    (payloadRoom : Fintype.card (TreeLink (PayloadStrip.edgeCount N) k)≤2^W)
    (boughtRoom : Fintype.card (TreeLink (ChainStrip.edgeCount v.depth) k)≤2^W)
    (atom : Subtype kept→Fin (v.ballotAtoms z a))
    (code : ∀i : Subtype kept,(b a).packet.eval snap (i.val.val:Word W)=(((atom i).val+1:ℕ):Word W))
    (valid : ∀i : Subtype kept,∀l : links,
      ((v.ballotTreePort P z width a l).eval out (i.val.val:Word W)).val<P.catalogue.rows)
    (e : Fin P.catalogue.rows) :
    let t:=v.nativeTrees P z width a
    (PaidWidths.paidBroadcast ar t.positions t.owner t.parity t.edge t.sourceRow (b a).copies v.maxBits).load out e=
      ∑i : Subtype kept,∑l : links,if ((v.ballotTreePort P z width a l).eval out (i.val.val:Word W)).val=e.val
        then (b a).copies*v.ballotSelectorBits z a (atom i) else 0 := by
  intro t
  have occurs : Event.attempt a∈events v.mesh := by
    change Event.attempt a ∈ events (C).mesh
    rw [cut.events]
    simp
  have under : (H).stop ≤ (G).first :=
    (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have first : (G).first ≤ (G).endAddress v.mesh := Nat.le_add_right ..
  have pages:=v.row_pages_of_low P z width a mem out D.resident _ D.prices (fun x hx=>
    (archive x ((hx.trans_le under).trans_le first)).trans
      (v.paid_forest_checkout P z width r banks src tab dst owners _ mem D.nativeStock.mounted_all
        first x (hx.trans_le under)))
  let s:=v.located (v.seed P z width) P width
  have rows : (ar).rows = treeRows s v.mesh P.catalogue P.routes F a :=
    (candidate_count F v.mesh G P.joint.initial (v.nativeBoards P z width) a).trans (by cases a <;> rfl)
  have rowFits : (ar).rows ≤ 2^W := v.market_rows_fit P z width late a
  let reads (n : ℕ) := t.Reads out (fun i : Fin n => treeWalk s v.mesh P.catalogue P.routes a out i.val pos)
  have head : reads (ar).rows := (congrArg reads rows).mpr
    (v.native_forest_resident P z width out pages.header a occurs room pos
      (rows ▸ rowFits) payloadRoom boughtRoom)
  let activeRow : Fin (ar).rows → Prop := kept
  let selector (i : Subtype activeRow) := v.ballotSelectorBits z a (atom i)
  have priced (i : Subtype activeRow) : (out ((ar).broadcast+i.val.val)).val = selector i :=
    D.broadcast_selected a prior tail entry out cut archive late bits i.val (atom i) i.property (code i)
  have idle (i : Fin (ar).rows) (h : ¬activeRow i) : (out ((ar).broadcast+i.val)).val=0 :=
    D.broadcast_idle a prior tail entry out cut archive late i h
  have cap (i : Fin (ar).rows) : (out ((ar).broadcast+i.val)).val≤v.maxBits := by
    by_cases h : activeRow i
    · exact (priced ⟨i,h⟩).le.trans (v.ballot_selector_le z a _)
    · rw [idle i h];exact Nat.zero_le _
  have full (i : Fin (ar).rows) : (b a).copies*(out ((ar).broadcast+i.val)).val<2^W :=
    (Nat.mul_le_mul_left _ (cap i)).trans_lt noWrap
  have rate:=v.strip_scalar_room P z width late D.payload
  have cp : (b a).copies<2^W := (v.ordinary_dimensions P z width a).2.le.trans_lt rate.copyFit
  cases a with
  | outer phase trial =>
    exact measured_elected_tree_load (A:=PayloadStrip.Quotes N k) (v.payloadPricePorts P z width)
      P.catalogue _ t out pos _ v.maxBits e head bits cp room cap full activeRow selector priced idle valid
  | inner phase trial slice rep =>
    exact measured_elected_tree_load (A:=ChainStrip.Axes v.depth k) (v.purchasedPricePorts P z width phase trial)
      P.catalogue _ t out pos _ v.maxBits e head bits cp room cap full activeRow selector priced idle valid

end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
