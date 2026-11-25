import OAI.Hierarchy.ProbeFixedTapeQuotes

namespace OAI
/-! # The native selected row tape has degree one and its actual column rate -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive

open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing BigOperators

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H → ℝ} {cap : A → ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "req" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap
variable {e : Role C H (A⊕B) k → Chord sites}
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}


namespace StripInput
variable (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)
local notation "cmt" => fresh x.form.pricedArea x.form.stockSource
local notation "header" => (⟨x.start,x.raw.market.rows,D⟩ : PortHeader)
local notation "field" => fun a : A => PortPadding.inject x.ports (Fintype.equivFin Roles (.extra (.inl a)))
variable {paths : ℕ} (mount : ((fresh x.form.pricedArea x.form.stockSource).native w x.raw.market.rows x.ballot).ready x.mem)
  (bc : BroadcastRoom (fresh x.form.pricedArea x.form.stockSource) x.ballot x.raw.market.rows w) (keys : CashKeys (fresh x.form.pricedArea x.form.stockSource).occurrences x.raw.market.rows (fresh x.form.pricedArea x.form.stockSource).goods paths)
  (link : Fin (fresh x.form.pricedArea x.form.stockSource).occurrences → ℕ → ℝ) (pricesAt : Fin x.raw.market.rows → ℕ → ℝ)
local notation "tape" => (cmt).tape x.ballot x.mem x.plan mount bc keys link pricesAt

omit [Nonempty (Fin k)] in
theorem degree_one (placed : x.Placed) (i : Fin x.raw.coordinates) :
    (Finset.univ.filter (fun f => (tape).activeKind f=some i)).card ≤ 1 := by
  classical
  obtain ⟨place,read⟩ := placed
  apply Finset.card_le_one.mpr
  intro e eMember f fMember
  have he := (Finset.mem_filter.mp eMember).2
  have hf := (Finset.mem_filter.mp fMember).2
  have live (g) (hit : (tape).activeKind g=some i) :
      (tape).kind ((tape).use g)=some i ∧ 0<(tape).put ((tape).use g)+(tape).take ((tape).use g) := by
    unfold SelectedRows.Tape.activeKind at hit
    split at hit
    · contradiction
    · rename_i nz
      exact ⟨hit,Nat.pos_of_ne_zero nz⟩
  obtain ⟨ae,pe⟩ := live e he
  obtain ⟨af,pf⟩ := live f hf
  apply (tape).use.injective
  exact (header).moving_unique x.form.pricedArea.start x.raw.coordinates x.form.limit x.form.stockSource.old
    x.form.sources.reserve x.form.sources.half x.form.sources.price (Calendar.word x.form.board.modeOut)
    (PortPadding.extend x.slots none) x.ballot x.form.board.wire x.mem x.loaded x.portFit x.termFit
    x.copyFit x.sumFit x.bankFit (field) x.addr x.ordinary_operand place read ae af pe pf

omit [Nonempty (Fin k)] in
/-- The physical numeric rate of every occurrence used in the compact tape. The
same actual resident code supplying a row quote also determines its packet rate. -/
theorem rate_at_used (K width : ℕ)
    (ordinals : ∀ i,(menu.packet i).terms ≤ q ∧ (menu.packet i).terms < 2^w)
    (mass : ∀i,x.ballot.copies ≤ copied K (menu.packet i).width width)
    (chosen : ∀ j,j∈liveRows x.ballot x.mem x.raw.market.rows → ∃ i : menu.index,
      x.ballot.packet.eval x.mem (j.val:Word w)=(((Fintype.equivFin menu.index i).val+1:ℕ):Word w) ∧
      x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))=((menu.packet i).terms:Word w))
    (f : Σ j,Fin ((tape).ports (SelectedRows.row (tape).selected j))) :
    ∃ i : menu.index,K*((tape).put ((tape).use f)+(tape).take ((tape).use f)) ≤ width*packetRate (menu.packet i) := by
  obtain ⟨u,v⟩ := f
  let j := SelectedRows.row (tape).selected u
  have on : j∈liveRows x.ballot x.mem x.raw.market.rows := SelectedRows.row_mem _ u
  obtain ⟨i,raw⟩ := chosen j on
  obtain ⟨extra,hq⟩ := Nat.exists_eq_add_of_le (ordinals i).1
  subst q
  have hit := x.decoded_packet_words j i (ordinals i).2 raw
  let R := packetAt i extra x j on hit.2 hit.1
  exact ⟨i,R.rate K width (Nat.zero_lt_of_lt (menu.wide i)) (mass i) v⟩

end StripInput
end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
