import OAI.Hierarchy.ProbeFixedRoleQuotes
import OAI.Hierarchy.ProbeFixedStripFunds
import OAI.Hierarchy.ProbeNativePacketBuild

namespace OAI
/-! # Reading the quoted price of every role of the actual native packet -/

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
local notation "header" => (⟨x.start,x.raw.market.rows,D⟩ : PortHeader)
local notation "field" => fun r : Roles => PortPadding.inject x.ports (Fintype.equivFin Roles r)
local notation "padded" => PortPadding.extend x.slots none
local notation "old" => x.form.stockSource.old


omit [Nonempty (Fin k)] in
/-- The exact histogram tag on a named real role, including both the addressed
and the cash-only branches. -/
theorem role_kind (j : Fin x.raw.market.rows) (idx : A → Fin x.raw.coordinates)
    (read : ∀ a,((x.addr a).eval x.mem (j.val:Word w)).val=(idx a).val) (r : Roles) :
    let c := fresh x.form.pricedArea x.form.stockSource
    RepairHistogram.kind c.plan.bank c.columns x.mem (x.plan.enum ⟨j,(field) r⟩) = account idx r := by
  let c := fresh x.form.pricedArea x.form.stockSource
  let tag := RepairHistogram.kind (goods:=x.raw.coordinates) c.plan.bank c.columns x.mem
    (x.plan.enum ⟨j,(field) r⟩)
  have spec (i : Fin x.raw.coordinates) : tag=some i ↔ ∃ a,account id r=some a ∧ idx a=i := by
    have h := StripDirectory.fresh_kind_iff (header) x.form.pricedArea.start x.raw.coordinates x.form.limit old
      x.form.sources.reserve x.form.sources.half x.form.sources.price (Calendar.word x.form.board.modeOut)
      padded x.ballot x.form.board.wire x.mem x.loaded x.portFit x.bankFit j ((field) r) i
    change tag=some i ↔ ∃ y,PortPadding.extend x.slots none ((field) r)=some y ∧ _ at h
    rw [PortPadding.extend_real] at h
    change tag=some i ↔ ∃ y,((account (id : A → A) ((Fintype.equivFin Roles).symm (Fintype.equivFin Roles r))).map x.addr)=some y ∧ _ at h
    rw [Equiv.symm_apply_apply] at h
    rw [h]
    constructor
    · rintro ⟨y,slot,word⟩
      obtain ⟨a,ordinary,rfl⟩ := Option.map_eq_some_iff.mp slot
      exact ⟨a,ordinary,Fin.ext ((read a).symm.trans word)⟩
    · rintro ⟨a,ordinary,rfl⟩
      exact ⟨x.addr a,by rw [ordinary];rfl,read a⟩
  change tag=account idx r
  cases orig : account (id : A → A) r with
  | some a =>
    obtain ⟨b,atRole,coord⟩ := ordinary_of_some _ _ orig
    change b=a at coord
    subst b
    have present := (spec (idx a)).2 ⟨a,orig,rfl⟩
    exact present.trans (by simp [atRole,account])
  | none =>
    have hnone : tag=none := by
      cases htag : tag with
      | none => rfl
      | some i =>
        obtain ⟨a,h,_⟩ := (spec i).1 htag
        simp [orig] at h
    rw [hnone]
    cases r with
    | extra e => cases e <;> simp_all [account]
    | radius | cross | horizontal | catalyst => rfl

omit [Nonempty (Fin k)] in
@[simp] theorem nominal_code (j : Fin x.raw.market.rows) (i : menu.index)
    (code : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1) :
    x.nominal j=(menu.packet i).width := by
  simp [nominal,picked,code,menuIndex_code]

omit [Nonempty (Fin k)] in
/-- A public recommendation and alphabet word, as returned by
`MenuROM.selected_packet`, give the exact natural readbacks for the compiled row. -/
theorem decoded_packet_words (j : Fin x.raw.market.rows) (i : menu.index)
    (capacity : (menu.packet i).terms < 2^w)
    (read : x.ballot.packet.eval x.mem (j.val:Word w)=(((Fintype.equivFin menu.index i).val+1:ℕ):Word w) ∧
      x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))=((menu.packet i).terms:Word w)) :
    (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1 ∧
    (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms := by
  have room : (Fintype.equivFin menu.index i).val + 1 < 2^w :=
    (Nat.succ_lt_succ (Fintype.equivFin menu.index i).isLt).trans_le
      (by simpa only [Nat.add_comm 1] using x.codeFit)
  exact ⟨(congrArg Fin.val read.1).trans (Fin.val_cast_of_lt room),
    (congrArg Fin.val read.2).trans (Fin.val_cast_of_lt capacity)⟩

/-- Compile the packet chosen by its actual immutable code and alphabet word.
The selector histogram is recovered from the committed ballot. -/
def packetAt (i : menu.index) (extra : ℕ) (x : StripInput menu w z d ((menu.packet i).terms+extra) D)
    (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
    (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
    (code : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1) :
    NativePacketRow (menu.packet i) extra x.ballot x.plan j := by
  let t := StripDirectory.tested {x.board.test with live:=x.active,rows:=x.raw.market.rows,population:=2^z}
    x.board.price (Calendar.GlobalTests.offsets x.board.globalTests) x.form.stockSource.old
    (fun a => x.addr ((Fintype.equivFin A).symm a))
  have maxEntry : (PacketWidths.ofMenu menu).entries i ≤ x.board.maxWidth :=
    ((PacketWidths.ofMenu menu).maximum_ge i).trans x.maximum
  have cap (u : Fin (menu.packet i).terms) (r : Roles) : (menu.packet i).count u r ≤ x.board.maxWidth := by
    apply le_trans _ maxEntry
    exact (Finset.le_sup (f:=fun v : Fin (menu.packet i).terms×Roles => (menu.packet i).count v.1 v.2)
      (Finset.mem_univ (u,r))).trans (Nat.le_add_right _ _)
  exact StripDirectory.nativeRow (extra:=extra) menu i t x.board.terms x.board.menu x.form.board.repairBits
    x.board.selectors x.form.stockSource.old x.board.copies x.board.maxWidth x.slots x.ports x.mem j
    (fresh x.form.pricedArea x.form.stockSource) x.codeFit x.fieldFit x.wide
    (fun r => (StripDirectory.cap_debit menu i r).trans maxEntry) cap x.plan rfl live arity code

omit [Nonempty (Fin k)] in
@[simp] theorem packetAt_port (i : menu.index) (extra : ℕ) (x : StripInput menu w z d ((menu.packet i).terms+extra) D)
    (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
    (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
    (code : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1) (r : Roles) :
    (packetAt i extra x j live arity code).ports r = PortPadding.inject x.ports (Fintype.equivFin Roles r) := rfl

end StripInput
end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
